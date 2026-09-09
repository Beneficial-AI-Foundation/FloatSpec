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

example (x : FaithfulPrimFloat.PrimitiveFloat) :
    PrimitiveFloat.toModel (-x) = Float.Model.neg (PrimitiveFloat.toModel x) := by simp

example (x : FaithfulPrimFloat.PrimitiveFloat) :
    PrimitiveFloat.toModel (FaithfulPrimFloat.abs x) =
      Float.Model.abs (PrimitiveFloat.toModel x) := by simp

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

example (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 24) (emax := 128) x = true) :
    model32OfStandardFloat (FaithfulPrimFloat.SFopp x) =
      Float32.Model.neg (model32OfStandardFloat x) :=
  model32OfStandardFloat_SFopp x hx

example (s : Bool) (m : Nat) (e : Int) (l : Loc) (hm : 0 < m) :
    model64OfStandardFloat
        (binary_round_aux (prec := 53) (emax := 1024) RoundingMode.RNE s m e l) =
      Float.Model.pack
        (Float.Model.UnpackedFloat.roundWithAccuracy Float.Model.Format.binary64
          (FloatSpec.IEEE754.Native.modelSignOfBool s) m e
          (FloatSpec.IEEE754.Native.accuracyOfLocation l)) :=
  model64OfStandardFloat_binaryRoundAux s m e l hm

example (s : Bool) (m : Nat) (e : Int) (l : Loc) (hm : 0 < m) :
    model32OfStandardFloat
        (binary_round_aux (prec := 24) (emax := 128) RoundingMode.RNE s m e l) =
      Float32.Model.pack
        (Float.Model.UnpackedFloat.roundWithAccuracy Float.Model.Format.binary32
          (FloatSpec.IEEE754.Native.modelSignOfBool s) m e
          (FloatSpec.IEEE754.Native.accuracyOfLocation l)) :=
  model32OfStandardFloat_binaryRoundAux s m e l hm

example (x y : BinarySingleNaNFloat 53 1024) :
    model64OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bmult 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x y) =
      Float.Model.mul (model64OfBinarySingleNaNFloat x)
        (model64OfBinarySingleNaNFloat y) :=
  model64OfBinarySingleNaNFloat_Bmult_RNE x y

example (x y : BinarySingleNaNFloat 24 128) :
    model32OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bmult 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x y) =
      Float32.Model.mul (model32OfBinarySingleNaNFloat x)
        (model32OfBinarySingleNaNFloat y) :=
  model32OfBinarySingleNaNFloat_Bmult_RNE x y
