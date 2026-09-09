import FloatSpec.src.IEEE754.PrimFloat

/-! Compatibility names for the native adapters now owned by the source modules. -/

namespace FloatSpec.IEEE754.LeanFloat

open Float.Model

abbrev unpackedOfStandardFloat :=
  FloatSpec.IEEE754.Native.unpackedOfStandardFloat

abbrev standardFloatOfUnpacked :=
  FloatSpec.IEEE754.Native.standardFloatOfUnpacked

theorem standardFloatOfUnpacked_unpackedOfStandardFloat
    (x : StandardFloat)
    (hvalid : match x with | .S754_finite _ m _ => 0 < m | _ => True) :
    standardFloatOfUnpacked (unpackedOfStandardFloat x) = x :=
  FloatSpec.IEEE754.Native.standardFloatOfUnpacked_unpackedOfStandardFloat x hvalid

@[simp] theorem unpackedOfStandardFloat_standardFloatOfUnpacked
    (x : UnpackedFloat) :
    unpackedOfStandardFloat (standardFloatOfUnpacked x) = x :=
  FloatSpec.IEEE754.Native.unpackedOfStandardFloat_standardFloatOfUnpacked x

abbrev model64OfStandardFloat :=
  FloatSpec.IEEE754.Native.model64OfStandardFloat

abbrev model32OfStandardFloat :=
  FloatSpec.IEEE754.Native.model32OfStandardFloat

abbrev standardFloatOfModel64 :=
  FloatSpec.IEEE754.Native.standardFloatOfModel64

abbrev standardFloatOfModel32 :=
  FloatSpec.IEEE754.Native.standardFloatOfModel32

abbrev model64OfBinarySingleNaNFloat :=
  FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat

abbrev model32OfBinarySingleNaNFloat :=
  FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat

theorem model64OfStandardFloat_binaryRoundAux
    (s : Bool) (m : Nat) (e : Int) (l : Loc) (hm : 0 < m) :
    model64OfStandardFloat
        (binary_round_aux (prec := 53) (emax := 1024) RoundingMode.RNE s m e l) =
      Float.Model.pack
        (UnpackedFloat.roundWithAccuracy Format.binary64
          (FloatSpec.IEEE754.Native.modelSignOfBool s) m e
          (FloatSpec.IEEE754.Native.accuracyOfLocation l)) :=
  FloatSpec.IEEE754.Native.model64OfStandardFloat_binaryRoundAux s m e l hm

theorem model32OfStandardFloat_binaryRoundAux
    (s : Bool) (m : Nat) (e : Int) (l : Loc) (hm : 0 < m) :
    model32OfStandardFloat
        (binary_round_aux (prec := 24) (emax := 128) RoundingMode.RNE s m e l) =
      Float32.Model.pack
        (UnpackedFloat.roundWithAccuracy Format.binary32
          (FloatSpec.IEEE754.Native.modelSignOfBool s) m e
          (FloatSpec.IEEE754.Native.accuracyOfLocation l)) :=
  FloatSpec.IEEE754.Native.model32OfStandardFloat_binaryRoundAux s m e l hm

private theorem unpack_model64OfBinarySingleNaNFloat
    (x : BinarySingleNaNFloat 53 1024) :
    (model64OfBinarySingleNaNFloat x).unpack =
      FloatSpec.IEEE754.Native.unpackedOfBinarySingleNaNFloat x := by
  have h := congrArg FloatSpec.IEEE754.Native.unpackedOfStandardFloat
    (FloatSpec.IEEE754.Native.standardFloatOfModel64_model64OfStandardFloat
      (binarySingleNaNFloatToStandardFloat x)
      (validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat x))
  simpa [FloatSpec.IEEE754.Native.standardFloatOfModel64,
    FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_eq_model64OfStandardFloat,
    FloatSpec.IEEE754.Native.unpackedOfStandardFloat_binarySingleNaNFloatToStandardFloat]
    using h

private theorem unpack_model32OfBinarySingleNaNFloat
    (x : BinarySingleNaNFloat 24 128) :
    (model32OfBinarySingleNaNFloat x).unpack =
      FloatSpec.IEEE754.Native.unpackedOfBinarySingleNaNFloat x := by
  have h := congrArg FloatSpec.IEEE754.Native.unpackedOfStandardFloat
    (FloatSpec.IEEE754.Native.standardFloatOfModel32_model32OfStandardFloat
      (binarySingleNaNFloatToStandardFloat x)
      (validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat x))
  simpa [FloatSpec.IEEE754.Native.standardFloatOfModel32,
    FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat_eq_model32OfStandardFloat,
    FloatSpec.IEEE754.Native.unpackedOfStandardFloat_binarySingleNaNFloatToStandardFloat]
    using h

theorem model64OfBinarySingleNaNFloat_Bmult_RNE
    (x y : BinarySingleNaNFloat 53 1024) :
    model64OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bmult 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x y) =
      Float.Model.mul (model64OfBinarySingleNaNFloat x)
        (model64OfBinarySingleNaNFloat y) := by
  change FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat
      (@BinarySingleNaN.Bmult 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
        RoundingMode.RNE x y) = _
  rw [FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_Bmult_RNE]
  unfold Float.Model.mul
  rw [unpack_model64OfBinarySingleNaNFloat, unpack_model64OfBinarySingleNaNFloat]

theorem model32OfBinarySingleNaNFloat_Bmult_RNE
    (x y : BinarySingleNaNFloat 24 128) :
    model32OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bmult 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x y) =
      Float32.Model.mul (model32OfBinarySingleNaNFloat x)
        (model32OfBinarySingleNaNFloat y) := by
  change FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat
      (@BinarySingleNaN.Bmult 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
        RoundingMode.RNE x y) = _
  rw [FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat_Bmult_RNE]
  unfold Float32.Model.mul
  rw [unpack_model32OfBinarySingleNaNFloat, unpack_model32OfBinarySingleNaNFloat]

theorem model64OfBinarySingleNaNFloat_Bplus_RNE
    (x y : BinarySingleNaNFloat 53 1024) :
    model64OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bplus 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x y) =
      Float.Model.add (model64OfBinarySingleNaNFloat x)
        (model64OfBinarySingleNaNFloat y) := by
  change FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat
      (@BinarySingleNaN.Bplus 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
        RoundingMode.RNE x y) = _
  rw [FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_Bplus_RNE]
  unfold Float.Model.add
  rw [unpack_model64OfBinarySingleNaNFloat, unpack_model64OfBinarySingleNaNFloat]

theorem model32OfBinarySingleNaNFloat_Bplus_RNE
    (x y : BinarySingleNaNFloat 24 128) :
    model32OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bplus 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x y) =
      Float32.Model.add (model32OfBinarySingleNaNFloat x)
        (model32OfBinarySingleNaNFloat y) := by
  change FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat
      (@BinarySingleNaN.Bplus 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
        RoundingMode.RNE x y) = _
  rw [FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat_Bplus_RNE]
  unfold Float32.Model.add
  rw [unpack_model32OfBinarySingleNaNFloat, unpack_model32OfBinarySingleNaNFloat]

theorem model64OfBinarySingleNaNFloat_Bminus_RNE
    (x y : BinarySingleNaNFloat 53 1024) :
    model64OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bminus 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x y) =
      Float.Model.sub (model64OfBinarySingleNaNFloat x)
        (model64OfBinarySingleNaNFloat y) := by
  change FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat
      (@BinarySingleNaN.Bminus 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
        RoundingMode.RNE x y) = _
  rw [FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_Bminus_RNE]
  unfold Float.Model.sub
  rw [unpack_model64OfBinarySingleNaNFloat, unpack_model64OfBinarySingleNaNFloat]

theorem model32OfBinarySingleNaNFloat_Bminus_RNE
    (x y : BinarySingleNaNFloat 24 128) :
    model32OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bminus 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x y) =
      Float32.Model.sub (model32OfBinarySingleNaNFloat x)
        (model32OfBinarySingleNaNFloat y) := by
  change FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat
      (@BinarySingleNaN.Bminus 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
        RoundingMode.RNE x y) = _
  rw [FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat_Bminus_RNE]
  unfold Float32.Model.sub
  rw [unpack_model32OfBinarySingleNaNFloat, unpack_model32OfBinarySingleNaNFloat]

theorem validStandardFloatOfModel64 (x : Float.Model) :
    validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024)
      (standardFloatOfModel64 x) = true :=
  FloatSpec.IEEE754.Native.validStandardFloatOfModel64 x

theorem validStandardFloatOfModel32 (x : Float32.Model) :
    validBinarySingleNaNStandardFloat (prec := 24) (emax := 128)
      (standardFloatOfModel32 x) = true :=
  FloatSpec.IEEE754.Native.validStandardFloatOfModel32 x

@[simp] theorem standardFloatOfModel64_model64OfStandardFloat
    (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024) x = true) :
    standardFloatOfModel64 (model64OfStandardFloat x) = x :=
  FloatSpec.IEEE754.Native.standardFloatOfModel64_model64OfStandardFloat x hx

@[simp] theorem standardFloatOfModel32_model32OfStandardFloat
    (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 24) (emax := 128) x = true) :
    standardFloatOfModel32 (model32OfStandardFloat x) = x :=
  FloatSpec.IEEE754.Native.standardFloatOfModel32_model32OfStandardFloat x hx

theorem model64OfStandardFloat_SFopp (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024) x = true) :
    model64OfStandardFloat (FaithfulPrimFloat.SFopp x) =
      Float.Model.neg (model64OfStandardFloat x) :=
  FloatSpec.IEEE754.Native.model64OfStandardFloat_SFopp x hx

theorem model32OfStandardFloat_SFopp (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 24) (emax := 128) x = true) :
    model32OfStandardFloat (FaithfulPrimFloat.SFopp x) =
      Float32.Model.neg (model32OfStandardFloat x) :=
  FloatSpec.IEEE754.Native.model32OfStandardFloat_SFopp x hx

theorem model64OfStandardFloat_SFabs (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024) x = true) :
    model64OfStandardFloat (FaithfulPrimFloat.SFabs x) =
      Float.Model.abs (model64OfStandardFloat x) :=
  FloatSpec.IEEE754.Native.model64OfStandardFloat_SFabs x hx

theorem model32OfStandardFloat_SFabs (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 24) (emax := 128) x = true) :
    model32OfStandardFloat (FaithfulPrimFloat.SFabs x) =
      Float32.Model.abs (model32OfStandardFloat x) :=
  FloatSpec.IEEE754.Native.model32OfStandardFloat_SFabs x hx

namespace PrimitiveFloat

abbrev toModel := FaithfulPrimFloat.PrimitiveFloat.toModel
abbrev toFloat := FaithfulPrimFloat.PrimitiveFloat.toFloat
abbrev ofModel := FaithfulPrimFloat.PrimitiveFloat.ofModel
abbrev ofFloat := FaithfulPrimFloat.PrimitiveFloat.ofFloat

@[simp] theorem toModel_ofModel (x : Float.Model) :
    toModel (ofModel x) = x :=
  FaithfulPrimFloat.PrimitiveFloat.toModel_ofModel x

@[simp] theorem ofModel_toModel (x : FaithfulPrimFloat.PrimitiveFloat) :
    ofModel (toModel x) = x :=
  FaithfulPrimFloat.PrimitiveFloat.ofModel_toModel x

@[simp] theorem toModel_neg (x : FaithfulPrimFloat.PrimitiveFloat) :
    toModel (-x) = Float.Model.neg (toModel x) :=
  FaithfulPrimFloat.PrimitiveFloat.toModel_neg x

@[simp] theorem toModel_abs (x : FaithfulPrimFloat.PrimitiveFloat) :
    toModel (FaithfulPrimFloat.abs x) = Float.Model.abs (toModel x) :=
  FaithfulPrimFloat.PrimitiveFloat.toModel_abs x

end PrimitiveFloat

end FloatSpec.IEEE754.LeanFloat
