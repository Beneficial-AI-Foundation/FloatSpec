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

end PrimitiveFloat

end FloatSpec.IEEE754.LeanFloat
