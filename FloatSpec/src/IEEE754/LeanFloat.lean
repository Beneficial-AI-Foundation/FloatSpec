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

namespace PrimitiveFloat

abbrev toModel := FaithfulPrimFloat.PrimitiveFloat.toModel
abbrev toFloat := FaithfulPrimFloat.PrimitiveFloat.toFloat
abbrev ofModel := FaithfulPrimFloat.PrimitiveFloat.ofModel
abbrev ofFloat := FaithfulPrimFloat.PrimitiveFloat.ofFloat

end PrimitiveFloat

end FloatSpec.IEEE754.LeanFloat
