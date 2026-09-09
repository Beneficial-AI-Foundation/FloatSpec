-- Bridges between FloatSpec's FLoCq-shaped carriers and Lean's native float model.

import Init.Data.Float
import FloatSpec.src.IEEE754.PrimFloat

namespace FloatSpec.IEEE754.LeanFloat

open Float.Model

private def signToModel : Bool → UnpackedFloat.Sign
  | false => .positive
  | true => .negative

private def signOfModel : UnpackedFloat.Sign → Bool
  | .positive => false
  | .negative => true

@[simp] private theorem signOfModel_signToModel (s : Bool) :
    signOfModel (signToModel s) = s := by cases s <;> rfl

@[simp] private theorem signToModel_signOfModel (s : UnpackedFloat.Sign) :
    signToModel (signOfModel s) = s := by cases s <;> rfl

/-- Structural translation from FLoCq's single-NaN surface to Lean's unpacked model. -/
def unpackedOfStandardFloat : StandardFloat → UnpackedFloat
  | .S754_zero s => .zero (signToModel s)
  | .S754_infinity s => .infinity (signToModel s)
  | .S754_nan => .notANumber
  | .S754_finite s m e =>
      if hm : 0 < m then .finite (signToModel s) m e hm else .zero (signToModel s)

/-- Structural translation from Lean's unpacked model to FLoCq's single-NaN surface. -/
def standardFloatOfUnpacked : UnpackedFloat → StandardFloat
  | .zero s => .S754_zero (signOfModel s)
  | .infinity s => .S754_infinity (signOfModel s)
  | .notANumber => .S754_nan
  | .finite s m e _ => .S754_finite (signOfModel s) m e

theorem standardFloatOfUnpacked_unpackedOfStandardFloat
    (x : StandardFloat)
    (hvalid : match x with | .S754_finite _ m _ => 0 < m | _ => True) :
    standardFloatOfUnpacked (unpackedOfStandardFloat x) = x := by
  cases x with
  | S754_zero s => cases s <;> rfl
  | S754_infinity s => cases s <;> rfl
  | S754_nan => rfl
  | S754_finite s m e =>
      cases s <;> simp_all [unpackedOfStandardFloat, standardFloatOfUnpacked]

@[simp] theorem unpackedOfStandardFloat_standardFloatOfUnpacked
    (x : UnpackedFloat) :
    unpackedOfStandardFloat (standardFloatOfUnpacked x) = x := by
  cases x with
  | infinity s => cases s <;> rfl
  | zero s => cases s <;> rfl
  | notANumber => rfl
  | finite s m e hm =>
      cases s <;> simp [unpackedOfStandardFloat, standardFloatOfUnpacked, hm]

/-- Encode a FLoCq standard float in Lean's binary64 logical model. -/
def model64OfStandardFloat (x : StandardFloat) : Float.Model :=
  Float.Model.pack (unpackedOfStandardFloat x)

/-- Encode a FLoCq standard float in Lean's binary32 logical model. -/
def model32OfStandardFloat (x : StandardFloat) : Float32.Model :=
  Float32.Model.pack (unpackedOfStandardFloat x)

/-- Decode Lean's binary64 logical model to the FLoCq single-NaN surface. -/
def standardFloatOfModel64 (x : Float.Model) : StandardFloat :=
  standardFloatOfUnpacked x.unpack

/-- Decode Lean's binary32 logical model to the FLoCq single-NaN surface. -/
def standardFloatOfModel32 (x : Float32.Model) : StandardFloat :=
  standardFloatOfUnpacked x.unpack

namespace PrimitiveFloat

open FaithfulPrimFloat

/-- The binary64 logical model of a proof-carrying FLoCq primitive float. -/
def toModel (x : PrimitiveFloat) : Float.Model :=
  model64OfStandardFloat (Prim2SF x)

/-- The native Lean float represented by a proof-carrying FLoCq primitive float. -/
def toFloat (x : PrimitiveFloat) : Float :=
  Float.ofModel (toModel x)

/-- Decode a Lean binary64 model, rejecting no valid model value. -/
def ofModel (x : Float.Model) : PrimitiveFloat :=
  SF2Prim (standardFloatOfModel64 x)

/-- Decode a native Lean float through its logical model. -/
def ofFloat (x : Float) : PrimitiveFloat :=
  ofModel x.toModel

end PrimitiveFloat

end FloatSpec.IEEE754.LeanFloat
