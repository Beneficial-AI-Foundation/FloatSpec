import FloatSpec.src.IEEE754.BitsSourceFacade

namespace FloatSpec.Test.BitsSourceFacade

private def fullFloatTag : full_float → Nat
  | .F754_zero _ => 0
  | .F754_infinity _ => 1
  | .F754_nan _ _ => 2
  | .F754_finite _ _ _ => 3

private def fullFloatSign : full_float → Bool
  | .F754_zero s | .F754_infinity s | .F754_nan s _ | .F754_finite s _ _ => s

private def fullFloatPayload : full_float → Nat
  | .F754_nan _ p => FloatSpec.Core.Zaux.positiveToNat p
  | _ => 0

private def fullFloatMantissa : full_float → Nat
  | .F754_finite _ p _ => FloatSpec.Core.Zaux.positiveToNat p
  | _ => 0

private def fullFloatExponent : full_float → Int
  | .F754_finite _ _ e => e
  | _ => 0

-- The source's signed-width behavior: a negative left shift is a right shift.
example : FloatSpec.IEEE754.Bits.Source.join_bits (-1) 1 false 0 3 = 1 := by decide

private theorem b32Hmax : (23 + 1 : Int) < FloatSpec.Core.Zaux.Zpower 2 (8 - 1) := by
  decide

private theorem b64Hmax : (52 + 1 : Int) < FloatSpec.Core.Zaux.Zpower 2 (11 - 1) := by
  decide

private def decode32 (x : Int) : full_float :=
  binaryFloatToFullFloat (FloatSpec.IEEE754.Bits.Source.binary_float_of_bits
    23 8 (by omega) (by omega) b32Hmax x)

private def decode64 (x : Int) : full_float :=
  binaryFloatToFullFloat (FloatSpec.IEEE754.Bits.Source.binary_float_of_bits
    52 11 (by omega) (by omega) b64Hmax x)

private theorem tinyHmax : (2 + 1 : Int) < FloatSpec.Core.Zaux.Zpower 2 (3 - 1) := by
  decide

private def decodeTiny (x : Int) : full_float :=
  binaryFloatToFullFloat (FloatSpec.IEEE754.Bits.Source.binary_float_of_bits
    2 3 (by omega) (by omega) tinyHmax x)

-- Concrete binary32 execution: negative zero, infinity, NaN payload,
-- least subnormal, and 1.0 (normal).
example : fullFloatTag (decode32 2147483648) = 0 ∧
    fullFloatSign (decode32 2147483648) = true := by decide
example : fullFloatTag (decode32 2139095040) = 1 := by decide
example : fullFloatTag (decode32 2139095041) = 2 ∧
    fullFloatPayload (decode32 2139095041) = 1 := by decide
example : fullFloatTag (decode32 1) = 3 ∧
    fullFloatMantissa (decode32 1) = 1 ∧
    fullFloatExponent (decode32 1) = -149 := by decide
example : fullFloatTag (decodeTiny 12) = 3 ∧
    fullFloatMantissa (decodeTiny 12) = 4 ∧
    fullFloatExponent (decodeTiny 12) = -2 := by decide

-- Concrete binary64 execution and the generic checked bit roundtrip.
example : fullFloatTag (decode64 0) = 0 := by decide
example : FloatSpec.IEEE754.Bits.Source.bits_of_binary_float 23 8
    (FloatSpec.IEEE754.Bits.Source.binary_float_of_bits
      23 8 (by omega) (by omega) b32Hmax 1065353216) =
      1065353216 :=
  FloatSpec.IEEE754.Bits.Source.bits_of_binary_float_of_bits
    23 8 (by omega) (by omega) b32Hmax
    1065353216 (by decide)
example : FloatSpec.IEEE754.Bits.Source.bits_of_binary_float 52 11
    (FloatSpec.IEEE754.Bits.Source.binary_float_of_bits
      52 11 (by omega) (by omega) b64Hmax 4607182418800017408) =
      4607182418800017408 :=
  FloatSpec.IEEE754.Bits.Source.bits_of_binary_float_of_bits
    52 11 (by omega) (by omega) b64Hmax
    4607182418800017408 (by decide)

end FloatSpec.Test.BitsSourceFacade
