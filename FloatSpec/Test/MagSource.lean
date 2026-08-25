import FloatSpec.src.Core.Raux

namespace FloatSpec.Test.MagSource

open FloatSpec.Core.Raux

private def binaryRadix : FloatSpec.Core.Zaux.Radix :=
  ⟨2, by omega⟩

/-- Coq's observable magnitude projection at one is preserved. -/
example : (mag_with_spec binaryRadix (1 : Real)).mag_val = 1 := by
  norm_num [mag_with_spec, mag, binaryRadix]

/-- The source-facing result carries the dependent bounds rather than merely
returning the integer projection. -/
example :
    (2 : Real) ^ ((mag_with_spec binaryRadix (1 : Real)).mag_val - 1) ≤ |(1 : Real)| ∧
      |(1 : Real)| < (2 : Real) ^ (mag_with_spec binaryRadix (1 : Real)).mag_val := by
  exact (mag_with_spec binaryRadix (1 : Real)).mag_spec one_ne_zero

end FloatSpec.Test.MagSource
