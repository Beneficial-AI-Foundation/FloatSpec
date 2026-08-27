import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade

namespace FloatSpec.Test.RoundingModeSource

open FloatSpec.IEEE754.BinarySingleNaN.Source

/-- The source constructors are a lossless renaming of the integrated ones. -/
example : mode.mode_NE.toRoundingMode = RoundingMode.RNE := rfl
example : mode.mode_ZR.toRoundingMode = RoundingMode.RTZ := rfl
example : mode.mode_DN.toRoundingMode = RoundingMode.RTN := rfl
example : mode.mode_UP.toRoundingMode = RoundingMode.RTP := rfl
example : mode.mode_NA.toRoundingMode = RoundingMode.RNA := rfl

/-- Distinct source modes remain distinct after translation. -/
example : mode.mode_NE.toRoundingMode ≠ mode.mode_ZR.toRoundingMode := by
  simp [mode.toRoundingMode]

/-- The source and integrated interpretations are definitionally identical. -/
example (m : mode) :
    round_mode m = rnd_of_mode m.toRoundingMode := rfl

end FloatSpec.Test.RoundingModeSource
