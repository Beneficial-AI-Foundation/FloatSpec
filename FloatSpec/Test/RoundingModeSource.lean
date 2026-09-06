import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade
import FloatSpec.src.Calc.Round
import FloatSpec.src.Prop.Round_odd

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

namespace FloatSpec.Test.CalcRoundSource

open FloatSpec.Calc.Round
open FloatSpec.Core.Generic_fmt

example :
    FloatSpec.Calc.Round.round 2 (FloatSpec.Core.FIX.FIX_exp 0)
      (Mode.ofRnd rnd_floor) (3 / 4 : ℝ) = 0 := by
  norm_num [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.Mode.ofRnd, FloatSpec.Core.Generic_fmt.roundR,
    FloatSpec.Core.Generic_fmt.scaled_mantissa,
    FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.FIX.FIX_exp,
    rnd_floor, FloatSpec.Core.Raux.Zfloor]

example :
    FloatSpec.Calc.Round.round 2 (FloatSpec.Core.FIX.FIX_exp 0)
      (Mode.ofRnd rnd_ceil) (3 / 4 : ℝ) = 1 := by
  norm_num [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.Mode.ofRnd, FloatSpec.Core.Generic_fmt.roundR,
    FloatSpec.Core.Generic_fmt.scaled_mantissa,
    FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.FIX.FIX_exp,
    rnd_ceil, FloatSpec.Core.Raux.Zceil]

example :
    FloatSpec.Calc.Round.round 2 (FloatSpec.Core.FIX.FIX_exp 0)
      (Mode.ofRnd FloatSpec.Core.Raux.Ztrunc) (-3 / 4 : ℝ) = 0 := by
  norm_num [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.Mode.ofRnd, FloatSpec.Core.Generic_fmt.roundR,
    FloatSpec.Core.Generic_fmt.scaled_mantissa,
    FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.FIX.FIX_exp,
    FloatSpec.Core.Raux.Ztrunc, FloatSpec.Core.Raux.Zceil]

example :
    FloatSpec.Calc.Round.round 2 (FloatSpec.Core.FIX.FIX_exp 0)
      (Mode.ofRnd (FloatSpec.Core.Generic_fmt.Znearest (fun _ => false))) (1 / 2 : ℝ) = 0 := by
  norm_num [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.Mode.ofRnd, FloatSpec.Core.Generic_fmt.roundR,
    FloatSpec.Core.Generic_fmt.scaled_mantissa,
    FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.FIX.FIX_exp,
    FloatSpec.Core.Generic_fmt.Znearest, FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil,
    FloatSpec.Core.Raux.Rcompare]

example :
    FloatSpec.Calc.Round.round 2 (FloatSpec.Core.FIX.FIX_exp 0)
      (Mode.ofRnd (FloatSpec.Core.Generic_fmt.Znearest (fun _ => true))) (1 / 2 : ℝ) = 1 := by
  norm_num [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.Mode.ofRnd, FloatSpec.Core.Generic_fmt.roundR,
    FloatSpec.Core.Generic_fmt.scaled_mantissa,
    FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.FIX.FIX_exp,
    FloatSpec.Core.Generic_fmt.Znearest, FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil,
    FloatSpec.Core.Raux.Rcompare]

end FloatSpec.Test.CalcRoundSource

namespace FloatSpec.Test.RoundOddSource

#check @mag_round_odd
#check @fexp_round_odd

example (beta : Int) [ValidRadix beta] (emin prec : Int)
    (heven : beta % 2 = 0) (hprec : 1 < prec) (x : ℝ)
    (hx : emin < FloatSpec.Core.Raux.mag beta x) :
    FloatSpec.Core.Raux.mag beta
        (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) Zrnd_odd x) =
      FloatSpec.Core.Raux.mag beta x :=
  mag_round_odd beta emin prec heven hprec x hx

end FloatSpec.Test.RoundOddSource
