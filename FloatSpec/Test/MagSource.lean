import FloatSpec.src.Core.RauxSourceFacade

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

/-! Focused source-contract regressions for `Core/Raux.v`. -/

#check @Rabs_gt
#check @Rcompare_sym
#check @Rcompare_opp
#check @Rcompare_plus_r
#check @Rcompare_plus_l
#check @Rcompare_mult_r
#check @Rcompare_mult_l
#check @negb_Rlt_bool
#check @negb_Rle_bool
#check @Zfloor_div
#check @Ztrunc_div
#check @FloatSpec.Core.Raux.Source.bpow
#check @IZR_Zpower_pos
#check @IZR_Zpower_nat
#check @IZR_Zpower
#check @FloatSpec.Core.Raux.Source.mag
#check @bpow_unique
#check @mag_unique_pos
#check @mag_le_abs
#check @mag_le
#check @lt_mag
#check @bpow_mag_gt
#check @bpow_mag_le
#check @mag_sqrt
#check @IZR_cond_Zopp

/-- Equality is the edge case that exposed the two swapped boolean lemmas. -/
example : Bool.not (Rle_bool (0 : Real) 0) = Rlt_bool 0 0 :=
  negb_Rlt_bool 0 0

example : Bool.not (Rlt_bool (0 : Real) 0) = Rle_bool 0 0 :=
  negb_Rle_bool 0 0

example : Rcompare (0 : Real) 0 = -(Rcompare 0 0) :=
  Rcompare_sym 0 0

/-- Coq floor division rounds toward negative infinity for a negative divisor. -/
example : Zfloor (((3 : Int) : Real) / (((-2 : Int) : Real))) = -2 := by
  calc
    Zfloor (((3 : Int) : Real) / (((-2 : Int) : Real)))
        = Int.fdiv 3 (-2) := Zfloor_div 3 (-2) (by norm_num)
    _ = -2 := by decide

/-- Coq truncating division rounds a negative dividend toward zero. -/
example : Ztrunc (((-3 : Int) : Real) / (((2 : Int) : Real))) = -1 := by
  calc
    Ztrunc (((-3 : Int) : Real) / (((2 : Int) : Real)))
        = Int.tdiv (-3) 2 := Ztrunc_div (-3) 2 (by norm_num)
    _ = -1 := by decide

/-- The same truncating convention applies with a negative divisor. -/
example : Ztrunc (((3 : Int) : Real) / (((-2 : Int) : Real))) = -1 := by
  calc
    Ztrunc (((3 : Int) : Real) / (((-2 : Int) : Real)))
        = Int.tdiv 3 (-2) := Ztrunc_div 3 (-2) (by norm_num)
    _ = -1 := by decide

end FloatSpec.Test.MagSource
