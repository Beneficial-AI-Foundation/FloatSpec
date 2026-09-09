import FloatSpec.src.Core.Zaux

namespace FloatSpec.Test.ZauxSource

#check @FloatSpec.Core.Zaux.Zsame_sign_trans
#check @FloatSpec.Core.Zaux.Zsame_sign_trans_weak
#check @FloatSpec.Core.Zaux.Zsame_sign_imp
#check @FloatSpec.Core.Zaux.Zsame_sign_odiv
#check @FloatSpec.Core.Zaux.Zmod_mod_mult
#check @FloatSpec.Core.Zaux.ZOmod_eq
#check @FloatSpec.Core.Zaux.ZOmod_mod_mult
#check @FloatSpec.Core.Zaux.Zdiv_mod_mult
#check @FloatSpec.Core.Zaux.ZOdiv_mod_mult
#check @FloatSpec.Core.Zaux.ZOdiv_small_abs
#check @FloatSpec.Core.Zaux.ZOmod_small_abs
#check @FloatSpec.Core.Zaux.ZOdiv_plus
#check @FloatSpec.Core.Zaux.Zeq_bool_opp
#check @FloatSpec.Core.Zaux.Zle_bool_opp
#check @FloatSpec.Core.Zaux.negb_Zle_bool
#check @FloatSpec.Core.Zaux.Zlt_bool_opp
#check @FloatSpec.Core.Zaux.negb_Zlt_bool
#check @FloatSpec.Core.Zaux.Zcompare_Lt
#check @FloatSpec.Core.Zaux.Zcompare_Eq
#check @FloatSpec.Core.Zaux.Zcompare_Gt
#check @FloatSpec.Core.Zaux.cond_Zopp_negb
#check @FloatSpec.Core.Zaux.abs_cond_Zopp
#check @FloatSpec.Core.Zaux.cond_Zopp_Zlt_bool
#check @FloatSpec.Core.Zaux.Zeq_bool_cond_Zopp
#check @FloatSpec.Core.Zaux.Zfast_pow_pos_correct
#check @FloatSpec.Core.Zaux.Zfast_div_eucl_correct
#check @FloatSpec.Core.Zaux.iter_nat_plus
#check @FloatSpec.Core.Zaux.iter_nat_S
#check @FloatSpec.Core.Zaux.iter_pos_nat

example : FloatSpec.Core.Zaux.Zfast_div_eucl 7 (-3) = (-3, -2) := by
  decide

example : FloatSpec.Core.Zaux.Zfast_div_eucl 7 0 = (0, 7) := by
  decide

example : 0 ≤ (-3 : Int) * Int.tdiv (-3) 2 := by
  exact FloatSpec.Core.Zaux.Zsame_sign_odiv (-3) 2 (by omega)

example : (Int.tmod (-17) (3 * 4)).tdiv 3 =
    (Int.tdiv (-17) 3).tmod 4 := by decide

example : Int.tdiv ((-7 : Int) + -5) 3 =
    Int.tdiv (-7) 3 + Int.tdiv (-5) 3 +
      Int.tdiv (Int.tmod (-7) 3 + Int.tmod (-5) 3) 3 := by decide

end FloatSpec.Test.ZauxSource
