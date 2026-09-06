import FloatSpec.src.Core.Zaux

namespace FloatSpec.Test.ZauxSource

#check @FloatSpec.Core.Zaux.Zsame_sign_trans
#check @FloatSpec.Core.Zaux.Zsame_sign_trans_weak
#check @FloatSpec.Core.Zaux.Zsame_sign_imp
#check @FloatSpec.Core.Zaux.Zsame_sign_odiv

example : 0 ≤ (-3 : Int) * Int.tdiv (-3) 2 := by
  exact FloatSpec.Core.Zaux.Zsame_sign_odiv (-3) 2 (by omega)

end FloatSpec.Test.ZauxSource
