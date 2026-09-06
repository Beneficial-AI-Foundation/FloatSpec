import FloatSpec.src.Calc.Bracket

namespace FloatSpec.Test.BracketSource

open FloatSpec.Calc.Bracket

/-- Regression for the exported Coq definition, whose domain is not restricted
by the later section hypothesis `1 < nb_steps`. -/
example :
    new_location_odd 1 0 (Location.loc_Inexact Ordering.gt) =
      Location.loc_Inexact Ordering.lt := by
  simp [new_location_odd]

end FloatSpec.Test.BracketSource
