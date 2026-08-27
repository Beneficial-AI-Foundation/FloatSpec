import FloatSpec.src.Core.Raux

/-! Source-shaped entry points for declarations whose idiomatic FloatSpec
implementation separates a computational projection from its proof payload. -/

namespace FloatSpec.Core.Raux.Source

abbrev mag_prop := FloatSpec.Core.Raux.mag_prop

/-- Coq `Raux.mag`: return the dependent magnitude witness. -/
noncomputable def mag (r : FloatSpec.Core.Zaux.Radix) (x : Real) :
    mag_prop r.val x :=
  FloatSpec.Core.Raux.mag_with_spec r x

@[simp] theorem mag_val (r : FloatSpec.Core.Zaux.Radix) (x : Real) :
    (mag r x).mag_val = FloatSpec.Core.Raux.mag r.val x := by
  rfl

end FloatSpec.Core.Raux.Source
