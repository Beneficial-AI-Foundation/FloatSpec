import FloatSpec.src.IEEE754.PrimFloat

/-! Regression checks for the source-facing Coq primitive-float contract. -/

open FaithfulPrimFloat

example : FaithfulPrimFloat.flatten_cmp_opt none = FNotComparable := rfl

example :
    FaithfulPrimFloat.flatten_cmp_opt (some Ordering.eq) = FEq := rfl

example :
    FaithfulPrimFloat.flatten_cmp_opt (some Ordering.lt) = FLt := rfl

example :
    FaithfulPrimFloat.flatten_cmp_opt (some Ordering.gt) = FGt := rfl

/-- The former three-way model incorrectly returned ordinary equality here. -/
example :
    FaithfulPrimFloat.compare FaithfulPrimFloat.nan FaithfulPrimFloat.zero =
      FNotComparable := rfl

/-- Coq's standalone class contains only `prec < emax`; it does not impose an
independent lower bound on `emax`. -/
example : Prec_lt_emax (-5) 0 := ⟨by omega⟩

/-- Binary-format proofs still recover the useful lower bound from the two
actual source premises. -/
example : (2 : Int) ≤ FaithfulPrimFloat.primEmax := by
  have hprec := FaithfulPrimFloat.Hprec.pos
  have hlt := FaithfulPrimFloat.Hmax.prec_lt_emax
  omega
