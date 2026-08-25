import FloatSpec.src.Pff.Pff

/-!
Regression checks for the exported total behavior of the legacy Pff digit
counter.  The surrounding Coq section's `radixMoreThanOne` hypothesis is not
an argument of `digit`, `Fnormalize`, or `Fulp`, so invalid operational radices
remain part of their observable source interface.
-/

namespace FloatSpec.Test.PffTotality

example : pffDigit 0 5 = 3 := by
  rfl

example : pffDigit (-1) 3 = 2 := by
  rfl

/-- This was a two-sided judge counterexample before the total Pff digit
implementation was restored.  Coq evaluates the same input to `Float 0 8`. -/
theorem Fnormalize_radix_zero :
    Fnormalize (beta := 2) 0
      (⟨0, 10, by omega, by omega⟩ : Fbound_skel) 5
      (⟨5, 10⟩ : FloatSpec.Core.Defs.FlocqFloat 2) =
      (⟨0, 8⟩ : FloatSpec.Core.Defs.FlocqFloat 2) := by
  rfl

/-- This was the second two-sided judge counterexample.  Coq evaluates the
same `Fulp` input to `1`; the prior Core-digit substitution returned `-1`. -/
theorem Fulp_radix_neg_one :
    @Fulp 2 ⟨by omega⟩
      ({ dExp := 10, vNum := 3 } : Fbound_skel) (-1) 6
      ({ Fnum := 3, Fexp := 0 } : FloatSpec.Core.Defs.FlocqFloat 2) =
      (1 : ℝ) := by
  have hnormalize :
      @Fnormalize 2 ⟨by omega⟩ (-1)
        ({ dExp := 10, vNum := 3 } : Fbound_skel) 6
        ({ Fnum := 3, Fexp := 0 } : FloatSpec.Core.Defs.FlocqFloat 2) =
        ({ Fnum := 3, Fexp := -4 } : FloatSpec.Core.Defs.FlocqFloat 2) := by
    rfl
  rw [Fulp, hnormalize]
  norm_num

end FloatSpec.Test.PffTotality
