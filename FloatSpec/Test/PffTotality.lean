import FloatSpec.src.Pff.Pff
import FloatSpec.src.Pff.SourceFacade

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

namespace FloatSpec.Test.PffSourceFacade

open FloatSpec.Pff

private def sourceBound : Source.Fbound :=
  { vNum := 1, dExp := 2, vNum_pos := by omega }

/-- The source-facing normalization has no independent representation radix.
Both Coq and Lean reduce this call to the record `(1, -2)`. -/
example :
    Source.Fnormalize 1 sourceBound 3 ({ Fnum := 1, Fexp := 0 } : Source.float) =
      ({ Fnum := 1, Fexp := -2 } : Source.float) := by
  rfl

/-- Its observable real value consequently uses radix one on both sides. -/
example :
    Source.FtoR 1
      (Source.Fnormalize 1 sourceBound 3
        ({ Fnum := 1, Fexp := 0 } : Source.float)) =
      (1 : Real) := by
  norm_num [Source.FtoR, Source.Fnormalize, Source.Fshift, Source.Fdigit,
    Source.digit, sourceBound]

/-- The two old invalid-radix counterexamples are retained at the exact source
interface, without manufacturing a `ValidRadix` instance. -/
example :
    Source.Fnormalize 0
      ({ vNum := 10, dExp := 0, vNum_pos := by omega } : Source.Fbound) 5
      ({ Fnum := 5, Fexp := 10 } : Source.float) =
      ({ Fnum := 0, Fexp := 8 } : Source.float) := by
  rfl

example :
    Source.Fulp
      ({ vNum := 3, dExp := 10, vNum_pos := by omega } : Source.Fbound) (-1) 6
      ({ Fnum := 3, Fexp := 0 } : Source.float) = (1 : Real) := by
  have hnormalize :
      Source.Fnormalize (-1)
        ({ vNum := 3, dExp := 10, vNum_pos := by omega } : Source.Fbound) 6
        ({ Fnum := 3, Fexp := 0 } : Source.float) =
        ({ Fnum := 3, Fexp := -4 } : Source.float) := by
    rfl
  rw [Source.Fulp, hnormalize]
  norm_num

end FloatSpec.Test.PffSourceFacade
