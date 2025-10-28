-- Compatibility layer to bridge Core defs to simpler signatures

import FloatSpec.src.Core
import FloatSpec.src.Core.FLX
import FloatSpec.src.Core.FLT
import FloatSpec.src.Core.Generic_fmt
import FloatSpec.src.Core.Ulp
import FloatSpec.src.Calc.Round
import Mathlib.Data.Real.Basic

open FloatSpec.Core
open FloatSpec.Core.Defs
open FloatSpec.Core.Generic_fmt

/-- Bridge: Float to real as a plain ℝ (unwraps Id) -/
noncomputable def F2R {beta : Int} (f : FlocqFloat beta) : ℝ :=
  (FloatSpec.Core.Defs.F2R f).run

/-- Bridge: `generic_format` as a plain Prop (unwraps Id) -/
noncomputable def generic_format (beta : Int) (fexp : Int → Int) (x : ℝ) : Prop :=
  (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run

/-- Bridge: magnitude function in root namespace -/
noncomputable def mag (beta : Int) (x : ℝ) : Int :=
  FloatSpec.Core.Raux.mag beta x

/-- Bridge: integer truncation toward zero -/
noncomputable def Ztrunc (x : ℝ) : Int :=
  (FloatSpec.Core.Raux.Ztrunc x).run

/-- Bridge: ulp as a plain ℝ (unwraps Id) -/
noncomputable def ulp (beta : Int) (fexp : Int → Int) (x : ℝ) : ℝ :=
  (FloatSpec.Core.Ulp.ulp beta fexp x).run

/-- Bridge: canonical exponent as plain Int -/
noncomputable def cexp (beta : Int) (fexp : Int → Int) (x : ℝ) : Int :=
  (FloatSpec.Core.Generic_fmt.cexp beta fexp x).run

/-- Bridge: FLX exponent function in root namespace -/
def FLX_exp (prec : Int) : Int → Int :=
  FloatSpec.Core.FLX.FLX_exp prec

/-- Bridge: FLT exponent function in root namespace -/
def FLT_exp (emin prec : Int) : Int → Int :=
  FloatSpec.Core.FLT.FLT_exp prec emin

/-
Typeclass bridge instances

Several files refer to the exponent functions through these Compat aliases
(`FLX_exp` and `FLT_exp`). The canonical `Valid_exp` instances are declared on
the Core versions (`FloatSpec.Core.FLX.FLX_exp` and
`FloatSpec.Core.FLT.FLT_exp`). While these functions are definitionally equal,
typeclass search may not unfold through aliases. We therefore provide explicit
bridge instances so users of the Compat layer can synthesize
`[Valid_exp beta (FLX_exp prec)]` and `[Valid_exp beta (FLT_exp emin prec)]`
without further hints.
-/

instance instValidExp_FLX_Compat (beta prec : Int) [Prec_gt_0 prec] :
    FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec) := by
  -- Use the Core instance after providing the `Fact (0 < prec)` bridge.
  haveI : Fact (0 < prec) := ⟨(Prec_gt_0.pos : 0 < prec)⟩
  -- Now `inferInstance` finds the Core `Valid_exp` for `FloatSpec.Core.FLX.FLX_exp`.
  -- Rewrite the target via the alias so the types match.
  simpa [FLX_exp] using
    (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FloatSpec.Core.FLX.FLX_exp prec))

instance instValidExp_FLT_Compat (beta emin prec : Int) [Prec_gt_0 prec] :
    FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec) := by
  -- The Core instance already requires `[Prec_gt_0 prec]`.
  -- We just rewrite through the alias.
  simpa [FLT_exp] using
    (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FloatSpec.Core.FLT.FLT_exp prec emin))

/-- Stub: rounding function parameter validity (placeholder) -/
class Valid_rnd (rnd : ℝ → Int) : Prop :=
  (trivial : True := True.intro)

/-- Stub: exponent monotonicity predicate (placeholder) -/
class Monotone_exp (fexp : Int → Int) : Prop :=
  (trivial : True := True.intro)

/-- Stub: precision and range constraints for IEEE 754 (placeholders) -/
/-
Coq: `Prec_gt_0 prec` asserts strictly positive precision.
We model it as `0 < prec` so arithmetic lemmas may use it.
-/
class Prec_lt_emax (prec emax : Int) : Prop :=
  (trivial : True := True.intro)

/-- Stub: exponent function not flushing to zero (placeholder) -/
class Exp_not_FTZ (fexp : Int → Int) : Prop :=
  (trivial : True := True.intro)

/-- Stub: Flocq addition on floats (placeholder) -/
def Fplus {beta : Int} (x y : FlocqFloat beta) : FlocqFloat beta := x

/-- Stub: Flocq multiplication on floats (placeholder) -/
def Fmult {beta : Int} (x y : FlocqFloat beta) : FlocqFloat beta := x

/-- Stub: Flocq absolute on floats (placeholder) -/
def Fabs {beta : Int} (x : FlocqFloat beta) : FlocqFloat beta := x

/-- Stub: Flocq opposite on floats (placeholder) -/
def Fopp {beta : Int} (x : FlocqFloat beta) : FlocqFloat beta := x

/-- Stub: Flocq rounding to a float value (placeholder) -/
noncomputable def round_float (beta : Int) (fexp : Int → Int) (rnd : ℝ → Int) (x : ℝ) : FlocqFloat beta :=
  FlocqFloat.mk 0 0

/-- Helper: a trivial nearest-ties mode to satisfy signatures that use it -/
def Znearest (_choice : Int → Bool) : FloatSpec.Calc.Round.Mode := ()
