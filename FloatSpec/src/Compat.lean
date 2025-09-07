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

/-- Bridge: generic_format as a plain Prop (unwraps Id) -/
noncomputable def generic_format (beta : Int) (fexp : Int → Int) (x : ℝ) : Prop :=
  (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run

/-- Bridge: magnitude function in root namespace -/
noncomputable def mag (beta : Int) (x : ℝ) : Int :=
  FloatSpec.Core.Generic_fmt.mag beta x

/-- Bridge: integer truncation toward zero -/
noncomputable def Ztrunc (x : ℝ) : Int :=
  FloatSpec.Core.Generic_fmt.Ztrunc x

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

/-- Stub: rounding function parameter validity (placeholder) -/
class Valid_rnd (rnd : ℝ → Int) : Prop :=
  (trivial : True := True.intro)

/-- Stub: exponent monotonicity predicate (placeholder) -/
class Monotone_exp (fexp : Int → Int) : Prop :=
  (trivial : True := True.intro)

/-- Stub: precision and range constraints for IEEE 754 (placeholders) -/
class Prec_gt_0 (prec : Int) : Prop :=
  (trivial : True := True.intro)

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
