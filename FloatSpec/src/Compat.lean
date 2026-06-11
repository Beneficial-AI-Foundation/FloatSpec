/-
Scaffold compatibility layer to bridge translated files to simpler signatures.
Trusted aggregate imports do not depend on this module.
-/

import FloatSpec.src.Core
import FloatSpec.src.Core.FLX
import FloatSpec.src.Core.FLT
import FloatSpec.src.Core.Generic_fmt
import FloatSpec.src.Core.Ulp
import FloatSpec.src.Calc.Operations
import FloatSpec.src.Calc.Round
import FloatSpec.src.Calc.Operations
import Mathlib.Data.Real.Basic

open FloatSpec.Core
open FloatSpec.Core.Defs
open FloatSpec.Core.Generic_fmt

export FloatSpec.Core.Generic_fmt (Valid_rnd Monotone_exp)
export FloatSpec.Core.Ulp (Exp_not_FTZ)

/-- Bridge the duplicated monotonicity classes in `Generic_fmt` and `Ulp`.
This keeps downstream files from having to pick one local definition too early. -/
instance instUlpMonotoneOfGenericMonotone (fexp : Int → Int)
    [FloatSpec.Core.Generic_fmt.Monotone_exp fexp] :
    FloatSpec.Core.Ulp.Monotone_exp fexp where
  mono := FloatSpec.Core.Generic_fmt.Monotone_exp.mono

/-- Bridge the duplicated monotonicity classes in `Ulp` and `Generic_fmt`. -/
instance instGenericMonotoneOfUlpMonotone (fexp : Int → Int)
    [FloatSpec.Core.Ulp.Monotone_exp fexp] :
    FloatSpec.Core.Generic_fmt.Monotone_exp fexp where
  mono := FloatSpec.Core.Ulp.Monotone_exp.mono

/-- Bridge: Float to real as a plain ℝ (unwraps Id) -/
noncomputable def F2R {beta : Int} (f : FlocqFloat beta) : ℝ :=
  (FloatSpec.Core.Defs.F2R f)

/-- Bridge: {name (full := FloatSpec.Core.Generic_fmt.generic_format)}`generic_format` as a plain Prop (unwraps Id) -/
noncomputable def generic_format (beta : Int) (fexp : Int → Int) (x : ℝ) : Prop :=
  FloatSpec.Core.Generic_fmt.generic_format beta fexp x

/-- Bridge: magnitude function in root namespace -/
noncomputable def mag (beta : Int) (x : ℝ) : Int :=
  (FloatSpec.Core.Raux.mag beta x)

/-- Bridge: integer truncation toward zero -/
noncomputable def Ztrunc (x : ℝ) : Int :=
  (FloatSpec.Core.Raux.Ztrunc x)

/-- Fixed-exponent function: always returns the provided exponent. -/
def FIX_exp (emin : Int) : Int → Int := fun _ => emin

/-- Bridge: ulp as a plain ℝ (unwraps Id) -/
noncomputable def ulp (beta : Int) (fexp : Int → Int) (x : ℝ) : ℝ :=
  (FloatSpec.Core.Ulp.ulp beta fexp x)

/-- Bridge: canonical exponent as plain Int -/
noncomputable def cexp (beta : Int) (fexp : Int → Int) (x : ℝ) : Int :=
  FloatSpec.Core.Generic_fmt.cexp beta fexp x

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

-- Bridge instances for FLX/FLT exponent functions via the Core instances

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

-- Namespace aliases so existing references like `FloatSpec.Compat.Ztrunc` work.
namespace FloatSpec.Compat
/-- Namespace alias for {name}`Ztrunc`. -/
noncomputable def Ztrunc := _root_.Ztrunc
/-- Namespace alias for {name}`FIX_exp`. -/
def FIX_exp := _root_.FIX_exp
end FloatSpec.Compat

/-- Compatibility name for the core integer-rounding validity predicate. -/
abbrev Valid_rnd (rnd : ℝ → Int) : Prop :=
  FloatSpec.Core.Generic_fmt.Valid_rnd rnd

/-- Compatibility name for the core exponent monotonicity predicate. -/
abbrev Monotone_exp (fexp : Int → Int) : Prop :=
  FloatSpec.Core.Generic_fmt.Monotone_exp fexp

/-
Coq: `Prec_gt_0 prec` asserts strictly positive precision.
We model it as `0 < prec` so arithmetic lemmas may use it.
-/
class Prec_lt_emax (prec emax : Int) : Prop where
  /-- Precision is strictly less than emax (IEEE 754 constraint) -/
  (prec_lt_emax : prec < emax)
  /-- emax is large enough for the exponent formula to work (emax ≥ 2) -/
  (emax_ge_2 : 2 ≤ emax)

/-- Compatibility name for the core non-FTZ exponent predicate. -/
abbrev Exp_not_FTZ (fexp : Int → Int) : Prop :=
  FloatSpec.Core.Ulp.Exp_not_FTZ fexp

/-- Compatibility name for exact float addition from `Calc.Operations`. -/
def Fplus {beta : Int} (x y : FlocqFloat beta) : FlocqFloat beta :=
  FloatSpec.Calc.Operations.Fplus beta x y

/-- Compatibility name for exact float multiplication from `Calc.Operations`. -/
def Fmult {beta : Int} (x y : FlocqFloat beta) : FlocqFloat beta :=
  FloatSpec.Calc.Operations.Fmult beta x y

/-- Compatibility name for float absolute value from `Calc.Operations`. -/
def Fabs {beta : Int} (x : FlocqFloat beta) : FlocqFloat beta :=
  FloatSpec.Calc.Operations.Fabs beta x

/-- Compatibility name for float negation from `Calc.Operations`. -/
def Fopp {beta : Int} (x : FlocqFloat beta) : FlocqFloat beta :=
  FloatSpec.Calc.Operations.Fopp beta x

/-- Flocq rounding to a float value

    Given a rounding function rnd (like Ztrunc, Zfloor, Zceil, Znearest),
    computes the canonical floating-point representation of the rounded value. -/
noncomputable def round_float (beta : Int) (fexp : Int → Int) (rnd : ℝ → Int) (x : ℝ) : FlocqFloat beta :=
  let exp := FloatSpec.Core.Generic_fmt.cexp beta fexp x
  let mantissa := x * (beta : ℝ) ^ (-exp)
  let rounded_mantissa := rnd mantissa
  FlocqFloat.mk rounded_mantissa exp

namespace FloatSpec.Compat.Scaffold

/-- Compatibility mode token for older translated files using `Calc.Round.Mode`. -/
noncomputable def ZnearestMode (choice : Int → Bool) : FloatSpec.Calc.Round.Mode where
  rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  rnd_zero := by
    unfold FloatSpec.Core.Generic_fmt.Znearest
    simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil,
      FloatSpec.Core.Raux.Rcompare]

end FloatSpec.Compat.Scaffold

/-- Scaffold compatibility alias retained for legacy translated files. -/
noncomputable def Znearest : (Int → Bool) → FloatSpec.Calc.Round.Mode :=
  FloatSpec.Compat.Scaffold.ZnearestMode
