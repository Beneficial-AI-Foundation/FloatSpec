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

/-- Bridge: Float to real as a plain ℝ (unwraps Id) -/
noncomputable abbrev F2R {beta : Int} [ValidRadix beta] (f : FlocqFloat beta) : ℝ :=
  (FloatSpec.Core.Defs.F2R f)

/-- Bridge: {name (full := FloatSpec.Core.Generic_fmt.generic_format)}`generic_format` as a plain Prop (unwraps Id) -/
noncomputable abbrev generic_format (beta : Int) [ValidRadix beta] (fexp : Int → Int) (x : ℝ) : Prop :=
  FloatSpec.Core.Generic_fmt.generic_format beta fexp x

/-- Bridge: magnitude function in root namespace -/
noncomputable abbrev mag (beta : Int) [ValidRadix beta] (x : ℝ) : Int :=
  (FloatSpec.Core.Raux.mag beta x)

/-- Bridge: integer truncation toward zero -/
noncomputable abbrev Ztrunc (x : ℝ) : Int :=
  (FloatSpec.Core.Raux.Ztrunc x)

/-- Fixed-exponent function selecting the provided exponent. -/
abbrev FIX_exp (emin : Int) : Int → Int := fun _ => emin

/-- Bridge: ulp as a plain ℝ (unwraps Id) -/
noncomputable abbrev ulp (beta : Int) [ValidRadix beta] (fexp : Int → Int) (x : ℝ) : ℝ :=
  (FloatSpec.Core.Ulp.ulp beta fexp x)

/-- Bridge: canonical exponent as plain Int -/
noncomputable abbrev cexp (beta : Int) [ValidRadix beta] (fexp : Int → Int) (x : ℝ) : Int :=
  FloatSpec.Core.Generic_fmt.cexp beta fexp x

/-- Bridge: FLX exponent function in root namespace -/
abbrev FLX_exp (prec : Int) : Int → Int :=
  FloatSpec.Core.FLX.FLX_exp prec

/-- Bridge: FLT exponent function in root namespace -/
abbrev FLT_exp (emin prec : Int) : Int → Int :=
  FloatSpec.Core.FLT.FLT_exp prec emin

-- Namespace aliases so existing references like `FloatSpec.Compat.Ztrunc` work.
namespace FloatSpec.Compat
/-- Namespace alias for {name}`Ztrunc`. -/
noncomputable abbrev Ztrunc := _root_.Ztrunc
/-- Namespace alias for {name}`FIX_exp`. -/
abbrev FIX_exp := _root_.FIX_exp
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

/-- Coq's `Prec_lt_emax` exports only `prec < emax`.  The lower bound on
`emax` used by binary-format proofs is a consequence of the separate
`Prec_gt_0` premise, not an additional field of the class. -/
theorem Prec_lt_emax.emax_ge_2 {prec emax : Int}
    [Prec_gt_0 prec] (h : Prec_lt_emax prec emax) : 2 ≤ emax := by
  have hprec_pos := (inferInstance : Prec_gt_0 prec).pos
  have hprec_lt := h.prec_lt_emax
  omega

/-- Compatibility name for the core non-FTZ exponent predicate. -/
abbrev Exp_not_FTZ (fexp : Int → Int) : Prop :=
  FloatSpec.Core.Ulp.Exp_not_FTZ fexp

/-- Compatibility name for exact float addition from `Calc.Operations`. -/
abbrev Fplus {beta : Int} [ValidRadix beta] (x y : FlocqFloat beta) : FlocqFloat beta :=
  FloatSpec.Calc.Operations.Fplus beta x y

/-- Compatibility name for exact float multiplication from `Calc.Operations`. -/
abbrev Fmult {beta : Int} [ValidRadix beta] (x y : FlocqFloat beta) : FlocqFloat beta :=
  FloatSpec.Calc.Operations.Fmult beta x y

/-- Compatibility name for float absolute value from `Calc.Operations`. -/
abbrev Fabs {beta : Int} [ValidRadix beta] (x : FlocqFloat beta) : FlocqFloat beta :=
  FloatSpec.Calc.Operations.Fabs beta x

/-- Compatibility name for float negation from `Calc.Operations`. -/
abbrev Fopp {beta : Int} [ValidRadix beta] (x : FlocqFloat beta) : FlocqFloat beta :=
  FloatSpec.Calc.Operations.Fopp beta x

/-- Flocq rounding to a float value

    Given a rounding function rnd (like Ztrunc, Zfloor, Zceil, Znearest),
    computes the canonical floating-point representation of the rounded value. -/
noncomputable def round_float (beta : Int) [ValidRadix beta] (fexp : Int → Int)
    (rnd : ℝ → Int) (x : ℝ) : FlocqFloat beta :=
  let exp := FloatSpec.Core.Generic_fmt.cexp beta fexp x
  let mantissa := x * (beta : ℝ) ^ (-exp)
  let rounded_mantissa := rnd mantissa
  FlocqFloat.mk rounded_mantissa exp

namespace FloatSpec.Compat.Scaffold

/-- Compatibility mode token for older translated files using `Calc.Round.Mode`. -/
noncomputable abbrev ZnearestMode (choice : Int → Bool) : FloatSpec.Calc.Round.Mode where
  rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  rnd_zero := by
    unfold FloatSpec.Core.Generic_fmt.Znearest
    simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil,
      FloatSpec.Core.Raux.Rcompare]

end FloatSpec.Compat.Scaffold

/-- Scaffold compatibility alias retained for legacy translated files. -/
noncomputable abbrev Znearest : (Int → Bool) → FloatSpec.Calc.Round.Mode :=
  FloatSpec.Compat.Scaffold.ZnearestMode
