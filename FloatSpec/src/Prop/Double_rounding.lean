-- Double rounding properties
-- Translated from Coq file: flocq/src/Prop/Double_rounding.v

import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import FloatSpec.src.Core.Generic_fmt
import Mathlib.Data.Real.Basic

open Real

variable (beta : Int)

-- Midpoint helpers (spec-variant of Coq's midp/midp')
noncomputable def midp (fexp : Int → Int) [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp] (x : ℝ) : ℝ :=
  -- We use the Calc.Round wrapper; mode is ignored in our model.
  FloatSpec.Calc.Round.round beta fexp (Znearest (fun _ => false)) x
    + (1/2) * (ulp beta fexp x)

noncomputable def midp' (fexp : Int → Int) [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp] (x : ℝ) : ℝ :=
  FloatSpec.Calc.Round.round beta fexp (Znearest (fun _ => false)) x
    - (1/2) * (ulp beta fexp x)

/-- Double rounding with two different precisions -/
theorem double_round_eq (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool) (x : ℝ)
  (h_precision : ∀ e, fexp2 e ≤ fexp1 e) :
  FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x) =
  FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x := by
  sorry

-- (reserved for later) Coq: `round_round_mult_hyp`
-- Structural hypothesis relating places for the product exponents.
-- We will introduce it if needed by subsequent lemmas.

/-- Coq: `round_round_mult_hyp`
    Structural relation between the places produced by `fexp1` and `fexp2`
    for products. -/
def round_round_mult_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex ey, fexp2 (ex + ey) ≤ fexp1 ex + fexp1 ey) ∧
  (∀ ex ey, fexp2 (ex + ey - 1) ≤ fexp1 ex + fexp1 ey)

/-- Coq: `round_round_mult_aux`
    Under `round_round_mult_hyp`, the product of two `fexp1`-generic
    numbers is `fexp2`-generic. -/
lemma round_round_mult_aux
  (fexp1 fexp2 : Int → Int)
  (Hh : round_round_mult_hyp fexp1 fexp2)
  (x y : ℝ)
  (Fx : generic_format beta fexp1 x)
  (Fy : generic_format beta fexp1 y) :
  generic_format beta fexp2 (x * y) := by
  sorry



/-- Coq: `round_round_lt_mid_further_place'`
    Conditions for innocuous double rounding when x lies sufficiently
    below both midpoints and fexp2 is at a further place. -/
theorem round_round_lt_mid_further_place'
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_place : fexp2 ((FloatSpec.Core.Raux.mag beta x).run)
              ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x).run) - 1)
  (hx_lt1 : x < (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x).run)
                  - (1/2) * (ulp beta fexp2 x))
  (hx_lt2 : x < midp (beta := beta) fexp1 x
                  - (1/2) * (ulp beta fexp2 x)) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x := by
  sorry

/-- Coq: `round_round_lt_mid_further_place`
    Further-place condition with an additional bound on `fexp1 (mag x)`
    ensuring innocuous double rounding below midpoints. -/
theorem round_round_lt_mid_further_place
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_place : fexp2 ((FloatSpec.Core.Raux.mag beta x).run)
              ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x).run) - 1)
  (h_f1_le_mag : fexp1 ((FloatSpec.Core.Raux.mag beta x).run) ≤ (FloatSpec.Core.Raux.mag beta x).run)
  (hx_lt : x < midp (beta := beta) fexp1 x - (1/2) * (ulp beta fexp2 x)) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x := by
  sorry

/-- Coq: `round_round_lt_mid_same_place`
    Same-place condition: if both formats have the same place at `mag x`
    and `x` lies below the midpoint, double rounding is innocuous. -/
theorem round_round_lt_mid_same_place
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_same : fexp2 ((FloatSpec.Core.Raux.mag beta x).run)
              = fexp1 ((FloatSpec.Core.Raux.mag beta x).run))
  (hx_lt_mid : x < midp (beta := beta) fexp1 x) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x := by
  sorry

/-- Coq: `round_round_lt_mid`
    Combined condition covering both same-place and further-place cases
    under a bound on `fexp1 (mag x)` and `x` below its midpoint. -/
theorem round_round_lt_mid
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_place_le : fexp2 ((FloatSpec.Core.Raux.mag beta x).run)
                ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x).run))
  (h_f1_le_mag : fexp1 ((FloatSpec.Core.Raux.mag beta x).run)
                ≤ (FloatSpec.Core.Raux.mag beta x).run)
  (hx_lt_mid : x < midp (beta := beta) fexp1 x)
  (hx_cond : (fexp2 ((FloatSpec.Core.Raux.mag beta x).run)
                ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x).run) - 1)
              → x < midp (beta := beta) fexp1 x - (1/2) * (ulp beta fexp2 x)) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x := by
  sorry

/-- Coq: `mag_mult_disj`
    For nonzero `x` and `y`, the magnitude of the product is either the
    sum of magnitudes or one less. -/
lemma mag_mult_disj (x y : ℝ)
  (hx : x ≠ 0) (hy : y ≠ 0) :
  ((FloatSpec.Core.Raux.mag beta (x * y)).run
      = (FloatSpec.Core.Raux.mag beta x).run + (FloatSpec.Core.Raux.mag beta y).run - 1)
  ∨ ((FloatSpec.Core.Raux.mag beta (x * y)).run
      = (FloatSpec.Core.Raux.mag beta x).run + (FloatSpec.Core.Raux.mag beta y).run) := by
  sorry

-- Coq: `round_round_mult_aux`
-- Under `round_round_mult_hyp`, the product of two `fexp1`-generic
-- numbers is `fexp2`-generic.
-- (reserved for later) Coq: `round_round_mult_aux` and `round_round_mult`
-- These will be added after `mag_mult_disj` compiles cleanly.

/-- Coq: `round_round_gt_mid_further_place'`
    Conditions for innocuous double rounding when x lies sufficiently
    above both midpoints and fexp2 is at a further place. -/
theorem round_round_gt_mid_further_place'
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_place : fexp2 ((FloatSpec.Core.Raux.mag beta x).run)
              ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x).run) - 1)
  (hx1 : FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x
            < (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x).run))
  (hx2 : midp' (beta := beta) fexp1 x + (1/2) * (ulp beta fexp2 x) < x) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x := by
  sorry

/-- Coq: `round_round_gt_mid_further_place`
    Further-place condition with an additional bound on `fexp1 (mag x)`
    ensuring innocuous double rounding above midpoints. -/
theorem round_round_gt_mid_further_place
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_place : fexp2 ((FloatSpec.Core.Raux.mag beta x).run)
              ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x).run) - 1)
  (h_f1_le_mag : fexp1 ((FloatSpec.Core.Raux.mag beta x).run)
                ≤ (FloatSpec.Core.Raux.mag beta x).run)
  (hx2 : midp' (beta := beta) fexp1 x + (1/2) * (ulp beta fexp2 x) < x) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x := by
  sorry

/-- Coq: `round_round_gt_mid_same_place`
    Same-place condition: if both formats have the same place at `mag x`
    and `x` lies above the midpoint, double rounding is innocuous. -/
theorem round_round_gt_mid_same_place
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_same : fexp2 ((FloatSpec.Core.Raux.mag beta x).run)
              = fexp1 ((FloatSpec.Core.Raux.mag beta x).run))
  (hx_gt_mid : midp' (beta := beta) fexp1 x < x) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x := by
  sorry

/-- Coq: `round_round_gt_mid`
    Combined condition covering both same-place and further-place cases
    under a bound on `fexp1 (mag x)` and `x` above its midpoint. -/
theorem round_round_gt_mid
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_place_le : fexp2 ((FloatSpec.Core.Raux.mag beta x).run)
                ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x).run))
  (h_f1_le_mag : fexp1 ((FloatSpec.Core.Raux.mag beta x).run)
                ≤ (FloatSpec.Core.Raux.mag beta x).run)
  (hx_gt_mid : midp' (beta := beta) fexp1 x < x)
  (hx_cond : (fexp2 ((FloatSpec.Core.Raux.mag beta x).run)
                ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x).run) - 1)
              → midp' (beta := beta) fexp1 x + (1/2) * (ulp beta fexp2 x) < x) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x := by
  sorry

/-- Double rounding property for FLX and FLT -/
theorem double_round_FLX_FLT (prec1 prec2 emin : Int) [Prec_gt_0 prec1] [Prec_gt_0 prec2]
  (choice1 choice2 : Int → Bool) (x : ℝ)
  (h_prec : prec2 ≤ prec1) :
  FloatSpec.Calc.Round.round beta (FLT_exp emin prec2) (Znearest choice2)
    (FloatSpec.Calc.Round.round beta (FLX_exp prec1) (Znearest choice1) x) =
  FloatSpec.Calc.Round.round beta (FLT_exp emin prec2) (Znearest choice2) x := by
  sorry

/-- Double rounding for same format is identity -/
theorem double_round_same (fexp : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp] (choice : Int → Bool) (x : ℝ) :
  FloatSpec.Calc.Round.round beta fexp (Znearest choice) (FloatSpec.Calc.Round.round beta fexp (Znearest choice) x) =
  FloatSpec.Calc.Round.round beta fexp (Znearest choice) x := by
  sorry

/-- Coq: `round_round_plus`
    Skeleton lemma asserting innocuous double rounding for a sum under
    appropriate magnitude/place side-conditions. We mirror the name and
    interface as a placeholder; the proof will be added later. -/
lemma round_round_plus
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (x y : ℝ) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x + y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x + y) := by
  sorry

/-- Coq: `round_round_minus`
    Skeleton lemma asserting innocuous double rounding for a difference
    under appropriate hypotheses. -/
lemma round_round_minus
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (x y : ℝ) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x - y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x - y) := by
  sorry
