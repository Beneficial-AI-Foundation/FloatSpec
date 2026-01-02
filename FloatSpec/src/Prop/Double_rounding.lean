-- Double rounding properties
-- Translated from Coq file: flocq/src/Prop/Double_rounding.v

import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import FloatSpec.src.Core.Generic_fmt
import FloatSpec.src.Core.FTZ
import Mathlib.Data.Real.Basic

open Real
open FloatSpec.Core.FTZ

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

/-
  Coq: `round_round_lt_mid_further_place`

  Hypotheses: `0 < x`, place relation `fexp2 (mag x) ≤ fexp1 (mag x) - 1`,
  and `fexp1 (mag x) ≤ mag x`, together with a strict bound placing `x`
  to the left of the `fexp1`-midpoint minus half a `fexp2`-ULP.

  Conclusion: nearest-on-nearest double rounding from `fexp2` to `fexp1`
  is innocuous. We mirror the statement and leave the proof as a placeholder.
-/
theorem round_round_lt_mid_further_place
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_place : fexp2 ((FloatSpec.Core.Raux.mag beta x))
              ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 1)
  (h_f1_le_mag : fexp1 ((FloatSpec.Core.Raux.mag beta x))
                ≤ (FloatSpec.Core.Raux.mag beta x))
  (hx_lt : x < midp (beta := beta) fexp1 x - (1/2) * (ulp beta fexp2 x)) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x := by
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


/-- Coq: `round_round_mult`
    If the product of two `fexp1`-generic numbers is always
    `fexp2`-generic (captured by `round_round_mult_hyp` together with
    `round_round_mult_aux`), then rounding the product twice with the
    same rounding mode `rnd` is innocuous. -/
theorem round_round_mult
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (mode : FloatSpec.Calc.Round.Mode)
  (Hh : round_round_mult_hyp fexp1 fexp2)
  (x y : ℝ)
  (Fx : generic_format beta fexp1 x)
  (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 mode
      (FloatSpec.Calc.Round.round beta fexp2 mode (x * y))
  = FloatSpec.Calc.Round.round beta fexp1 mode (x * y) := by
  sorry

/-- Coq: `round_round_mult_FLX`
    Double rounding for products in FLX under the precision relation
    `2 * prec ≤ prec'`. -/
theorem round_round_mult_FLX
  (prec prec' : Int) [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec')]
  (mode : FloatSpec.Calc.Round.Mode)
  (x y : ℝ)
  (hprec : 2 * prec ≤ prec')
  (Fx : generic_format beta (FLX_exp prec) x)
  (Fy : generic_format beta (FLX_exp prec) y) :
  FloatSpec.Calc.Round.round beta (FLX_exp prec) mode
    (FloatSpec.Calc.Round.round beta (FLX_exp prec') mode (x * y))
  = FloatSpec.Calc.Round.round beta (FLX_exp prec) mode (x * y) := by
  sorry

/-- Coq: `round_round_mult_FLT`
    Double rounding for products in FLT under relations on exponents
    and precisions. -/
theorem round_round_mult_FLT
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin' prec')]
  (mode : FloatSpec.Calc.Round.Mode)
  (x y : ℝ)
  (Hemin : emin' ≤ 2 * emin) (Hprec : 2 * prec ≤ prec')
  (Fx : generic_format beta (FLT_exp emin prec) x)
  (Fy : generic_format beta (FLT_exp emin prec) y) :
  FloatSpec.Calc.Round.round beta (FLT_exp emin prec) mode
    (FloatSpec.Calc.Round.round beta (FLT_exp emin' prec') mode (x * y))
  = FloatSpec.Calc.Round.round beta (FLT_exp emin prec) mode (x * y) := by
  sorry

/-- Coq: `round_round_mult_FTZ`
    Double rounding for products in FTZ under relations on exponents
    and precisions. -/
theorem round_round_mult_FTZ
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp emin prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp emin' prec')]
  (mode : FloatSpec.Calc.Round.Mode)
  (x y : ℝ)
  (Hemin : emin' + prec' ≤ 2 * emin + prec) (Hprec : 2 * prec ≤ prec')
  (Fx : generic_format beta (FTZ_exp emin prec) x)
  (Fy : generic_format beta (FTZ_exp emin prec) y) :
  FloatSpec.Calc.Round.round beta (FTZ_exp emin prec) mode
    (FloatSpec.Calc.Round.round beta (FTZ_exp emin' prec') mode (x * y))
  = FloatSpec.Calc.Round.round beta (FTZ_exp emin prec) mode (x * y) := by
  sorry


/-- Coq: `round_round_mid_cases`
    Midpoint case splitter: assuming `0 < x`, a place relation
    `fexp2 (mag x) ≤ fexp1 (mag x) - 1`, and `fexp1 (mag x) ≤ mag x`,
    if the absolute gap to the `fexp1`-midpoint is at most
    `1/2 * ulp fexp2 x`, then double rounding (nearest-on-nearest)
    from `fexp2` to `fexp1` equals a single rounding at `fexp1`. -/
lemma round_round_mid_cases
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_place : fexp2 ((FloatSpec.Core.Raux.mag beta x))
              ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 1)
  (h_f1_le_mag : fexp1 ((FloatSpec.Core.Raux.mag beta x))
                ≤ (FloatSpec.Core.Raux.mag beta x))
  (Cmid : |x - midp (beta := beta) fexp1 x|
            ≤ (1/2) * (ulp beta fexp2 x) →
          FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
            (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
          = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x := by
  sorry

/-- Coq: `round_round_eq_mid_beta_even`
    Midpoint equality case under an even-base assumption on `beta`.
    If `x` equals the `fexp1`-midpoint, with `fexp2 (mag x) ≤ fexp1 (mag x) - 1`
    and `fexp1 (mag x) ≤ mag x`, then nearest-on-nearest double rounding
    from `fexp2` to `fexp1` is innocuous. -/
lemma round_round_eq_mid_beta_even
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Ebeta : ∃ n : Int, beta = 2 * n)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_place : fexp2 ((FloatSpec.Core.Raux.mag beta x))
              ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 1)
  (h_f1_le_mag : fexp1 ((FloatSpec.Core.Raux.mag beta x))
                ≤ (FloatSpec.Core.Raux.mag beta x))
  (hx_mid : x = midp (beta := beta) fexp1 x) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x := by
  sorry

/-- Coq: `round_round_really_zero`
    If `fexp1 (mag x)` is at least two places beyond `mag x` and `x > 0`,
    then double rounding (nearest-on-nearest) from `fexp2` to `fexp1`
    is innocuous. -/
lemma round_round_really_zero
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_f1 : (FloatSpec.Core.Raux.mag beta x)
            ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 2) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x := by
  sorry

/-- Coq: `round_round_zero`
    Special case where `fexp1 (mag x) = mag x + 1` and `x` lies strictly
    below `bpow (mag x) - 1/2 * ulp fexp2 x`; double rounding is innocuous. -/
lemma round_round_zero
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_f1 : fexp1 ((FloatSpec.Core.Raux.mag beta x))
            = (FloatSpec.Core.Raux.mag beta x) + 1)
  (hx_lt : x < (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x))
              - (1/2) * (ulp beta fexp2 x)) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x := by
  sorry

/-- Coq: `round_round_all_mid_cases`
    All-mid-cases splitter used by the division lemmas later: under
    `fexp2 (mag x) ≤ fexp1 (mag x) - 1`, reduce to near-midpoint cases
    or to the equality midpoint case guarded by an even `beta` premise. -/
lemma round_round_all_mid_cases
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_place : fexp2 ((FloatSpec.Core.Raux.mag beta x))
              ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 1)
  (case1 : (fexp1 ((FloatSpec.Core.Raux.mag beta x))
              = (FloatSpec.Core.Raux.mag beta x) + 1)
            → (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x))
              - (1/2) * (ulp beta fexp2 x) ≤ x
            → FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
                (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
              = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x)
  (case2 : (fexp1 ((FloatSpec.Core.Raux.mag beta x))
              ≤ (FloatSpec.Core.Raux.mag beta x))
            → midp (beta := beta) fexp1 x - (1/2) * (ulp beta fexp2 x) ≤ x
            → x < midp (beta := beta) fexp1 x
            → FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
                (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
              = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x)
  (case3 : (fexp1 ((FloatSpec.Core.Raux.mag beta x))
              ≤ (FloatSpec.Core.Raux.mag beta x))
            → x = midp (beta := beta) fexp1 x
            → FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
                (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
              = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x)
  (case4 : (fexp1 ((FloatSpec.Core.Raux.mag beta x))
              ≤ (FloatSpec.Core.Raux.mag beta x))
            → midp (beta := beta) fexp1 x < x
            → x ≤ midp (beta := beta) fexp1 x + (1/2) * (ulp beta fexp2 x)
            → FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
                (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
              = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x)
  (case5 : (fexp1 ((FloatSpec.Core.Raux.mag beta x))
              = (FloatSpec.Core.Raux.mag beta x) + 1)
            → x < (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x))
                - (1/2) * (ulp beta fexp2 x)
            → FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
                (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
              = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x)
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x := by
  sorry

/-- Coq: `mag_sqrt_disj`
    For positive `x`, the magnitude of `x` is either
    `2 * mag (sqrt x) - 1` or exactly `2 * mag (sqrt x)`.
    We mirror the Coq statement and leave the proof as a placeholder. -/
lemma mag_sqrt_disj (x : ℝ)
  (hx_pos : 0 < x) :
  ((FloatSpec.Core.Raux.mag beta x)
      = 2 * (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1)
  ∨ ((FloatSpec.Core.Raux.mag beta x)
      = 2 * (FloatSpec.Core.Raux.mag beta (Real.sqrt x))) := by
  sorry


/-- Coq: `round_round_sqrt_hyp`
    Structural hypothesis used for analyzing double rounding on square
    roots. We mirror the Coq definition. -/
def round_round_sqrt_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex)) ∧
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex - 1)) ∧
  (∀ ex, fexp1 (2 * ex) < 2 * ex → fexp2 ex + ex ≤ 2 * fexp1 ex - 2)

/-- Coq: `round_round_sqrt_aux`
    Under `round_round_sqrt_hyp`, positivity of `x`, a place relation at
    `mag (sqrt x)`, and `fexp1`-genericity of `x`, the midpoint gap for
    `sqrt x` is larger than `1/2 * ulp fexp2 (sqrt x)`. We keep the same
    name and leave the proof as a placeholder. -/
lemma round_round_sqrt_aux
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (Hexp : round_round_sqrt_hyp fexp1 fexp2)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_place : fexp2 ((FloatSpec.Core.Raux.mag beta (Real.sqrt x)))
              ≤ fexp1 ((FloatSpec.Core.Raux.mag beta (Real.sqrt x))) - 1)
  (Fx : generic_format beta fexp1 x) :
  (1/2) * (ulp beta fexp2 (Real.sqrt x))
    < |Real.sqrt x - midp (beta := beta) fexp1 (Real.sqrt x)| := by
  sorry

/-- Coq: `round_round_sqrt` 
    If `round_round_sqrt_hyp` holds and `x` is `fexp1`-generic with the
    place relation at `mag (sqrt x)`, then nearest-on-nearest double
    rounding of `sqrt x` from `fexp2` to `fexp1` is innocuous. -/
lemma round_round_sqrt
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_sqrt_hyp fexp1 fexp2)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_place : fexp2 ((FloatSpec.Core.Raux.mag beta (Real.sqrt x)))
              ≤ fexp1 ((FloatSpec.Core.Raux.mag beta (Real.sqrt x))) - 1)
  (Fx : generic_format beta fexp1 x) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (Real.sqrt x))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (Real.sqrt x) := by
  sorry

/-- Coq: `FLX_round_round_sqrt_hyp`
    In FLX, the structural hypothesis for sqrt double rounding holds
    without additional side conditions. -/
lemma FLX_round_round_sqrt_hyp
  (prec prec' : Int) [Prec_gt_0 prec] [Prec_gt_0 prec'] :
  round_round_sqrt_hyp (FLX_exp prec) (FLX_exp prec') := by
  sorry

/-- Coq: `round_round_sqrt_FLX`
    For FLX with `2 * prec + 2 ≤ prec'`, nearest-on-nearest double
    rounding of `sqrt x` from `(FLX_exp prec')` to `(FLX_exp prec)` is
    innocuous. -/
theorem round_round_sqrt_FLX
  (prec prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec')]
  (choice1 choice2 : Int → Bool)
  (hprec : 2 * prec + 2 ≤ prec')
  (x : ℝ)
  (Fx : generic_format beta (FLX_exp prec) x) :
  FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FLX_exp prec') (Znearest choice2) (Real.sqrt x))
  = FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice1) (Real.sqrt x) := by
  sorry

/-- Coq: `FLT_round_round_sqrt_hyp`
    Sufficient conditions for FLT exponents to satisfy the
    `round_round_sqrt_hyp` (non-radix-ge-4 variant). -/
lemma FLT_round_round_sqrt_hyp
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  (Hemin : emin ≤ 0)
  (Hrel : emin' ≤ emin - prec - 2 ∨ 2 * emin' ≤ emin - 4 * prec - 2)
  (Hprec : 2 * prec + 2 ≤ prec') :
  round_round_sqrt_hyp (FLT_exp emin prec) (FLT_exp emin' prec') := by
  sorry

/-- Coq: `round_round_sqrt_FLT`
    Under `Hemin`, `Hrel`, and `2 * prec + 2 ≤ prec'`, nearest-on-nearest
    double rounding of `sqrt x` from `(FLT_exp emin' prec')` to
    `(FLT_exp emin prec)` is innocuous. -/
theorem round_round_sqrt_FLT
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin' prec')]
  (choice1 choice2 : Int → Bool)
  (Hemin : emin ≤ 0)
  (Hrel : emin' ≤ emin - prec - 2 ∨ 2 * emin' ≤ emin - 4 * prec - 2)
  (Hprec : 2 * prec + 2 ≤ prec')
  (x : ℝ)
  (Fx : generic_format beta (FLT_exp emin prec) x) :
  FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FLT_exp emin' prec') (Znearest choice2) (Real.sqrt x))
  = FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice1) (Real.sqrt x) := by
  sorry


/-
  Coq: `round_round_sqrt_radix_ge_4_hyp`
  Strengthened hypothesis used for sqrt when the radix satisfies `4 ≤ beta`.
-/
def round_round_sqrt_radix_ge_4_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex)) ∧
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex - 1)) ∧
  (∀ ex, fexp1 (2 * ex) < 2 * ex → fexp2 ex + ex ≤ 2 * fexp1 ex - 1)


/-- Coq: `round_round_sqrt_radix_ge_4_aux`
    Under `4 ≤ beta` and `round_round_sqrt_radix_ge_4_hyp`, if `0 < x`,
    `fexp2 (mag (sqrt x)) ≤ fexp1 (mag (sqrt x)) - 1`, and `x` is
    `fexp1`-generic, then the midpoint gap at `sqrt x` is strictly larger
    than `1/2 * ulp fexp2 (sqrt x)`. -/
lemma round_round_sqrt_radix_ge_4_aux
  (Hbeta : 4 ≤ beta)
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (Hexp : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2)
  (x : ℝ)
  (hx_pos : 0 < x)
  (h_place : fexp2 ((FloatSpec.Core.Raux.mag beta (Real.sqrt x)))
              ≤ fexp1 ((FloatSpec.Core.Raux.mag beta (Real.sqrt x))) - 1)
  (Fx : generic_format beta fexp1 x) :
  (1/2) * (ulp beta fexp2 (Real.sqrt x))
    < |Real.sqrt x - midp (beta := beta) fexp1 (Real.sqrt x)| := by
  sorry

/-- Coq: `round_round_sqrt_radix_ge_4`
    Under `4 ≤ beta` and `round_round_sqrt_radix_ge_4_hyp`, if `x` is
    `fexp1`-generic and `fexp2 (mag (sqrt x)) ≤ fexp1 (mag (sqrt x)) - 1`,
    then nearest-on-nearest double rounding of `sqrt x` from `fexp2` to
    `fexp1` collapses to a single rounding at `fexp1`. -/
lemma round_round_sqrt_radix_ge_4
  (Hbeta : 4 ≤ beta)
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2)
  (x : ℝ)
  (Fx : generic_format beta fexp1 x)
  (h_place : fexp2 ((FloatSpec.Core.Raux.mag beta (Real.sqrt x)))
              ≤ fexp1 ((FloatSpec.Core.Raux.mag beta (Real.sqrt x))) - 1) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (Real.sqrt x))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (Real.sqrt x) := by
  sorry

/-- Coq: `FLX_round_round_sqrt_radix_ge_4_hyp`
    For FLX exponents, the `round_round_sqrt_radix_ge_4_hyp` holds
    unconditionally. -/
lemma FLX_round_round_sqrt_radix_ge_4_hyp
  (prec prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec'] :
  round_round_sqrt_radix_ge_4_hyp (FLX_exp prec) (FLX_exp prec') := by
  sorry

/-- Coq: `round_round_sqrt_radix_ge_4_FLX`
    Under `4 ≤ beta` and `2 * prec + 1 ≤ prec'`, double rounding of
    `sqrt x` from `(FLX_exp prec')` to `(FLX_exp prec)` collapses. -/
theorem round_round_sqrt_radix_ge_4_FLX
  (prec prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec')]
  (choice1 choice2 : Int → Bool)
  (Hbeta : 4 ≤ beta)
  (hprec : 2 * prec + 1 ≤ prec')
  (x : ℝ)
  (Fx : generic_format beta (FLX_exp prec) x) :
  FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FLX_exp prec') (Znearest choice2) (Real.sqrt x))
  = FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice1) (Real.sqrt x) := by
  sorry

/-- Coq: `FLT_round_round_sqrt_radix_ge_4_hyp`
    Sufficient conditions for FLT exponents to satisfy the
    `round_round_sqrt_radix_ge_4_hyp`. -/
lemma FLT_round_round_sqrt_radix_ge_4_hyp
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  (Hemin : emin ≤ 0)
  (Hrel : emin' ≤ emin - prec - 1 ∨ 2 * emin' ≤ emin - 4 * prec)
  (Hprec : 2 * prec + 1 ≤ prec') :
  round_round_sqrt_radix_ge_4_hyp (FLT_exp emin prec) (FLT_exp emin' prec') := by
  sorry

/-- Coq: `round_round_sqrt_radix_ge_4_FLT`
    Under `4 ≤ beta` and the above FLT relations, double rounding of
    `sqrt x` from `(FLT_exp emin' prec')` to `(FLT_exp emin prec)` collapses. -/
theorem round_round_sqrt_radix_ge_4_FLT
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin' prec')]
  (choice1 choice2 : Int → Bool)
  (Hbeta : 4 ≤ beta)
  (Hemin : emin ≤ 0)
  (Hrel : emin' ≤ emin - prec - 1 ∨ 2 * emin' ≤ emin - 4 * prec)
  (Hprec : 2 * prec + 1 ≤ prec')
  (x : ℝ)
  (Fx : generic_format beta (FLT_exp emin prec) x) :
  FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FLT_exp emin' prec') (Znearest choice2) (Real.sqrt x))
  = FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice1) (Real.sqrt x) := by
  sorry

/-- Coq: `FTZ_round_round_sqrt_hyp`
    Sufficient conditions for FTZ exponents to satisfy the base
    `round_round_sqrt_hyp`. -/
lemma FTZ_round_round_sqrt_hyp
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  (Hemin : 2 * (emin' + prec') ≤ emin + prec ∧ emin + prec ≤ 1)
  (Hprec : 2 * prec + 2 ≤ prec') :
  round_round_sqrt_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec') := by
  sorry

/-- Coq: `round_round_sqrt_FTZ`
    Under `4 ≤ beta` and the above FTZ relations, nearest-on-nearest
    double rounding of `sqrt x` from `(FTZ_exp emin' prec')` to
    `(FTZ_exp emin prec)` collapses to a single rounding at
    `(FTZ_exp emin prec)`. -/
theorem round_round_sqrt_FTZ
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp emin prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp emin' prec')]
  (choice1 choice2 : Int → Bool)
  (Hbeta : 4 ≤ beta)
  (Hemin : 2 * (emin' + prec') ≤ emin + prec ∧ emin + prec ≤ 1)
  (Hprec : 2 * prec + 2 ≤ prec')
  (x : ℝ)
  (Fx : generic_format beta (FTZ_exp emin prec) x) :
  FloatSpec.Calc.Round.round beta (FTZ_exp emin prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FTZ_exp emin' prec') (Znearest choice2) (Real.sqrt x))
  = FloatSpec.Calc.Round.round beta (FTZ_exp emin prec) (Znearest choice1) (Real.sqrt x) := by
  sorry

/-- Coq: `FTZ_round_round_sqrt_radix_ge_4_hyp`
    Sufficient conditions for FTZ exponents to satisfy the
    `round_round_sqrt_radix_ge_4_hyp`. -/
lemma FTZ_round_round_sqrt_radix_ge_4_hyp
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  (Hemin : 2 * (emin' + prec') ≤ emin + prec ∧ emin + prec ≤ 1)
  (Hprec : 2 * prec + 1 ≤ prec') :
  round_round_sqrt_radix_ge_4_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec') := by
  sorry

/-- Coq: `round_round_sqrt_radix_ge_4_FTZ`
    Under `4 ≤ beta` and the above FTZ relations, double rounding of
    `sqrt x` from `(FTZ_exp emin' prec')` to `(FTZ_exp emin prec)` collapses. -/
theorem round_round_sqrt_radix_ge_4_FTZ
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp emin prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp emin' prec')]
  (choice1 choice2 : Int → Bool)
  (Hbeta : 4 ≤ beta)
  (Hemin : 2 * (emin' + prec') ≤ emin + prec ∧ emin + prec ≤ 1)
  (Hprec : 2 * prec + 1 ≤ prec')
  (x : ℝ)
  (Fx : generic_format beta (FTZ_exp emin prec) x) :
  FloatSpec.Calc.Round.round beta (FTZ_exp emin prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FTZ_exp emin' prec') (Znearest choice2) (Real.sqrt x))
  = FloatSpec.Calc.Round.round beta (FTZ_exp emin prec) (Znearest choice1) (Real.sqrt x) := by
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
  (h_place : fexp2 ((FloatSpec.Core.Raux.mag beta x))
              ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 1)
  (hx_lt1 : x < (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x))
                  - (1/2) * (ulp beta fexp2 x))
  (hx_lt2 : x < midp (beta := beta) fexp1 x
                  - (1/2) * (ulp beta fexp2 x)) :
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
  (h_same : fexp2 ((FloatSpec.Core.Raux.mag beta x))
              = fexp1 ((FloatSpec.Core.Raux.mag beta x)))
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
  (h_place_le : fexp2 ((FloatSpec.Core.Raux.mag beta x))
                ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)))
  (h_f1_le_mag : fexp1 ((FloatSpec.Core.Raux.mag beta x))
                ≤ (FloatSpec.Core.Raux.mag beta x))
  (hx_lt_mid : x < midp (beta := beta) fexp1 x)
  (hx_cond : (fexp2 ((FloatSpec.Core.Raux.mag beta x))
                ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 1)
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
  ((FloatSpec.Core.Raux.mag beta (x * y))
      = (FloatSpec.Core.Raux.mag beta x) + (FloatSpec.Core.Raux.mag beta y) - 1)
  ∨ ((FloatSpec.Core.Raux.mag beta (x * y))
      = (FloatSpec.Core.Raux.mag beta x) + (FloatSpec.Core.Raux.mag beta y)) := by
  sorry

/-- Coq: `mag_div_disj`
    For positive `x` and `y`, the magnitude of the quotient `x / y`
    is either `mag x - mag y` or exactly one greater. -/
lemma mag_div_disj (x y : ℝ)
  (hx_pos : 0 < x) (hy_pos : 0 < y) :
  ((FloatSpec.Core.Raux.mag beta (x / y))
      = (FloatSpec.Core.Raux.mag beta x) - (FloatSpec.Core.Raux.mag beta y))
  ∨ ((FloatSpec.Core.Raux.mag beta (x / y))
      = (FloatSpec.Core.Raux.mag beta x) - (FloatSpec.Core.Raux.mag beta y) + 1) := by
  sorry

/-- Coq: `round_round_div_hyp`
    Structural hypothesis relating `fexp1` and `fexp2` for analyzing
    double rounding of divisions. -/
def round_round_div_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex, fexp2 ex ≤ fexp1 ex - 1) ∧
  (∀ ex ey, fexp1 ex < ex → fexp1 ey < ey →
            fexp1 (ex - ey) ≤ ex - ey + 1 →
            fexp2 (ex - ey) ≤ fexp1 ex - ey) ∧
  (∀ ex ey, fexp1 ex < ex → fexp1 ey < ey →
            fexp1 (ex - ey + 1) ≤ ex - ey + 1 + 1 →
            fexp2 (ex - ey + 1) ≤ fexp1 ex - ey) ∧
  (∀ ex ey, fexp1 ex < ex → fexp1 ey < ey →
            fexp1 (ex - ey) ≤ ex - ey →
            fexp2 (ex - ey) ≤ fexp1 (ex - ey) + fexp1 ey - ey) ∧
  (∀ ex ey, fexp1 ex < ex → fexp1 ey < ey →
            fexp1 (ex - ey) = ex - ey + 1 →
            fexp2 (ex - ey) ≤ ex - ey - ey + fexp1 ey)

/-- Coq: `round_round_div_aux0`
    First auxiliary inequality used in the division double-rounding
    analysis when the place equals `mag (x / y) + 1`. -/
lemma round_round_div_aux0
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_div_hyp fexp1 fexp2)
  (x y : ℝ)
  (hx_pos : 0 < x) (hy_pos : 0 < y)
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y)
  (hplace : fexp1 ((FloatSpec.Core.Raux.mag beta (x / y)))
            = (FloatSpec.Core.Raux.mag beta (x / y)) + 1) :
  ¬ ((beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta (x / y)))
        - (1/2) * (ulp beta fexp2 (x / y)) ≤ x / y) := by
  sorry

/-- Coq: `round_round_div_aux1`
    In the division setting, under `round_round_div_hyp` and assuming
    positivity and genericity hypotheses, the mid-interval above `x/y`
    cannot occur when `fexp1 (mag (x / y)) ≤ mag (x / y)`.
    This is used as a case in the all-mid-cases analysis. -/
lemma round_round_div_aux1
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_div_hyp fexp1 fexp2)
  (x y : ℝ)
  (hx_pos : 0 < x) (hy_pos : 0 < y)
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y)
  (h_f1_le : fexp1 ((FloatSpec.Core.Raux.mag beta (x / y)))
              ≤ (FloatSpec.Core.Raux.mag beta (x / y))) :
  ¬ (midp (beta := beta) fexp1 (x / y) - (1/2) * (ulp beta fexp2 (x / y)) ≤ x / y
      ∧ x / y < midp (beta := beta) fexp1 (x / y)) := by
  sorry

/-- Coq: `round_round_div_aux2`
    Companion inequality used in the all-mid-cases division analysis
    for the complementary magnitude split. -/
lemma round_round_div_aux2
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_div_hyp fexp1 fexp2)
  (x y : ℝ)
  (hx_pos : 0 < x) (hy_pos : 0 < y)
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y)
  (h_f1_gt : (FloatSpec.Core.Raux.mag beta (x / y))
              < fexp1 ((FloatSpec.Core.Raux.mag beta (x / y)))) :
  ¬ (midp (beta := beta) fexp1 (x / y) ≤ x / y
      ∧ x / y < midp (beta := beta) fexp1 (x / y) + (1/2) * (ulp beta fexp2 (x / y))) := by
  sorry

/-/ Coq: `round_round_div_aux`
    Positive case: under an even-base hypothesis `beta = 2*n` and the
    structural hypothesis `round_round_div_hyp`, for `0 < x` and `0 < y`
    with `fexp1`-genericity of both operands, nearest-on-nearest double
    rounding of `x / y` from `fexp2` to `fexp1` collapses to a single
    rounding at `fexp1`. -/
lemma round_round_div_aux
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Ebeta : ∃ n : Int, beta = 2 * n)
  (Hexp : round_round_div_hyp fexp1 fexp2)
  (x y : ℝ)
  (hx_pos : 0 < x) (hy_pos : 0 < y)
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x / y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x / y) := by
  sorry

-- Coq: `round_round_mult_aux`
-- Under `round_round_mult_hyp`, the product of two `fexp1`-generic
-- numbers is `fexp2`-generic.
-- (reserved for later) Coq: `round_round_mult_aux` and `round_round_mult`
-- These will be added after `mag_mult_disj` compiles cleanly.

/-- Coq: `round_round_div`
    General double-rounding property for divisions under the structural
    hypothesis `round_round_div_hyp` and an even-base assumption on `beta`.
    We mirror the Coq statement and leave the proof as a placeholder. -/
lemma round_round_div
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Ebeta : ∃ n : Int, beta = 2 * n)
  (Hexp : round_round_div_hyp fexp1 fexp2)
  (x y : ℝ)
  (hy_nz : y ≠ 0)
  (Fx : generic_format beta fexp1 x)
  (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x / y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x / y) := by
  sorry

/-- Coq: `FLX_round_round_div_hyp`
    Under `2 * prec ≤ prec'`, the division structural hypothesis holds
    between `(FLX_exp prec)` and `(FLX_exp prec')`. -/
lemma FLX_round_round_div_hyp
  (prec prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  (hprec : 2 * prec ≤ prec') :
  round_round_div_hyp (FLX_exp prec) (FLX_exp prec') := by
  sorry

/-- Coq: `round_round_div_FLX`
    For FLX with an even radix and `2 * prec ≤ prec'`, nearest-on-nearest
    double rounding of a quotient collapses to a single rounding at
    `(FLX_exp prec)`. -/
theorem round_round_div_FLX
  (prec prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec')]
  (choice1 choice2 : Int → Bool)
  (Ebeta : ∃ n : Int, beta = 2 * n)
  (hprec : 2 * prec ≤ prec')
  (x y : ℝ)
  (hy_nz : y ≠ 0)
  (Fx : generic_format beta (FLX_exp prec) x)
  (Fy : generic_format beta (FLX_exp prec) y) :
  FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FLX_exp prec') (Znearest choice2) (x / y))
  = FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice1) (x / y) := by
  sorry

/-- Coq: `FLT_round_round_div_hyp`
    Under `emin' ≤ emin - prec - 2` and `2 * prec ≤ prec'`, the division
    structural hypothesis holds between the corresponding FLT exponents. -/
lemma FLT_round_round_div_hyp
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  (Hemin : emin' ≤ emin - prec - 2)
  (Hprec : 2 * prec ≤ prec') :
  round_round_div_hyp (FLT_exp emin prec) (FLT_exp emin' prec') := by
  sorry

/-- Coq: `round_round_div_FLT`
    For FLT with an even radix and the above relations on `emin/prec`,
    nearest-on-nearest double rounding of a quotient collapses at
    `(FLT_exp emin prec)`. -/
theorem round_round_div_FLT
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin' prec')]
  (choice1 choice2 : Int → Bool)
  (Ebeta : ∃ n : Int, beta = 2 * n)
  (Hemin : emin' ≤ emin - prec - 2)
  (Hprec : 2 * prec ≤ prec')
  (x y : ℝ)
  (hy_nz : y ≠ 0)
  (Fx : generic_format beta (FLT_exp emin prec) x)
  (Fy : generic_format beta (FLT_exp emin prec) y) :
  FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FLT_exp emin' prec') (Znearest choice2) (x / y))
  = FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice1) (x / y) := by
  sorry

/-- Coq: `FTZ_round_round_div_hyp`
    Under `emin' + prec' ≤ emin - 1` and `2 * prec ≤ prec'`, the division
    structural hypothesis holds between the corresponding FTZ exponents. -/
lemma FTZ_round_round_div_hyp
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  (Hemin : emin' + prec' ≤ emin - 1)
  (Hprec : 2 * prec ≤ prec') :
  round_round_div_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec') := by
  sorry

/-- Coq: `round_round_div_FTZ`
    For FTZ with an even radix and the above relation, nearest-on-nearest
    double rounding of a quotient collapses at `(FTZ_exp emin prec)`. -/
theorem round_round_div_FTZ
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp emin prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp emin' prec')]
  (choice1 choice2 : Int → Bool)
  (Ebeta : ∃ n : Int, beta = 2 * n)
  (Hemin : emin' + prec' ≤ emin - 1)
  (Hprec : 2 * prec ≤ prec')
  (x y : ℝ)
  (hy_nz : y ≠ 0)
  (Fx : generic_format beta (FTZ_exp emin prec) x)
  (Fy : generic_format beta (FTZ_exp emin prec) y) :
  FloatSpec.Calc.Round.round beta (FTZ_exp emin prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FTZ_exp emin' prec') (Znearest choice2) (x / y))
  = FloatSpec.Calc.Round.round beta (FTZ_exp emin prec) (Znearest choice1) (x / y) := by
  sorry

/-- Coq: `mag_plus_disj`
    For `0 < y ≤ x`, the magnitude of `x + y` is either the same as
    the magnitude of `x` or exactly one greater. -/
lemma mag_plus_disj (x y : ℝ)
  (hy_pos : 0 < y) (hyx : y ≤ x) :
  ((FloatSpec.Core.Raux.mag beta (x + y)) = (FloatSpec.Core.Raux.mag beta x))
  ∨ ((FloatSpec.Core.Raux.mag beta (x + y)) = (FloatSpec.Core.Raux.mag beta x) + 1) := by
  sorry

/-- Coq: `mag_plus_separated`
    If `x` is positive, `y` is nonnegative, `x` is `fexp`-generic and
    `mag y ≤ fexp (mag x)`, then `mag (x + y) = mag x`. -/
lemma mag_plus_separated (fexp : Int → Int)
  (x y : ℝ)
  (hx_pos : 0 < x) (hy_nonneg : 0 ≤ y)
  (Fx : generic_format beta fexp x)
  (Hsep : (FloatSpec.Core.Raux.mag beta y) ≤ fexp ((FloatSpec.Core.Raux.mag beta x))) :
  (FloatSpec.Core.Raux.mag beta (x + y)) = (FloatSpec.Core.Raux.mag beta x) := by
  sorry

/-- Coq: `mag_minus_disj`
    For positive `x` and `y` with `mag y ≤ mag x - 2`, the magnitude of
    `x - y` is either `mag x` or `mag x - 1`. -/
lemma mag_minus_disj (x y : ℝ)
  (hx_pos : 0 < x) (hy_pos : 0 < y)
  (hln : (FloatSpec.Core.Raux.mag beta y) ≤ (FloatSpec.Core.Raux.mag beta x) - 2) :
  ((FloatSpec.Core.Raux.mag beta (x - y)) = (FloatSpec.Core.Raux.mag beta x))
  ∨ ((FloatSpec.Core.Raux.mag beta (x - y)) = (FloatSpec.Core.Raux.mag beta x) - 1) := by
  sorry

/-- Coq: `mag_minus_separated`
    Under separation hypotheses and genericity of `x`, the magnitude of
    `x - y` equals `mag x`. -/
lemma mag_minus_separated (fexp : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
  (x y : ℝ)
  (hx_pos : 0 < x) (hy_pos : 0 < y) (hy_lt_x : y < x)
  (hx_gt_pow : (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x) - 1) < x)
  (Fx : generic_format beta fexp x)
  (Ly : (FloatSpec.Core.Raux.mag beta y) ≤ fexp ((FloatSpec.Core.Raux.mag beta x))) :
  (FloatSpec.Core.Raux.mag beta (x - y)) = (FloatSpec.Core.Raux.mag beta x) := by
  sorry

/-- Coq: `round_round_plus_aux0_aux_aux`
    If `fexp1 (mag x) ≤ fexp1 (mag y)` and the place induced by `fexp2`
    at `mag (x + y)` is below both `fexp1 (mag x)` and `fexp1 (mag y)`,
    then the sum of two `fexp1`-generic numbers is `fexp2`-generic. -/
lemma round_round_plus_aux0_aux_aux
  (fexp1 fexp2 : Int → Int) (x y : ℝ)
  (Hxy : fexp1 ((FloatSpec.Core.Raux.mag beta x)) ≤ fexp1 ((FloatSpec.Core.Raux.mag beta y)))
  (Hlnx : fexp2 ((FloatSpec.Core.Raux.mag beta (x + y))) ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)))
  (Hlny : fexp2 ((FloatSpec.Core.Raux.mag beta (x + y))) ≤ fexp1 ((FloatSpec.Core.Raux.mag beta y)))
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
  generic_format beta fexp2 (x + y) := by
  sorry

/-- Coq: `round_round_plus_aux0_aux`
    Symmetric version using only the two fexp2-bounds at `mag (x + y)`.
    Given `fexp2 (mag (x + y)) ≤ fexp1 (mag x)` and similarly for `y`,
    the sum of two `fexp1`-generic numbers is `fexp2`-generic. -/
lemma round_round_plus_aux0_aux
  (fexp1 fexp2 : Int → Int) (x y : ℝ)
  (Hlnx : fexp2 ((FloatSpec.Core.Raux.mag beta (x + y))) ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)))
  (Hlny : fexp2 ((FloatSpec.Core.Raux.mag beta (x + y))) ≤ fexp1 ((FloatSpec.Core.Raux.mag beta y)))
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
  generic_format beta fexp2 (x + y) := by
  sorry

/-- Coq: `round_round_plus_hyp`
    Structural hypothesis relating `fexp1` and `fexp2` around places
    needed for reasoning on sums. -/
def round_round_plus_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex ey, fexp1 (ex + 1) - 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, fexp1 (ex - 1) + 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, fexp1 ex - 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, ex - 1 ≤ ey → fexp2 ex ≤ fexp1 ey)

/-- Coq: `round_round_plus_aux0`
    Exact-addition case in the largest precision captured by
    `round_round_plus_hyp`. -/
lemma round_round_plus_aux0
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  (Hexp : round_round_plus_hyp fexp1 fexp2)
  (x y : ℝ)
  (hx_pos : 0 < x) (hy_pos : 0 < y) (hyx : y ≤ x)
  (Hln : fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 1 ≤ (FloatSpec.Core.Raux.mag beta y))
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
  generic_format beta fexp2 (x + y) := by
  sorry

/-- Coq: `round_round_plus_aux1_aux`
    With a positive integer `k`, if `mag y ≤ fexp (mag x) - k` and the
    magnitudes of `x` and `x + y` coincide, then the rounding gap for
    `(x + y)` is within `bpow (fexp (mag x) - k)` and positive. -/
lemma round_round_plus_aux1_aux
  (k : Int) (Hk : 0 < k)
  (fexp : Int → Int) [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
  (x y : ℝ)
  (hx_pos : 0 < x) (hy_pos : 0 < y)
  (Hln : (FloatSpec.Core.Raux.mag beta y) ≤ fexp ((FloatSpec.Core.Raux.mag beta x)) - k)
  (Hlxy : (FloatSpec.Core.Raux.mag beta (x + y)) = (FloatSpec.Core.Raux.mag beta x))
  (Fx : generic_format beta fexp x) :
  0 < (x + y) - FloatSpec.Calc.Round.round beta fexp (Znearest (fun _ => false)) (x + y)
    ∧ (x + y) - FloatSpec.Calc.Round.round beta fexp (Znearest (fun _ => false)) (x + y)
      < (beta : ℝ) ^ (fexp ((FloatSpec.Core.Raux.mag beta x)) - k) := by
  sorry

/-- Coq: `round_round_plus_aux1`
    If `0 < x`, `0 < y`, `mag y ≤ fexp1 (mag x) - 2`, and `x` is
    `fexp1`-generic, then rounding `x + y` at `fexp2` then at `fexp1`
    (both to nearest) equals rounding once at `fexp1`. -/
lemma round_round_plus_aux1
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_plus_hyp fexp1 fexp2)
  (x y : ℝ)
  (hx_pos : 0 < x) (hy_pos : 0 < y)
  (Hly : (FloatSpec.Core.Raux.mag beta y) ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 2)
  (Fx : generic_format beta fexp1 x) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x + y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x + y) := by
  sorry

/-- Coq: `round_round_plus_radix_ge_3_hyp`
    Structural hypothesis specialized for the radix-≥3 case used by the
    `round_round_plus_radix_ge_3_*` lemmas. -/
def round_round_plus_radix_ge_3_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex ey, fexp1 (ex + 1) ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, fexp1 (ex - 1) + 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, fexp1 ex ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, ex - 1 ≤ ey → fexp2 ex ≤ fexp1 ey)

/-- Coq: `round_round_plus_radix_ge_3_aux0`
    If `0 < y ≤ x`, `fexp1 (mag x) ≤ mag y`, and both `x` and `y` are
    `fexp1`-generic, then the sum `x + y` is `fexp2`-generic under the
    hypothesis `round_round_plus_radix_ge_3_hyp`. -/
lemma round_round_plus_radix_ge_3_aux0
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  (Hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
  (x y : ℝ)
  (hy_pos : 0 < y) (hyx : y ≤ x)
  (Hln : fexp1 ((FloatSpec.Core.Raux.mag beta x)) ≤ (FloatSpec.Core.Raux.mag beta y))
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
  generic_format beta fexp2 (x + y) := by
  sorry

/-- Coq: `round_round_plus_radix_ge_3_aux1`
    If `0 < x`, `0 < y`, `mag y ≤ fexp1 (mag x) - 1` and both `x` and `y`
    are `fexp1`-generic, then double rounding of `x + y` with nearest is
    innocuous under the radix-≥3 hypothesis. -/
lemma round_round_plus_radix_ge_3_aux1
  (Hbeta : 3 ≤ beta)
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
  (x y : ℝ)
  (hx_pos : 0 < x) (hy_pos : 0 < y)
  (Hly : (FloatSpec.Core.Raux.mag beta y) ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 1)
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x + y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x + y) := by
  sorry

/-- Coq: `round_round_plus_radix_ge_3_aux2`
    Combination of the previous cases: for `0 < y ≤ x` and both `x` and `y`
    `fexp1`-generic, the double rounding of `x + y` is innocuous under the
    radix-≥3 hypothesis. -/
lemma round_round_plus_radix_ge_3_aux2
  (Hbeta : 3 ≤ beta)
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
  (x y : ℝ)
  (hy_pos : 0 < y) (hyx : y ≤ x)
  (Fx : generic_format beta fexp1 x)
  (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x + y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x + y) := by
  sorry

/-- Coq: `FLX_round_round_plus_radix_ge_3_hyp`
    For FLX exponent functions, the radix-≥3 structural hypothesis for
    plus double rounding holds unconditionally. -/
lemma FLX_round_round_plus_radix_ge_3_hyp
  (prec prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  (hprec : 2 * prec ≤ prec') :
  round_round_plus_radix_ge_3_hyp (FLX_exp prec) (FLX_exp prec') := by
  sorry

/-- Coq: `FLT_round_round_plus_radix_ge_3_hyp`
    For FLT exponent functions, under `emin' ≤ emin` and `2*prec ≤ prec'`,
    the radix-≥3 structural hypothesis for plus double rounding holds. -/
lemma FLT_round_round_plus_radix_ge_3_hyp
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  (Hemin : emin' ≤ emin) (Hprec : 2 * prec ≤ prec') :
  round_round_plus_radix_ge_3_hyp (FLT_exp emin prec) (FLT_exp emin' prec') := by
  sorry

/-- Coq: `FTZ_round_round_plus_radix_ge_3_hyp`
    For FTZ exponent functions, under `emin' + prec' ≤ emin + 1` and
    `2*prec ≤ prec'`, the radix-≥3 structural hypothesis holds. -/
lemma FTZ_round_round_plus_radix_ge_3_hyp
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  (Hemin : emin' + prec' ≤ emin + 1) (Hprec : 2 * prec ≤ prec') :
  round_round_plus_radix_ge_3_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec') := by
  sorry

/-- Coq: `round_round_plus_radix_ge_3_FLX`
    Under `3 ≤ beta` and `2 * prec ≤ prec'`, nearest-on-nearest
    double rounding of `x + y` from `(FLX_exp prec')` to `(FLX_exp prec)`
    collapses to a single rounding at `(FLX_exp prec)`. -/
theorem round_round_plus_radix_ge_3_FLX
  (prec prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec')]
  (choice1 choice2 : Int → Bool)
  (Hbeta : 3 ≤ beta)
  (hprec : 2 * prec ≤ prec')
  (x y : ℝ)
  (Fx : generic_format beta (FLX_exp prec) x)
  (Fy : generic_format beta (FLX_exp prec) y) :
  FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FLX_exp prec') (Znearest choice2) (x + y))
  = FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice1) (x + y) := by
  sorry

/-- Coq: `round_round_minus_radix_ge_3_FLX`
    Under `3 ≤ beta` and `2 * prec ≤ prec'`, nearest-on-nearest double
    rounding of `x - y` from `(FLX_exp prec')` to `(FLX_exp prec)`
    collapses to a single rounding at `(FLX_exp prec)`. -/
theorem round_round_minus_radix_ge_3_FLX
  (prec prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec')]
  (choice1 choice2 : Int → Bool)
  (Hbeta : 3 ≤ beta)
  (hprec : 2 * prec ≤ prec')
  (x y : ℝ)
  (Fx : generic_format beta (FLX_exp prec) x)
  (Fy : generic_format beta (FLX_exp prec) y) :
  FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FLX_exp prec') (Znearest choice2) (x - y))
  = FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice1) (x - y) := by
  sorry

/-- Coq: `round_round_plus_radix_ge_3_FLT`
    Under `3 ≤ beta`, `emin' ≤ emin` and `2 * prec ≤ prec'`, nearest-on-
    nearest double rounding of `x + y` from `(FLT_exp emin' prec')` to
    `(FLT_exp emin prec)` collapses to a single rounding at
    `(FLT_exp emin prec)`. -/
theorem round_round_plus_radix_ge_3_FLT
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin' prec')]
  (choice1 choice2 : Int → Bool)
  (Hbeta : 3 ≤ beta)
  (Hemin : emin' ≤ emin) (Hprec : 2 * prec ≤ prec')
  (x y : ℝ)
  (Fx : generic_format beta (FLT_exp emin prec) x)
  (Fy : generic_format beta (FLT_exp emin prec) y) :
  FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FLT_exp emin' prec') (Znearest choice2) (x + y))
  = FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice1) (x + y) := by
  sorry

/-- Coq: `round_round_minus_radix_ge_3_FLT`
    Under `3 ≤ beta`, `emin' ≤ emin` and `2 * prec ≤ prec'`, nearest-on-
    nearest double rounding of `x - y` from `(FLT_exp emin' prec')` to
    `(FLT_exp emin prec)` collapses to a single rounding at
    `(FLT_exp emin prec)`. -/
theorem round_round_minus_radix_ge_3_FLT
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin' prec')]
  (choice1 choice2 : Int → Bool)
  (Hbeta : 3 ≤ beta)
  (Hemin : emin' ≤ emin) (Hprec : 2 * prec ≤ prec')
  (x y : ℝ)
  (Fx : generic_format beta (FLT_exp emin prec) x)
  (Fy : generic_format beta (FLT_exp emin prec) y) :
  FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FLT_exp emin' prec') (Znearest choice2) (x - y))
  = FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice1) (x - y) := by
  sorry

/-- Coq: `round_round_plus_radix_ge_3_FTZ`
    Under `3 ≤ beta`, `emin' + prec' ≤ emin + 1` and `2 * prec ≤ prec'`,
    nearest-on-nearest double rounding of `x + y` from
    `(FTZ_exp emin' prec')` to `(FTZ_exp emin prec)` collapses to a
    single rounding at `(FTZ_exp emin prec)`. -/
theorem round_round_plus_radix_ge_3_FTZ
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp emin prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp emin' prec')]
  (choice1 choice2 : Int → Bool)
  (Hbeta : 3 ≤ beta)
  (Hemin : emin' + prec' ≤ emin + 1) (Hprec : 2 * prec ≤ prec')
  (x y : ℝ)
  (Fx : generic_format beta (FTZ_exp emin prec) x)
  (Fy : generic_format beta (FTZ_exp emin prec) y) :
  FloatSpec.Calc.Round.round beta (FTZ_exp emin prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FTZ_exp emin' prec') (Znearest choice2) (x + y))
  = FloatSpec.Calc.Round.round beta (FTZ_exp emin prec) (Znearest choice1) (x + y) := by
  sorry

/-- Coq: `round_round_minus_radix_ge_3_FTZ`
    Under `3 ≤ beta`, `emin' + prec' ≤ emin + 1` and `2 * prec ≤ prec'`,
    nearest-on-nearest double rounding of `x - y` from
    `(FTZ_exp emin' prec')` to `(FTZ_exp emin prec)` collapses to a
    single rounding at `(FTZ_exp emin prec)`. -/
theorem round_round_minus_radix_ge_3_FTZ
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp emin prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp emin' prec')]
  (choice1 choice2 : Int → Bool)
  (Hbeta : 3 ≤ beta)
  (Hemin : emin' + prec' ≤ emin + 1) (Hprec : 2 * prec ≤ prec')
  (x y : ℝ)
  (Fx : generic_format beta (FTZ_exp emin prec) x)
  (Fy : generic_format beta (FTZ_exp emin prec) y) :
  FloatSpec.Calc.Round.round beta (FTZ_exp emin prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FTZ_exp emin' prec') (Znearest choice2) (x - y))
  = FloatSpec.Calc.Round.round beta (FTZ_exp emin prec) (Znearest choice1) (x - y) := by
  sorry

/-- Coq: `round_round_plus_radix_ge_3_aux`
    Nonnegative case: if `0 ≤ x`, `0 ≤ y`, and both are `fexp1`-generic,
    then under `round_round_plus_radix_ge_3_hyp` the double rounding of
    `x + y` is innocuous. -/
lemma round_round_plus_radix_ge_3_aux
  (Hbeta : 3 ≤ beta)
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
  (x y : ℝ)
  (hx_nonneg : 0 ≤ x) (hy_nonneg : 0 ≤ y)
  (Fx : generic_format beta fexp1 x)
  (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x + y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x + y) := by
  sorry

/-- Coq: `round_round_plus_radix_ge_3`
    Full sign-split theorem: for arbitrary `x` and `y` that are
    `fexp1`-generic, under the radix-≥3 hypothesis and
    `round_round_plus_radix_ge_3_hyp`, double rounding of `x + y` is
    innocuous. -/
lemma round_round_plus_radix_ge_3
  (Hbeta : 3 ≤ beta)
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
  (x y : ℝ)
  (Fx : generic_format beta fexp1 x)
  (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x + y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x + y) := by
  sorry

/-- Coq: `round_round_minus_radix_ge_3_aux0`
    If `0 < y < x`, `fexp1 (mag x) ≤ mag y`, and both `x` and `y` are
    `fexp1`-generic, then the subtraction `x - y` is `fexp2`-generic
    under the hypothesis `round_round_plus_radix_ge_3_hyp`. -/
lemma round_round_minus_radix_ge_3_aux0
  (fexp1 fexp2 : Int → Int)
  (Hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
  (x y : ℝ)
  (hy_pos : 0 < y) (hyx : y < x)
  (Hln : fexp1 ((FloatSpec.Core.Raux.mag beta x)) ≤ (FloatSpec.Core.Raux.mag beta y))
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
  generic_format beta fexp2 (x - y) := by
  sorry

/-- Coq: `round_round_minus_radix_ge_3_aux1`
    If `0 < y < x`, `mag y ≤ fexp1 (mag x) - 1`, and
    `fexp1 (mag (x - y)) ≤ mag y`, then under
    `round_round_plus_radix_ge_3_hyp` the subtraction `x - y` is
    `fexp2`-generic. -/
lemma round_round_minus_radix_ge_3_aux1
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (Hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
  (x y : ℝ)
  (hy_pos : 0 < y) (hyx : y < x)
  (Hly : (FloatSpec.Core.Raux.mag beta y) ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 1)
  (Hln' : fexp1 ((FloatSpec.Core.Raux.mag beta (x - y))) ≤ (FloatSpec.Core.Raux.mag beta y))
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
  generic_format beta fexp2 (x - y) := by
  sorry

/-- Coq: `round_round_minus_radix_ge_3_aux2`
    If `0 < y < x`, `mag y ≤ fexp1 (mag x) - 1` and also
    `mag y ≤ fexp1 (mag (x - y)) - 1`, then nearest-on-nearest double
    rounding of `x - y` collapses to a single rounding at `fexp1` under
    the radix-≥3 hypothesis. -/
lemma round_round_minus_radix_ge_3_aux2
  (Hbeta : 3 ≤ beta)
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
  (x y : ℝ)
  (hy_pos : 0 < y) (hyx : y < x)
  (Hly : (FloatSpec.Core.Raux.mag beta y) ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 1)
  (Hly' : (FloatSpec.Core.Raux.mag beta y) ≤ fexp1 ((FloatSpec.Core.Raux.mag beta (x - y))) - 1)
  (Fx : generic_format beta fexp1 x)
  (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x - y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x - y) := by
  sorry

/-- Coq: `round_round_minus_radix_ge_3_aux3`
    Combination lemma for the subtraction case under radix-≥3: for
    `0 < y ≤ x` with both operands `fexp1`-generic, nearest-on-nearest
    double rounding of `x - y` collapses to a single rounding at `fexp1`. -/
lemma round_round_minus_radix_ge_3_aux3
  (Hbeta : 3 ≤ beta)
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
  (x y : ℝ)
  (hy_pos : 0 < y) (hyx : y ≤ x)
  (Fx : generic_format beta fexp1 x)
  (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x - y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x - y) := by
  sorry

/-- Coq: `round_round_minus_radix_ge_3_aux`
    Nonnegative inputs version for differences: for `0 ≤ x` and `0 ≤ y`,
    under the hypothesis `round_round_plus_radix_ge_3_hyp`, nearest-on-
    nearest double rounding of `x - y` collapses to a single rounding at
    `fexp1`. -/
lemma round_round_minus_radix_ge_3_aux
  (Hbeta : 3 ≤ beta)
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
  (x y : ℝ)
  (hx_nonneg : 0 ≤ x) (hy_nonneg : 0 ≤ y)
  (Fx : generic_format beta fexp1 x)
  (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x - y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x - y) := by
  sorry

/-- Coq: `round_round_minus_radix_ge_3`
    Full sign-split theorem for subtraction: for arbitrary `x` and `y`
    that are `fexp1`-generic, under the radix-≥3 hypothesis and
    `round_round_plus_radix_ge_3_hyp`, double rounding of `x - y` is
    innocuous. -/
lemma round_round_minus_radix_ge_3
  (Hbeta : 3 ≤ beta)
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
  (x y : ℝ)
  (Fx : generic_format beta fexp1 x)
  (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x - y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x - y) := by
  sorry

/-- Coq: `round_round_plus_aux2`
    Case split on `mag y ≤ fexp1 (mag x) - 2` driving either the
    `round_round_plus_aux1` branch or the exact-addition branch
    `round_round_plus_aux0`. -/
lemma round_round_plus_aux2
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_plus_hyp fexp1 fexp2)
  (x y : ℝ)
  (hx_pos : 0 < x) (hy_pos : 0 < y) (hyx : y ≤ x)
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x + y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x + y) := by
  sorry

/-- Coq: `round_round_plus_aux`
    Nonnegative inputs version: for `0 ≤ x` and `0 ≤ y`, under the
    structural hypothesis `round_round_plus_hyp`, double rounding of
    `x + y` (nearest-on-nearest) collapses to a single rounding at
    `fexp1`. -/
lemma round_round_plus_aux
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_plus_hyp fexp1 fexp2)
  (x y : ℝ)
  (hx_nonneg : 0 ≤ x) (hy_nonneg : 0 ≤ y)
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x + y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x + y) := by
  sorry

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
  (h_place : fexp2 ((FloatSpec.Core.Raux.mag beta x))
              ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 1)
  (hx1 : FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x
            < (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x)))
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
  (h_place : fexp2 ((FloatSpec.Core.Raux.mag beta x))
              ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 1)
  (h_f1_le_mag : fexp1 ((FloatSpec.Core.Raux.mag beta x))
                ≤ (FloatSpec.Core.Raux.mag beta x))
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
  (h_same : fexp2 ((FloatSpec.Core.Raux.mag beta x))
              = fexp1 ((FloatSpec.Core.Raux.mag beta x)))
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
  (h_place_le : fexp2 ((FloatSpec.Core.Raux.mag beta x))
                ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)))
  (h_f1_le_mag : fexp1 ((FloatSpec.Core.Raux.mag beta x))
                ≤ (FloatSpec.Core.Raux.mag beta x))
  (hx_gt_mid : midp' (beta := beta) fexp1 x < x)
  (hx_cond : (fexp2 ((FloatSpec.Core.Raux.mag beta x))
                ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 1)
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

/-- Coq: `round_round_minus_aux0_aux`
    If the place induced by `fexp2` at `mag (x - y)` is below both
    `fexp1 (mag x)` and `fexp1 (mag y)`, then the difference of two
    `fexp1`-generic numbers is `fexp2`-generic. -/
lemma round_round_minus_aux0_aux
  (fexp1 fexp2 : Int → Int)
  (x y : ℝ)
  (Hlnx : fexp2 ((FloatSpec.Core.Raux.mag beta (x - y))) ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)))
  (Hlny : fexp2 ((FloatSpec.Core.Raux.mag beta (x - y))) ≤ fexp1 ((FloatSpec.Core.Raux.mag beta y)))
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
  generic_format beta fexp2 (x - y) := by
  sorry

/-- Coq: `round_round_minus_aux0`
    Exact-subtraction case in the largest precision captured by
    `round_round_plus_hyp`. -/
lemma round_round_minus_aux0
  (fexp1 fexp2 : Int → Int)
  (Hexp : round_round_plus_hyp fexp1 fexp2)
  (x y : ℝ)
  (hy_pos : 0 < y) (hyx : y < x)
  (Hln : fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 1 ≤ (FloatSpec.Core.Raux.mag beta y))
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
  generic_format beta fexp2 (x - y) := by
  sorry

/-- Coq: `round_round_minus_aux1`
    Under `mag y ≤ fexp1 (mag x) - 2` and a bound relating
    `fexp1 (mag (x - y))` and `mag y`, subtraction is exact in the
    largest precision. -/
lemma round_round_minus_aux1
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (Hexp : round_round_plus_hyp fexp1 fexp2)
  (x y : ℝ)
  (hy_pos : 0 < y) (hyx : y < x)
  (Hly : (FloatSpec.Core.Raux.mag beta y) ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 2)
  (Hln' : fexp1 ((FloatSpec.Core.Raux.mag beta (x - y))) - 1 ≤ (FloatSpec.Core.Raux.mag beta y))
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
  generic_format beta fexp2 (x - y) := by
  sorry

/-- Coq: `round_round_minus_aux2_aux`
    Auxiliary bound: for `0 < y < x`, with `mag y ≤ fexp (mag x) - 1` and
    both `x` and `y` being `fexp`-generic, the rounding gap of `x - y`
    under an upward rounding (mode placeholder) is at most `y`. -/
lemma round_round_minus_aux2_aux
  (fexp : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
  (x y : ℝ)
  (hy_pos : 0 < y) (hyx : y < x)
  (Hly : (FloatSpec.Core.Raux.mag beta y) ≤ fexp ((FloatSpec.Core.Raux.mag beta x)) - 1)
  (Fx : generic_format beta fexp x)
  (Fy : generic_format beta fexp y) :
  FloatSpec.Calc.Round.round beta fexp (Znearest (fun _ => false)) (x - y) - (x - y) ≤ y := by
  sorry

/-- Coq: `round_round_minus_aux2`
    If `0 < y < x`, `mag y ≤ fexp1 (mag x) - 2` and also
    `mag y ≤ fexp1 (mag (x - y)) - 2`, then nearest-on-nearest double
    rounding of `x - y` collapses to a single rounding at `fexp1`. -/
lemma round_round_minus_aux2
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_plus_hyp fexp1 fexp2)
  (x y : ℝ)
  (hy_pos : 0 < y) (hyx : y < x)
  (Hly : (FloatSpec.Core.Raux.mag beta y) ≤ fexp1 ((FloatSpec.Core.Raux.mag beta x)) - 2)
  (Hly' : (FloatSpec.Core.Raux.mag beta y) ≤ fexp1 ((FloatSpec.Core.Raux.mag beta (x - y))) - 2)
  (Fx : generic_format beta fexp1 x)
  (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x - y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x - y) := by
  sorry

/-- Coq: `round_round_minus_aux3`
    Case distinction combining `round_round_minus_aux{0,1,2}`. -/
lemma round_round_minus_aux3
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_plus_hyp fexp1 fexp2)
  (x y : ℝ)
  (hy_pos : 0 < y) (hyx : y ≤ x)
  (Fx : generic_format beta fexp1 x)
  (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x - y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x - y) := by
  sorry

/-- Coq: `round_round_minus_aux`
    Nonnegative inputs version for differences: for `0 ≤ x` and `0 ≤ y`,
    under the structural hypothesis `round_round_plus_hyp`, nearest-on-
    nearest double rounding of `x - y` collapses to a single rounding
    at `fexp1`. -/
lemma round_round_minus_aux
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_plus_hyp fexp1 fexp2)
  (x y : ℝ)
  (hx_nonneg : 0 ≤ x) (hy_nonneg : 0 ≤ y)
  (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x - y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x - y) := by
  sorry

/-- Coq: `round_round_plus`
    General double-rounding property for sums under the structural
    hypothesis `round_round_plus_hyp`. No sign constraints; this is the
    sign-split consolidation of the `aux` lemmas. -/
lemma round_round_plus'
  (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool)
  (Hexp : round_round_plus_hyp fexp1 fexp2)
  (x y : ℝ)
  (Fx : generic_format beta fexp1 x)
  (Fy : generic_format beta fexp1 y) :
  FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1)
    (FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (x + y))
  = FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) (x + y) := by
  sorry


/-- Coq: `FLX_round_round_plus_hyp`
    Under the precision relation `2 * prec + 1 ≤ prec'`, the structural
    hypothesis `round_round_plus_hyp (FLX_exp prec) (FLX_exp prec')` holds. -/
lemma FLX_round_round_plus_hyp
  (prec prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  (hprec : 2 * prec + 1 ≤ prec') :
  round_round_plus_hyp (FLX_exp prec) (FLX_exp prec') := by
  sorry

/-- Coq: `round_round_plus_FLX`
    Under `2 * prec + 1 ≤ prec'`, nearest-on-nearest double rounding of
    a sum collapses from `(FLX prec')` then `(FLX prec)` to a single
    rounding at `(FLX prec)`. -/
theorem round_round_plus_FLX
  (prec prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec')]
  (choice1 choice2 : Int → Bool)
  (hprec : 2 * prec + 1 ≤ prec')
  (x y : ℝ)
  (Fx : generic_format beta (FLX_exp prec) x)
  (Fy : generic_format beta (FLX_exp prec) y) :
  FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FLX_exp prec') (Znearest choice2) (x + y))
  = FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice1) (x + y) := by
  sorry

/-- Coq: `round_round_minus_FLX`
    FLX difference version under `2 * prec + 1 ≤ prec'`. -/
theorem round_round_minus_FLX
  (prec prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec')]
  (choice1 choice2 : Int → Bool)
  (hprec : 2 * prec + 1 ≤ prec')
  (x y : ℝ)
  (Fx : generic_format beta (FLX_exp prec) x)
  (Fy : generic_format beta (FLX_exp prec) y) :
  FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FLX_exp prec') (Znearest choice2) (x - y))
  = FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice1) (x - y) := by
  sorry

/-- Coq: `FLT_round_round_plus_hyp`
    Under `(emin' ≤ emin)` and `2 * prec + 1 ≤ prec'`, the structural
    hypothesis holds between the corresponding FLT exponent functions. -/
lemma FLT_round_round_plus_hyp
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  (Hemin : emin' ≤ emin) (Hprec : 2 * prec + 1 ≤ prec') :
  round_round_plus_hyp (FLT_exp emin prec) (FLT_exp emin' prec') := by
  sorry

/-- Coq: `round_round_plus_FLT`
    FLT sum version under `(emin' ≤ emin)` and `2 * prec + 1 ≤ prec'`. -/
theorem round_round_plus_FLT
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin' prec')]
  (choice1 choice2 : Int → Bool)
  (Hemin : emin' ≤ emin) (Hprec : 2 * prec + 1 ≤ prec')
  (x y : ℝ)
  (Fx : generic_format beta (FLT_exp emin prec) x)
  (Fy : generic_format beta (FLT_exp emin prec) y) :
  FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FLT_exp emin' prec') (Znearest choice2) (x + y))
  = FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice1) (x + y) := by
  sorry

/-- Coq: `round_round_minus_FLT`
    FLT difference version under `(emin' ≤ emin)` and `2 * prec + 1 ≤ prec'`. -/
theorem round_round_minus_FLT
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin' prec')]
  (choice1 choice2 : Int → Bool)
  (Hemin : emin' ≤ emin) (Hprec : 2 * prec + 1 ≤ prec')
  (x y : ℝ)
  (Fx : generic_format beta (FLT_exp emin prec) x)
  (Fy : generic_format beta (FLT_exp emin prec) y) :
  FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FLT_exp emin' prec') (Znearest choice2) (x - y))
  = FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice1) (x - y) := by
  sorry

/-- Coq: `FTZ_round_round_plus_hyp`
    Under `(emin' + prec' ≤ emin + 1)` and `2 * prec + 1 ≤ prec'`, the
    structural hypothesis holds between the corresponding FTZ exponent
    functions. -/
lemma FTZ_round_round_plus_hyp
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  (Hemin : emin' + prec' ≤ emin + 1) (Hprec : 2 * prec + 1 ≤ prec') :
  round_round_plus_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec') := by
  sorry

/-- Coq: `round_round_plus_FTZ`
    FTZ sum version under `(emin' + prec' ≤ emin + 1)` and
    `2 * prec + 1 ≤ prec'`. -/
theorem round_round_plus_FTZ
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp emin prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp emin' prec')]
  (choice1 choice2 : Int → Bool)
  (Hemin : emin' + prec' ≤ emin + 1) (Hprec : 2 * prec + 1 ≤ prec')
  (x y : ℝ)
  (Fx : generic_format beta (FTZ_exp emin prec) x)
  (Fy : generic_format beta (FTZ_exp emin prec) y) :
  FloatSpec.Calc.Round.round beta (FTZ_exp emin prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FTZ_exp emin' prec') (Znearest choice2) (x + y))
  = FloatSpec.Calc.Round.round beta (FTZ_exp emin prec) (Znearest choice1) (x + y) := by
  sorry

/-- Coq: `round_round_minus_FTZ`
    FTZ difference version under `(emin' + prec' ≤ emin + 1)` and
    `2 * prec + 1 ≤ prec'`. -/
theorem round_round_minus_FTZ
  (emin prec emin' prec' : Int)
  [Prec_gt_0 prec] [Prec_gt_0 prec']
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp emin prec)]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp emin' prec')]
  (choice1 choice2 : Int → Bool)
  (Hemin : emin' + prec' ≤ emin + 1) (Hprec : 2 * prec + 1 ≤ prec')
  (x y : ℝ)
  (Fx : generic_format beta (FTZ_exp emin prec) x)
  (Fy : generic_format beta (FTZ_exp emin prec) y) :
  FloatSpec.Calc.Round.round beta (FTZ_exp emin prec) (Znearest choice1)
    (FloatSpec.Calc.Round.round beta (FTZ_exp emin' prec') (Znearest choice2) (x - y))
  = FloatSpec.Calc.Round.round beta (FTZ_exp emin prec) (Znearest choice1) (x - y) := by
  sorry
