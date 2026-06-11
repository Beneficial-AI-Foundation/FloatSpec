import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import Mathlib.Data.Real.Basic

/-!
Tier 1 Scaffold / Tier 3 Excluded.

This property-analysis leaf keeps the concrete helper definitions from the
translated Flocq double-rounding development. The former theorem shells in this
file were not re-exported by `FloatSpec.src.Prop`, were not referenced by other
modules, and still required the larger Flocq proof context, so they have been
removed instead of retained as unproved compatibility declarations.
-/

-- Double rounding properties
-- Translated from Coq file: flocq/src/Prop/Double_rounding.v

variable (beta : Int)

/-! Midpoint helpers, corresponding to Coq's `midp` and `midp'`. -/

noncomputable def midp (fexp : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp] (x : ℝ) : ℝ :=
  FloatSpec.Calc.Round.round beta fexp (Znearest (fun _ => false)) x
    + (1 / 2) * ulp beta fexp x

noncomputable def midp' (fexp : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp] (x : ℝ) : ℝ :=
  FloatSpec.Calc.Round.round beta fexp (Znearest (fun _ => false)) x
    - (1 / 2) * ulp beta fexp x

/-! Structural hypotheses used by the omitted Flocq double-rounding lemmas. -/

/-- Coq: `round_round_mult_hyp`. -/
def round_round_mult_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex ey, fexp2 (ex + ey) ≤ fexp1 ex + fexp1 ey) ∧
  (∀ ex ey, fexp2 (ex + ey - 1) ≤ fexp1 ex + fexp1 ey)

/-- Coq: `round_round_sqrt_hyp`. -/
def round_round_sqrt_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex)) ∧
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex - 1)) ∧
  (∀ ex, fexp1 (2 * ex) < 2 * ex → fexp2 ex + ex ≤ 2 * fexp1 ex - 2)

/-- Coq: `round_round_sqrt_radix_ge_4_hyp`. -/
def round_round_sqrt_radix_ge_4_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex)) ∧
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex - 1)) ∧
  (∀ ex, fexp1 (2 * ex) < 2 * ex → fexp2 ex + ex ≤ 2 * fexp1 ex - 1)

/-- Coq: `round_round_div_hyp`. -/
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

/-- Coq: `round_round_plus_hyp`. -/
def round_round_plus_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex ey, fexp1 (ex + 1) - 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, fexp1 (ex - 1) + 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, fexp1 ex - 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, ex - 1 ≤ ey → fexp2 ex ≤ fexp1 ey)

/-- Coq: `round_round_plus_radix_ge_3_hyp`. -/
def round_round_plus_radix_ge_3_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex ey, fexp1 (ex + 1) ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, fexp1 (ex - 1) + 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, fexp1 ex ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, ex - 1 ≤ ey → fexp2 ex ≤ fexp1 ey)
