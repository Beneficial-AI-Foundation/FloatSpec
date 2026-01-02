-- Round to odd properties
-- Translated from Coq file: flocq/src/Prop/Round_odd.v

import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import Mathlib.Data.Real.Basic

open Real
open FloatSpec.Calc.Round

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

/-- Rnd_odd_pt: pointwise specification of round-to-odd witness

    Mirrors Coq's `Rnd_odd_pt` predicate: `f` is in format and either
    equals `x`, or it is a DN/UP witness and corresponds to a canonical
    float with an odd mantissa. -/
def Rnd_odd_pt (x f : ℝ) : Prop :=
  generic_format beta fexp f ∧
  (f = x ∨
    ((FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x f ∨
      FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x f) ∧
     ∃ g : FloatSpec.Core.Defs.FlocqFloat beta,
       f = (FloatSpec.Core.Defs.F2R g) ∧
       FloatSpec.Core.Generic_fmt.canonical beta fexp g ∧
       g.Fnum % 2 ≠ 0))

/-- Round to odd rounding mode -/
noncomputable def Zodd : ℝ → Int := fun x =>
  let n := Ztrunc x
  if n % 2 = 0 then
    if x = (n : ℝ) then n else n + 1
  else n

/-- Round to odd is a valid rounding -/
instance : Valid_rnd (Zodd) := by sorry

/-- If `x` is not exactly an integer (`Zfloor x`), then the result of
    rounding-to-odd (`Zodd x`) is odd. This mirrors Coq's `Zrnd_odd_Zodd`. -/
lemma Zrnd_odd_Zodd (x : ℝ)
  (hx : x ≠ (((FloatSpec.Core.Raux.Zfloor x) : Int) : ℝ)) :
  (Zodd x) % 2 = 1 := by
  sorry

/-- Integer floor of a translated real: `Zfloor (n + y) = n + Zfloor y`. -/
lemma Zfloor_plus (n : Int) (y : ℝ) :
  (FloatSpec.Core.Raux.Zfloor ((n : ℝ) + y)) =
    n + (FloatSpec.Core.Raux.Zfloor y) := by
  sorry

/-- Integer ceil of a translated real: `Zceil (n + y) = n + Zceil y`. -/
lemma Zceil_plus (n : Int) (y : ℝ) :
  (FloatSpec.Core.Raux.Zceil ((n : ℝ) + y)) =
    n + (FloatSpec.Core.Raux.Zceil y) := by
  sorry

/-- Parity is invariant by absolute value: `(abs z)` is even iff `z` is even.
    Coq counterpart: `Zeven_abs`. -/
lemma Zeven_abs (z : Int) :
  ((Int.ofNat (Int.natAbs z)) % 2 = 0) ↔ (z % 2 = 0) := by
  sorry

/-- Sum with round-to-odd at an even integer point.
    Coq counterpart: `Zrnd_odd_plus`. -/
lemma Zrnd_odd_plus (x y : ℝ)
  (hx : x = (((FloatSpec.Core.Raux.Zfloor x) : Int) : ℝ))
  (heven : ((FloatSpec.Core.Raux.Zfloor x) : Int) % 2 = 0) :
  ((Zodd (x + y) : Int) : ℝ) = x + ((Zodd y : Int) : ℝ) := by
  sorry

/-- Negation invariance for the `Rnd_odd_pt` predicate.
    Coq counterpart: `Rnd_odd_pt_opp_inv`. -/
theorem Rnd_odd_pt_opp_inv (x f : ℝ) :
  Rnd_odd_pt (beta := beta) (fexp := fexp) (-x) (-f) →
  Rnd_odd_pt (beta := beta) (fexp := fexp) x f := by
  sorry

/-- Negation commutes with round-to-odd (mode `()` in this file).
    Coq counterpart: `round_odd_opp`. -/
theorem round_odd_opp (x : ℝ) :
  FloatSpec.Calc.Round.round beta fexp () (-x)
  = - FloatSpec.Calc.Round.round beta fexp () x := by
  sorry

/-- Pointwise round-to-odd witness for `round beta fexp () x`.
    Coq counterpart: `round_odd_pt`. -/
theorem round_odd_pt (x : ℝ) :
  Rnd_odd_pt (beta := beta) (fexp := fexp) x (FloatSpec.Calc.Round.round beta fexp () x) := by
  sorry

/-- Uniqueness of the round-to-odd witness.
    Coq counterpart: `Rnd_odd_pt_unique`. -/
theorem Rnd_odd_pt_unique (x f1 f2 : ℝ) :
  Rnd_odd_pt (beta := beta) (fexp := fexp) x f1 →
  Rnd_odd_pt (beta := beta) (fexp := fexp) x f2 →
  f1 = f2 := by
  sorry

/-- Monotonicity of the round-to-odd predicate.
    Coq counterpart: `Rnd_odd_pt_monotone`. -/
theorem Rnd_odd_pt_monotone :
  FloatSpec.Core.Defs.round_pred_monotone (Rnd_odd_pt (beta := beta) (fexp := fexp)) := by
  sorry

/-- Round to odd properties -/
theorem round_odd_ge_ulp (x : ℝ) :
  generic_format beta fexp x ∨
  ulp beta fexp x ≤ |FloatSpec.Calc.Round.round beta fexp () x - x| := by
  sorry

/-- Round to odd for double rounding -/
theorem round_odd_double_round (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice : Int → Bool) (x : ℝ)
  (h_precision : ∀ e, fexp2 e ≤ fexp1 e) :
  FloatSpec.Calc.Round.round beta fexp2 (Znearest choice) (FloatSpec.Calc.Round.round beta fexp1 () x) =
  FloatSpec.Calc.Round.round beta fexp2 (Znearest choice) x := by
  sorry

/-- Round to odd maintains format when appropriate -/
theorem generic_format_round_odd (x : ℝ) :
  generic_format beta fexp (FloatSpec.Calc.Round.round beta fexp () x) := by
  sorry

/-- Magnitude after round-to-odd is controlled. Coq: `mag_round_odd`. -/
theorem mag_round_odd (x : ℝ) :
  (FloatSpec.Core.Raux.mag beta (FloatSpec.Calc.Round.round beta fexp () x))
    ≤ (FloatSpec.Core.Raux.mag beta x) + 1 := by
  sorry

/-- Exponent after round-to-odd is within one place. Coq: `fexp_round_odd`. -/
theorem fexp_round_odd (x : ℝ) :
  fexp ((FloatSpec.Core.Raux.mag beta (FloatSpec.Calc.Round.round beta fexp () x)))
    ≤ (FloatSpec.Core.Raux.mag beta x) + 1 := by
  sorry


variable (fexpe : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexpe]

/-- If the auxiliary exponent `fexpe` is pointwise below `fexp - 2`,
    then any `fexp`-generic number is also `fexpe`-generic.
    Coq counterpart: `generic_format_fexpe_fexp`. -/
lemma generic_format_fexpe_fexp
  (hrel : ∀ e, fexpe e ≤ fexp e - 2)
  (x : ℝ) :
  generic_format beta fexp x → generic_format beta fexpe x := by
  intro _
  sorry

/-- Zodd summation at even-base aligned points.
    Coq counterpart: `Zrnd_odd_plus'`.

    If `beta` is even and `x` sits exactly on a radix grid point
    `n * beta^e` with `1 ≤ e`, then rounding-to-odd satisfies
    `Zodd (x + y) = x + Zodd y` (as integers mapped to reals).
    We mirror the Coq statement and leave the proof as a placeholder. -/
theorem Zrnd_odd_plus' (Ebeta : ∃ n : Int, beta = 2 * n)
  (x y : ℝ)
  (hx : ∃ n e : Int, x = (n : ℝ) * (beta : ℝ) ^ e ∧ 1 ≤ e) :
  ((Zodd (x + y) : Int) : ℝ) = x + ((Zodd y : Int) : ℝ) := by
  sorry

/-- Existence of an even-exponent canonical representative larger than a bound.
    Coq counterpart: `exists_even_fexp_lt`.
    We pose it over an abstract exponent function `c` mirroring the Coq version. -/
lemma exists_even_fexp_lt
  (c : Int → Int) (x : ℝ)
  (hx : ∃ g : FloatSpec.Core.Defs.FlocqFloat beta,
            (FloatSpec.Core.Defs.F2R g) = x ∧ c ((FloatSpec.Core.Raux.mag beta x)) < g.Fexp) :
  ∃ g : FloatSpec.Core.Defs.FlocqFloat beta,
    (FloatSpec.Core.Defs.F2R g) = x ∧
    FloatSpec.Core.Generic_fmt.canonical beta c g ∧
    g.Fnum % 2 = 0 := by
  sorry

/-
  Additional Coq lemmas (`DN_odd_d_aux`, `UP_odd_d_aux`, `round_N_odd_pos`, `round_N_odd`)
  are not imported yet. They depend on a larger internal development
  around witnesses d,u,m and will be introduced with that context.
-/

/-!
  Coq Section Fcore_rnd_odd: auxiliary witnesses d, u, and midpoint m.
  We introduce the missing lemmas by mirroring the Coq statements and
  leave proofs as placeholders. These lemmas assume DN/UP witnesses `d` and `u`.
-/

/-- Coq: `d_eq`
    Equality between the DN-witness value and rounding with `Zfloor`.
    Mirrors: `F2R d = round beta fexp Zfloor x`.

    We state it over Core’s `roundR` with the concrete rounding function `Zfloor`.
-/
lemma d_eq (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) :
  F2R d =
    (FloatSpec.Core.Generic_fmt.roundR (beta := beta) (fexp := fexp)
        (fun y => (FloatSpec.Core.Raux.Zfloor y)) x) := by
  sorry

/-- Coq: `u_eq`
    Equality between the UP-witness value and rounding with `Zceil`.

    Mirrors: `F2R u = round beta fexp Zceil x`. We use the Core `roundR`
    helper with the integer rounding function `Zceil` (as `Int` via `.run`). -/
lemma u_eq (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) :
  F2R u =
    (FloatSpec.Core.Generic_fmt.roundR (beta := beta) (fexp := fexp)
        (fun y => (FloatSpec.Core.Raux.Zceil y)) x) := by
  sorry

/-- Coq: `d_ge_0`
    From the DN-witness hypothesis, the down-rounded value `F2R d` is
    nonnegative when `0 < x`. -/
lemma d_ge_0 (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) :
  0 ≤ F2R d := by
  sorry

/-- Coq: `mag_d`
    If `0 < F2R d`, then the magnitudes of `F2R d` and `x` coincide. -/
lemma mag_d (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (dPos : 0 < F2R d) :
  (FloatSpec.Core.Raux.mag beta (F2R d))
    = (FloatSpec.Core.Raux.mag beta x) := by
  sorry

/-- Midpoint between the DN/UP witnesses used in Coq's section `Fcore_rnd_odd`.
    We keep it as a plain real number constructed from `d` and `u`. -/
noncomputable def m (d u : FloatSpec.Core.Defs.FlocqFloat beta) : ℝ :=
  (F2R d + F2R u) / 2

/-- Coq: `Fexp_d`. If `0 < F2R d`, then the exponent of `d` equals
    `fexp (mag x)`. We mirror the statement shape used by adjacent lemmas. -/
lemma Fexp_d (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (dPos : 0 < F2R d) :
  d.Fexp = fexp ((FloatSpec.Core.Raux.mag beta x)) := by
  sorry

/-- Coq: `format_bpow_x` (spec-variant). If `0 < F2R d`, then the radix-
    power at `mag x` is in format. -/
lemma format_bpow_x (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (dPos : 0 < F2R d) :
  generic_format beta fexp ((beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x))) := by
  sorry

/-- Coq: `format_bpow_d` (spec-variant). If `0 < F2R d`, then the radix-
    power at `mag (F2R d)` is in format. -/
lemma format_bpow_d (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (dPos : 0 < F2R d) :
  generic_format beta fexp ((beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta (F2R d)))) := by
  sorry

/-- Coq: `d_le_m`. The down-rounded value is below the midpoint `m`. -/
lemma d_le_m (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) :
  F2R d ≤ m (beta := beta) d u := by
  sorry

/-- Coq: `m_le_u`. The midpoint `m` is below the up-rounded value. -/
lemma m_le_u (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) :
  m (beta := beta) d u ≤ F2R u := by
  sorry

/-- Coq: `mag_m`. If `0 < F2R d`, then `mag m = mag (F2R d)`. -/
lemma mag_m (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (dPos : 0 < F2R d) :
  (FloatSpec.Core.Raux.mag beta (m (beta := beta) d u))
    = (FloatSpec.Core.Raux.mag beta (F2R d)) := by
  sorry

/-- Coq: `mag_m_0`. If `F2R d = 0`, then `mag m = mag (F2R u) - 1`. -/
lemma mag_m_0 (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (dZero : F2R d = 0) :
  (FloatSpec.Core.Raux.mag beta (m (beta := beta) d u))
    = (FloatSpec.Core.Raux.mag beta (F2R u)) - 1 := by
  sorry

/-- Coq: `u'_eq`. If `0 < F2R d`, there exists a float with the same
    real value as `u` and exponent equal to `Fexp d`. -/
lemma u'_eq (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (dPos : 0 < F2R d) :
  ∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
    F2R f = F2R u ∧ f.Fexp = d.Fexp := by
  sorry

/-- Coq: `m_eq`. If `0 < F2R d`, there exists a float whose value is `m`
    and whose exponent is `fexp (mag x) - 1`. -/
lemma m_eq (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (dPos : 0 < F2R d) :
  ∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
    F2R f = m (beta := beta) d u ∧ f.Fexp = fexp ((FloatSpec.Core.Raux.mag beta x)) - 1 := by
  sorry

/-- Coq: `m_eq_0`. If `F2R d = 0`, there exists a float whose value is `m`
    and whose exponent is `fexp (mag (F2R u)) - 1`. -/
lemma m_eq_0 (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (dZero : F2R d = 0) :
  ∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
    F2R f = m (beta := beta) d u ∧ f.Fexp = fexp ((FloatSpec.Core.Raux.mag beta (F2R u))) - 1 := by
  sorry

/-- Coq: `fexp_m_eq_0`. If `F2R d = 0`, then `fexp (mag (F2R u) - 1) < fexp (mag (F2R u)) + 1`. -/
lemma fexp_m_eq_0 (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (dZero : F2R d = 0) :
  fexp ((FloatSpec.Core.Raux.mag beta (F2R u)) - 1)
    < fexp ((FloatSpec.Core.Raux.mag beta (F2R u))) + 1 := by
  sorry

variable (fexpe : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexpe]

/-- Coq: `Fm`. The midpoint `m` is in the auxiliary format `fexpe`. -/
lemma Fm (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (Hrel : ∀ e, fexpe e ≤ fexp e - 2) :
  generic_format beta fexpe (m (beta := beta) d u) := by
  sorry

/-- Coq: `Zm`. There exists a canonical representative of `m` in `fexpe`
    with an even mantissa. -/
lemma Zm (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (Hrel : ∀ e, fexpe e ≤ fexp e - 2) :
  ∃ g : FloatSpec.Core.Defs.FlocqFloat beta,
    F2R g = m (beta := beta) d u ∧
    FloatSpec.Core.Generic_fmt.canonical beta fexpe g ∧
    g.Fnum % 2 = 0 := by
  sorry

/-- Coq: `DN_odd_d_aux`.
    For any `z` between `F2R d` and `F2R u`, the DN rounding predicate
    selects `F2R d`. -/
lemma DN_odd_d_aux (x z : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (Hz : F2R d ≤ z ∧ z < F2R u) :
  FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) z (F2R d) := by
  sorry

/-- Coq: `UP_odd_d_aux`.
    For any `z` strictly between `F2R d` and `F2R u` (up to `≤` on the right),
    the UP rounding predicate selects `F2R u`. -/
lemma UP_odd_d_aux (x z : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (Hz : F2R d < z ∧ z ≤ F2R u) :
  FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) z (F2R u) := by
  sorry

variable (fexpe : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexpe]

/-- Coq: `round_N_odd_pos`.
    Under the relation `fexpe e ≤ fexp e - 2`, double rounding with
    round-to-odd at `fexpe` then nearest at `fexp` equals nearest at `fexp`.

    This is the “positive x” auxiliary version taking DN/UP witnesses `d,u`. -/
theorem round_N_odd_pos (choice : Int → Bool) (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (Hrel : ∀ e, fexpe e ≤ fexp e - 2) :
  FloatSpec.Calc.Round.round beta fexp (Znearest choice)
      (FloatSpec.Calc.Round.round beta fexpe () x)
    = FloatSpec.Calc.Round.round beta fexp (Znearest choice) x := by
  sorry

/-- Coq: `round_N_odd`.
    Global double-rounding equivalence: nearest at `fexp` after odd at `fexpe`
    equals nearest at `fexp`, assuming `fexpe ≤ fexp - 2`. -/
theorem round_N_odd (choice : Int → Bool)
  (Hrel : ∀ e, fexpe e ≤ fexp e - 2) (x : ℝ) :
  FloatSpec.Calc.Round.round beta fexp (Znearest choice)
      (FloatSpec.Calc.Round.round beta fexpe () x)
    = FloatSpec.Calc.Round.round beta fexp (Znearest choice) x := by
  sorry
