/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4, ported from Coq: https://flocq.gitlabpages.inria.fr/

Helper function and theorem for computing the rounded quotient of two floating-point numbers
Translated from Coq file: flocq/src/Calc/Div.v
-/

import FloatSpec.src.Core.Zaux
import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Generic_fmt
import FloatSpec.src.Core.Float_prop
import FloatSpec.src.Core.Digits
import FloatSpec.src.Calc.Bracket
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real FloatSpec.Calc.Bracket FloatSpec.Core.Defs FloatSpec.Core.Digits FloatSpec.Core.Generic_fmt
open FloatSpec.Core.Generic_fmt FloatSpec.Core.Raux
open Std.Do

namespace FloatSpec.Calc.Div

variable (beta : Int)
variable (fexp : Int → Int)

section MagnitudeBounds

/-- Compute magnitude bound for division

    Calculates the exponent range for the quotient of two floats
-/
def mag_div_F2R_compute (m1 e1 m2 e2 : Int) : Id Int :=
  Zdigits beta m1 >>= fun d1 =>
  Zdigits beta m2 >>= fun d2 =>
  pure ((d1 + e1) - (d2 + e2))

/-- Specification: Division magnitude bounds

    The magnitude of a quotient is bounded by the difference of magnitudes
-/
lemma mag_div_F2R (m1 e1 m2 e2 : Int) (Hm1 : 0 < m1) (Hm2 : 0 < m2)
    (Hβ : 1 < beta) :
    ⦃⌜0 < m1 ∧ 0 < m2⌝⦄
    mag_div_F2R_compute beta m1 e1 m2 e2
    ⦃⇓_ => ⌜(mag beta ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run)).run
              - (mag beta ((F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)).run)).run
              ≤ (mag beta ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run /
                   (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)).run)).run
          ∧ (mag beta ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run /
                   (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)).run)).run
              ≤ (mag beta ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run)).run
                - (mag beta ((F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)).run)).run + 1⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hm1_pos, hm2_pos⟩
  -- Reduce the computation and expose the result expression
  simp [mag_div_F2R_compute, wp, PostCond.noThrow, Id.run]
  -- Abbreviations
  set x : ℝ := (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run
  set y : ℝ := (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)).run
  have hx_ne : x ≠ 0 := by
    have hx_pos : 0 < x := by
      simpa [FloatSpec.Core.Defs.F2R] using
        (FloatSpec.Core.Float_prop.F2R_gt_0 (beta := beta) (f := FlocqFloat.mk m1 e1) Hβ hm1_pos)
    exact ne_of_gt hx_pos
  have hy_ne : y ≠ 0 := by
    have hy_pos : 0 < y := by
      simpa [FloatSpec.Core.Defs.F2R] using
        (FloatSpec.Core.Float_prop.F2R_gt_0 (beta := beta) (f := FlocqFloat.mk m2 e2) Hβ hm2_pos)
    exact ne_of_gt hy_pos
  -- Use generic magnitude bound under division from Core.Raux
  have hmag :=
    (FloatSpec.Core.Raux.mag_div (beta := beta) (x := x) (y := y))
      ⟨Hβ, hx_ne, hy_ne⟩
  -- Unpack and rewrite the triple result to get the inequalities on `mag beta (x / y)`
  simpa [x, y, FloatSpec.Core.Defs.F2R, wp, PostCond.noThrow, Id.run, pure, bind]
    using hmag

end MagnitudeBounds

section CoreDivision

/-- Core division function with precision control

    Performs division by adjusting mantissas to achieve desired exponent
-/
noncomputable def Fdiv_core (m1 e1 m2 e2 e : Int) : Id (Int × Location) :=
  pure (
    let (m1', m2') :=
      if e ≤ e1 - e2 then
        (m1 * beta ^ Int.natAbs (e1 - e2 - e), m2)
      else
        (m1, m2 * beta ^ Int.natAbs (e - (e1 - e2)))
    let q := m1' / m2'
    let r := m1' % m2'
    -- Define the real bounds and midpoint for the quotient interval
    let dR : ℝ := (F2R (FlocqFloat.mk q e : FlocqFloat beta)).run
    let uR : ℝ := (F2R (FlocqFloat.mk (q + 1) e : FlocqFloat beta)).run
    let xR : ℝ :=
      ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run) /
      ((F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)).run)
    let l := if r = 0 then Location.loc_Exact
             else Location.loc_Inexact (FloatSpec.Calc.Bracket.compare xR ((dR + uR) / 2))
    (q, l))

/-- Specification: Core division correctness

    The computed quotient with location accurately represents the division
-/
theorem Fdiv_core_correct (m1 e1 m2 e2 e : Int) (Hm1 : 0 < m1) (Hm2 : 0 < m2)
    (Hβ : 1 < beta) :
    ⦃⌜0 < m1 ∧ 0 < m2 ∧ e ≤ e1 - e2⌝⦄
    Fdiv_core beta m1 e1 m2 e2 e
    ⦃⇓result => let (m, l) := result
                ⌜inbetween_float beta m e
                  ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run /
                   (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)).run) l⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hm1_pos, hm2_pos, hele⟩
  -- Evaluate the branch selected by the precondition e ≤ e1 - e2
  simp [Fdiv_core, hele, wp, PostCond.noThrow, Id.run, pure]
  -- Abbreviations for reals and base
  set b : ℝ := (beta : ℝ)
  have hbpos : 0 < b := by
    have hbpos' : (0 : ℝ) < (beta : ℝ) := by
      exact_mod_cast (lt_trans (by decide) Hβ : (0 : Int) < beta)
    simpa [b] using hbpos'
  have hbne : b ≠ 0 := ne_of_gt hbpos
  -- With the chosen branch, m2' = m2 and m1' = m1 * beta ^ |e1 - e2 - e|
  -- Define helpful names for quotient and remainder (matching the ones introduced by simp)
  set m1' : Int := m1 * beta ^ Int.natAbs (e1 - e2 - e)
  set q : Int := m1' / m2
  set r : Int := m1' % m2
  -- Real endpoints and target value
  set dR : ℝ := (F2R (FlocqFloat.mk q e : FlocqFloat beta)).run
  set uR : ℝ := (F2R (FlocqFloat.mk (q + 1) e : FlocqFloat beta)).run
  set xR : ℝ :=
    ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run) /
    ((F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)).run)
  -- Show that xR is between dR and uR, using Euclidean division properties
  have hm2R_pos : 0 < (m2 : ℝ) := by exact_mod_cast hm2_pos
  have hbpow_pos : 0 < b ^ e := zpow_pos hbpos _
  -- Expand the real forms of dR, uR, xR
  have hdR : dR = (q : ℝ) * b ^ e := by simpa [dR, F2R, b]
  have huR : uR = (q + 1 : ℝ) * b ^ e := by simpa [uR, F2R, b]
  -- Express xR as ((m1' / m2) : ℝ) * b ^ e
  -- First, relate b^(e1 - e2) with b^(e1 - e2 - e) * b^e
  have hnonneg : 0 ≤ e1 - e2 - e := sub_nonneg.mpr hele
  have hzpow_split : b ^ (e1 - e2) = b ^ (e1 - e2 - e) * b ^ e := by
    have := (zpow_add₀ hbne (e1 - e2 - e) e)
    simpa [sub_add, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
  -- Cast the integer power used in m1' to real
  have cast_pow : ((beta ^ Int.natAbs (e1 - e2 - e) : Int) : ℝ)
        = b ^ (Int.natAbs (e1 - e2 - e)) := by
    simpa [b] using (Int.cast_pow (R := ℝ) (m := beta) (n := Int.natAbs (e1 - e2 - e)))
  -- Connect b^E with the natural-power form since E ≥ 0
  set E : Int := e1 - e2 - e
  have hE_nonneg : 0 ≤ E := hnonneg
  have hE_toNat : Int.ofNat (Int.toNat E) = E := Int.toNat_of_nonneg hE_nonneg
  -- Bridge zpow Int exponent with nat power under E ≥ 0
  have hbE : (b ^ (E : Int)) = b ^ (Int.natAbs E) := by
    -- First rewrite exponent to (E.natAbs : Int), then move to Nat exponent
    have habs_int : (b ^ (E : Int)) = b ^ ((E.natAbs : Int)) := by
      have h1 : ((E.natAbs : Int)) = E := Int.natAbs_of_nonneg hE_nonneg
      simpa [h1]
    have htoNat : b ^ ((E.natAbs : Int)) = b ^ (E.natAbs) :=
      _root_.zpow_ofNat b (E.natAbs)
    simpa using habs_int.trans htoNat
  -- Now compute xR in terms of q and r
  -- Use Euclidean division decomposition at integers: m1' = m2 * q + r
  have hdecompZ : m2 * q + r = m1 * beta ^ Int.natAbs (e1 - e2 - e) := by
    -- Euclidean division decomposition for integers
    have := Int.ediv_add_emod m1' m2
    -- Unfold m1'
    simpa [m1'] using this
  -- Cast to reals and divide by m2
  have hdecompR : (m2 : ℝ) * (q : ℝ) + (r : ℝ)
      = (m1 : ℝ) * b ^ (Int.natAbs E) := by
    -- rewrite the cast of pow and of the decomposition
    have := congrArg (fun t : Int => (t : ℝ)) hdecompZ
    simpa [Int.cast_mul, Int.cast_add, cast_pow, E, b] using this
  -- Divide by positive (m2 : ℝ)
  have hdivR : ((m1 : ℝ) * b ^ (e1 - e2 - e)) / (m2 : ℝ)
      = (q : ℝ) + (r : ℝ) / (m2 : ℝ) := by
    have hm2_ne : (m2 : ℝ) ≠ 0 := ne_of_gt hm2R_pos
    -- Start from the integer decomposition divided by m2 on both sides
    have hstep : ((m1 : ℝ) * b ^ (Int.natAbs E)) / (m2 : ℝ)
                = ((m2 : ℝ) * (q : ℝ) + (r : ℝ)) / (m2 : ℝ) := by
      have := congrArg (fun t : ℝ => t / (m2 : ℝ)) (by simpa [Int.cast_mul, Int.cast_add, cast_pow, E, b] using congrArg (fun t : Int => (t : ℝ)) hdecompZ.symm)
      simpa using this
    -- Simplify the RHS and rewrite b^natAbs E as b^E
    have hRHS : ((m2 : ℝ) * (q : ℝ) + (r : ℝ)) / (m2 : ℝ)
                  = (q : ℝ) + (r : ℝ) / (m2 : ℝ) := by
      simp [add_div, hm2_ne]
    -- Put together
    calc
      ((m1 : ℝ) * b ^ (e1 - e2 - e)) / (m2 : ℝ)
          = ((m1 : ℝ) * b ^ (Int.natAbs E)) / (m2 : ℝ) := by simpa [E, hbE]
      _   = ((m2 : ℝ) * (q : ℝ) + (r : ℝ)) / (m2 : ℝ) := hstep
      _   = (q : ℝ) + (r : ℝ) / (m2 : ℝ) := hRHS
  -- Bridge from xR to ((m1' / m2) : ℝ) * b^e
  have hxR_eq : xR = ((q : ℝ) + (r : ℝ) / (m2 : ℝ)) * b ^ e := by
    -- Step 1: compute xR in the (e1 - e2) exponent form
    have hx0 : xR = (((m1 : ℝ) * b ^ (e1 - e2)) / (m2 : ℝ)) := by
      -- Expand xR and cancel the common factor b^e2 on numerator and denominator
      have hz : b ^ e1 = b ^ (e1 - e2) * b ^ e2 := by
        simpa [sub_eq_add_neg] using (zpow_add₀ hbne (e1 - e2) e2)
      have hbpow_ne' : b ^ e2 ≠ 0 := by
        simpa using zpow_ne_zero e2 hbne
      have hxR_base : xR = ((m1 : ℝ) * b ^ e1) / ((m2 : ℝ) * b ^ e2) := by
        -- rearrange ((m1*b^e1)/(m2*b^e2)) from the original definition
        simp [xR, F2R, b, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      calc
        xR = (((m1 : ℝ) * (b ^ (e1 - e2) * b ^ e2)) / ((m2 : ℝ) * b ^ e2)) := by
          simpa [hxR_base, hz]
        _  = ((((m1 : ℝ) * b ^ (e1 - e2)) * b ^ e2) / ((m2 : ℝ) * b ^ e2)) := by
          simp [mul_comm, mul_left_comm, mul_assoc]
        _  = (((m1 : ℝ) * b ^ (e1 - e2)) / (m2 : ℝ)) * (b ^ e2 / b ^ e2) := by
          -- Cancel the common factor b^e2 on both numerator and denominator,
          -- then re-introduce it as a neutral factor (b^e2)/(b^e2) = 1
          have hcancel : ((((m1 : ℝ) * b ^ (e1 - e2)) * b ^ e2) / ((m2 : ℝ) * b ^ e2))
              = (((m1 : ℝ) * b ^ (e1 - e2)) / (m2 : ℝ)) := by
            -- Use the standard cancellation lemma a*c/(b*c)=a/b with c≠0
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (mul_div_mul_left ((m1 : ℝ) * b ^ (e1 - e2)) (m2 : ℝ) hbpow_ne')
          have hone : (b ^ e2) / (b ^ e2) = (1 : ℝ) := by
            simp [hbpow_ne']
          calc
            ((((m1 : ℝ) * b ^ (e1 - e2)) * b ^ e2) / ((m2 : ℝ) * b ^ e2))
                = (((m1 : ℝ) * b ^ (e1 - e2)) / (m2 : ℝ)) := hcancel
            _ = (((m1 : ℝ) * b ^ (e1 - e2)) / (m2 : ℝ)) * 1 := by simp
            _ = (((m1 : ℝ) * b ^ (e1 - e2)) / (m2 : ℝ)) * (b ^ e2 / b ^ e2) := by
                  simpa [hone]
        _  = (((m1 : ℝ) * b ^ (e1 - e2)) / (m2 : ℝ)) := by
          simp [hbpow_ne']
    -- Step 2: split exponent to isolate b^e, then use the Euclidean decomposition
    have hx1 : ((m1 : ℝ) * b ^ (e1 - e2)) / (m2 : ℝ)
          = (((m1 : ℝ) * b ^ (e1 - e2 - e)) / (m2 : ℝ)) * b ^ e := by
      calc
        ((m1 : ℝ) * b ^ (e1 - e2)) / (m2 : ℝ)
            = ((m1 : ℝ) * (b ^ (e1 - e2 - e) * b ^ e)) / (m2 : ℝ) := by
                simp [hzpow_split, E, mul_comm, mul_left_comm, mul_assoc]
        _   = (((m1 : ℝ) * b ^ (e1 - e2 - e)) / (m2 : ℝ)) * b ^ e := by
                simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    -- Step 3: Use the Euclidean division relation to rewrite ((m1 * b^E)/m2)
    have hdivR' : ((m1 : ℝ) * b ^ (e1 - e2 - e)) / (m2 : ℝ)
          = (q : ℝ) + (r : ℝ) / (m2 : ℝ) := by simpa [b, hbE] using hdivR
    -- Step 4: Conclude
    calc
      xR = ((m1 : ℝ) * b ^ (e1 - e2)) / (m2 : ℝ) := hx0
      _  = (((m1 : ℝ) * b ^ (e1 - e2 - e)) / (m2 : ℝ)) * b ^ e := hx1
      _  = ((q : ℝ) + (r : ℝ) / (m2 : ℝ)) * b ^ e := by simpa [hdivR']
  -- Conclude the inbetween proof by cases on r
  by_cases hr0 : r = 0
  · -- Exact case
    have hr0R : (r : ℝ) = 0 := by simpa using congrArg (fun t : Int => (t : ℝ)) hr0
    -- xR = q*b^e
    have hx_eq : xR = (q : ℝ) * b ^ e := by
      simpa [hxR_eq, hr0R, hdR, mul_comm] using rfl
    -- build the predicate
    have hx_eq' : xR = dR := by simpa [hdR] using hx_eq
    have hx_exact : FloatSpec.Calc.Bracket.inbetween dR uR xR Location.loc_Exact := by
      have hx_exact_raw : inbetween ((q : ℝ) * b ^ e) ((q + 1 : ℝ) * b ^ e) xR Location.loc_Exact :=
        FloatSpec.Calc.Bracket.inbetween.inbetween_Exact hx_eq
      simpa [hdR, huR] using hx_exact_raw
    -- Under r = 0, we have m2 ∣ m1' so the goal's conditional location reduces to loc_Exact
    have hdiv : m2 ∣ m1' := by
      -- r = m1' % m2 by definition; with r = 0 obtain divisibility
      have : m1' % m2 = 0 := by simpa [r] using hr0
      exact Int.dvd_of_emod_eq_zero this
    simpa [inbetween_float, dR, uR, xR, hdiv] using hx_exact
  · -- Inexact case: show strict inequalities dR < xR < uR
    have hr_nonnegZ : (0 : Int) ≤ r := Int.emod_nonneg _ (ne_of_gt hm2_pos)
    have hr_posZ : 0 < r := lt_of_le_of_ne' hr_nonnegZ hr0
    have hr_ltZ : r < m2 := Int.emod_lt_of_pos _ hm2_pos
    have hr_posR : 0 < (r : ℝ) := by exact_mod_cast hr_posZ
    have hm2_posR : 0 < (m2 : ℝ) := by exact_mod_cast hm2_pos
    have hr_div_pos : 0 < (r : ℝ) / (m2 : ℝ) := div_pos hr_posR hm2_posR
    have hr_div_lt_one : (r : ℝ) / (m2 : ℝ) < 1 := by
      have : (r : ℝ) < (m2 : ℝ) := by exact_mod_cast hr_ltZ
      have hm2_posR' : 0 < (m2 : ℝ) := hm2_posR
      have h := (div_lt_div_of_pos_right this hm2_posR')
      simpa [div_self (ne_of_gt hm2_posR')] using h
    -- turn into bounds for xR around dR and uR
    have hdx : dR < xR := by
      -- xR = dR + (r/m2)*b^e with positive increment
      have : xR = (q : ℝ) * b ^ e + ((r : ℝ) / (m2 : ℝ)) * b ^ e := by
        simpa [hxR_eq, mul_add, mul_comm, mul_left_comm, mul_assoc]
      have hincr_pos : 0 < ((r : ℝ) / (m2 : ℝ)) * b ^ e := mul_pos hr_div_pos hbpow_pos
      simpa [hdR, this, lt_add_iff_pos_right]
    have hux : xR < uR := by
      -- uR = dR + b^e and 0 < (r/m2) * b^e < b^e
      have hx' : xR = dR + ((r : ℝ) / (m2 : ℝ)) * b ^ e := by
        simpa [hxR_eq, hdR, mul_add, mul_comm, mul_left_comm, mul_assoc]
      have hincr_lt : ((r : ℝ) / (m2 : ℝ)) * b ^ e < b ^ e := by
        have := (mul_lt_mul_of_pos_right hr_div_lt_one hbpow_pos)
        simpa using this
      have : xR < dR + b ^ e := by
        have hbnd : dR + ((r : ℝ) / (m2 : ℝ)) * b ^ e < dR + b ^ e := by
          exact add_lt_add_right hincr_lt dR
        simpa [hx'] using hbnd
      -- rewrite dR + b^e into (q + 1) * b^e using distributivity
      have hsum : dR + b ^ e = (q + 1 : ℝ) * b ^ e := by
        have := (add_mul (q : ℝ) (1 : ℝ) (b ^ e))
        -- (q + 1) * b^e = q*b^e + 1*b^e
        simpa [hdR, one_mul, add_comm] using this.symm
      have hxR_lt : xR < (q + 1 : ℝ) * b ^ e := by simpa [hsum] using this
      simpa [huR] using hxR_lt
    -- Convert bounds to the raw endpoint form
    have hdx' : (q : ℝ) * b ^ e < xR := by simpa [hdR] using hdx
    have hux' : xR < (q + 1 : ℝ) * b ^ e := by simpa [huR] using hux
    -- Conclude with Inexact location, where the ordering matches by construction
    have hx_inexact_raw :
        FloatSpec.Calc.Bracket.inbetween ((q : ℝ) * b ^ e) ((q + 1 : ℝ) * b ^ e) xR
          (Location.loc_Inexact (FloatSpec.Calc.Bracket.compare xR (((q : ℝ) * b ^ e + (q + 1 : ℝ) * b ^ e) / 2))) := by
      refine FloatSpec.Calc.Bracket.inbetween.inbetween_Inexact
        (l := FloatSpec.Calc.Bracket.compare xR (((q : ℝ) * b ^ e + (q + 1 : ℝ) * b ^ e) / 2)) ?hb ?hc
      · exact ⟨hdx', hux'⟩
      · rfl
    have hx_inexact :
        FloatSpec.Calc.Bracket.inbetween dR uR xR
          (Location.loc_Inexact (FloatSpec.Calc.Bracket.compare xR ((dR + uR) / 2))) := by
      simpa [hdR, huR] using hx_inexact_raw
    -- Under r ≠ 0, we have ¬ m2 ∣ m1' so the goal's conditional location reduces to loc_Inexact ...
    have hnotdvd : ¬ m2 ∣ m1' := by
      intro h
      have : m1' % m2 = 0 := Int.emod_eq_zero_of_dvd h
      exact hr0 (by simpa [r])
    simpa [inbetween_float, dR, uR, xR, hnotdvd] using hx_inexact
    -- The alternative branch of Fdiv_core is not needed here because the precondition enforces e ≤ e1 - e2

end CoreDivision

section MainDivision

/-- Main division function

    Computes the quotient of two floats with automatic exponent selection
-/
noncomputable def Fdiv (x y : FlocqFloat beta) : Id (Int × Int × Location) :=
  let m1 := x.Fnum
  let e1 := x.Fexp
  let m2 := y.Fnum
  let e2 := y.Fexp
  Zdigits beta m1 >>= fun d1 =>
  Zdigits beta m2 >>= fun d2 =>
  let e' := (d1 + e1) - (d2 + e2)
  let e := min (min (fexp e') (fexp (e' + 1))) (e1 - e2)
  Fdiv_core beta m1 e1 m2 e2 e >>= fun (m, l) =>
  pure (m, e, l)

/-- Specification: Division correctness

    The division result accurately represents the quotient with proper location
-/
theorem Fdiv_correct (x y : FlocqFloat beta)
    (Hβ : 1 < beta)
    (Hx : 0 < (F2R x).run) (Hy : 0 < (F2R y).run) :
    ⦃⌜0 < (F2R x).run ∧ 0 < (F2R y).run⌝⦄
    Fdiv beta fexp x y
    ⦃⇓result => let (m, e, l) := result
                ⌜inbetween_float beta m e ((F2R x).run / (F2R y).run) l⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hx_pos, hy_pos⟩
  -- Destructure inputs to access components
  cases x with
  | mk m1 e1 =>
    cases y with
    | mk m2 e2 =>
      -- Positive F2R implies positive mantissas when 1 < beta
      have hm1_pos : 0 < m1 :=
        (FloatSpec.Core.Float_prop.gt_0_F2R (beta := beta) (f := FlocqFloat.mk m1 e1) Hβ) hx_pos
      have hm2_pos : 0 < m2 :=
        (FloatSpec.Core.Float_prop.gt_0_F2R (beta := beta) (f := FlocqFloat.mk m2 e2) Hβ) hy_pos
      -- Reduce the Id binds of Fdiv
      simp (config := {zeta := true}) [Fdiv, wp, PostCond.noThrow, Id.run, bind, pure]
      -- Notations for digit counts, candidate exponent, and quotient
      set d1 : Int := (Zdigits beta m1).run
      set d2 : Int := (Zdigits beta m2).run
      set e' : Int := (d1 + e1) - (d2 + e2)
      set e  : Int := min (min (fexp e') (fexp (e' + 1))) (e1 - e2)
      set qR : ℝ :=
        ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run /
         (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)).run)
      -- Inbetween property via core correctness; precondition e ≤ e1 - e2 by construction
      have hele : e ≤ e1 - e2 := by
        have : e ≤ (e1 - e2) := min_le_right _ _
        simpa [e] using this
      -- Apply core correctness and rewrite to obtain the inbetween property on the components
      have hinst :=
        (Fdiv_core_correct (beta := beta) (m1 := m1) (e1 := e1)
          (m2 := m2) (e2 := e2) (e := e) (Hm1 := hm1_pos) (Hm2 := hm2_pos) (Hβ := Hβ))
          ⟨hm1_pos, hm2_pos, hele⟩
      have hinSimple : inbetween_float beta ((Fdiv_core beta m1 e1 m2 e2 e).run).fst e qR
            ((Fdiv_core beta m1 e1 m2 e2 e).run).snd := by
        simpa [wp, PostCond.noThrow, Id.run, pure] using hinst
      -- The goal matches this after rewriting the `match` structure; conclude by `simpa`.
      simpa [qR, e, e', d1, d2] using hinSimple

end MainDivision

end FloatSpec.Calc.Div
