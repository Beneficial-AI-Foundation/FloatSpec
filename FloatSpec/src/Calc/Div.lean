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
import FloatSpec.src.SimprocWP

open Real FloatSpec.Calc.Bracket FloatSpec.Core.Defs FloatSpec.Core.Digits FloatSpec.Core.Generic_fmt
open FloatSpec.Core.Generic_fmt FloatSpec.Core.Raux
open Std.Do

namespace FloatSpec.Calc.Div

variable (beta : Int) [ValidRadix beta]
variable (fexp : Int → Int)

section MagnitudeBounds

/-- Compute magnitude bound for division

    Calculates the exponent range for the quotient of two floats
-/
def mag_div_F2R_compute (m1 e1 m2 e2 : Int) : Int :=
  let d1 := Zdigits beta m1
  let d2 := Zdigits beta m2
  (d1 + e1) - (d2 + e2)

/-- Specification: Division magnitude bounds

    The magnitude of a quotient is bounded by the difference of magnitudes
-/
lemma mag_div_F2R (m1 e1 m2 e2 : Int) (Hm1 : 0 < m1) (Hm2 : 0 < m2)
    (Hβ : 1 < beta) :
    ⦃⌜0 < m1 ∧ 0 < m2⌝⦄
    (pure (mag_div_F2R_compute beta m1 e1 m2 e2) : Id Int)
    ⦃⇓_ => ⌜(mag beta ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta))))
              - (mag beta ((F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta))))
              ≤ (mag beta ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)) /
                   (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta))))
          ∧ (mag beta ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)) /
                   (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta))))
              ≤ (mag beta ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta))))
                - (mag beta ((F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)))) + 1⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hm1_pos, hm2_pos⟩
  -- Reduce the computation and expose the result expression
  simp [mag_div_F2R_compute]
  -- Abbreviations
  set x : ℝ := (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta))
  set y : ℝ := (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta))
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
    (FloatSpec.Core.Raux.mag_div (beta := beta) (x := x) (y := y) Hβ hx_ne hy_ne) trivial
  -- Unpack and rewrite the triple result to get the inequalities on `mag beta (x / y)`
  -- hmag gives us: t.2.1 - t.2.2 ≤ t.1 ∧ t.1 ≤ t.2.1 - t.2.2 + 1
  -- where t = (mag β (x/y), mag β x, mag β y)
  simp only [x, y, FloatSpec.Core.Defs.F2R, pure, bind] at hmag ⊢
  simpa [wp, PostCond.noThrow, pure] using hmag

end MagnitudeBounds

section CoreDivision

/-- Core division function with precision control

    Performs division by adjusting mantissas to achieve desired exponent
-/
noncomputable def Fdiv_core_from_real_midpoint_payload
    (m1 e1 m2 e2 e : Int) : (Int × Location) :=
  (
    let (m1', m2') :=
      if e ≤ e1 - e2 then
        (m1 * beta ^ Int.natAbs (e1 - e2 - e), m2)
      else
        (m1, m2 * beta ^ Int.natAbs (e - (e1 - e2)))
    let q := m1' / m2'
    let r := m1' % m2'
    -- Define the real bounds and midpoint for the quotient interval
    let dR : ℝ := (q : ℝ) * (beta : ℝ) ^ e
    let uR : ℝ := ((q + 1 : Int) : ℝ) * (beta : ℝ) ^ e
    let xR : ℝ :=
      ((m1 : ℝ) * (beta : ℝ) ^ e1) /
      ((m2 : ℝ) * (beta : ℝ) ^ e2)
    let l := if r = 0 then Location.loc_Exact
             else Location.loc_Inexact (FloatSpec.Calc.Bracket.compare xR ((dR + uR) / 2))
    (q, l))

/-- Exact executable translation of FLoCq `Fdiv_core`. -/
noncomputable def Fdiv_core (m1 e1 m2 e2 e : Int) : (Int × Location) :=
  let (m1', m2') :=
    if e ≤ e1 - e2 then
      (m1 * beta ^ Int.natAbs (e1 - e2 - e), m2)
    else
      (m1, m2 * beta ^ Int.natAbs (e - (e1 - e2)))
  let (q, r) := FloatSpec.Core.Zaux.Z_div_eucl m1' m2'
  (q, new_location m2' r Location.loc_Exact)

/-- Specification: Core division correctness

    The computed quotient with location accurately represents the division
-/
theorem Fdiv_core_correct_left_branch (m1 e1 m2 e2 e : Int)
    (Hm1 : 0 < m1) (Hm2 : 0 < m2)
    (Hβ : 1 < beta) :
    ⦃⌜0 < m1 ∧ 0 < m2 ∧ e ≤ e1 - e2⌝⦄
    (pure (Fdiv_core beta m1 e1 m2 e2 e) : Id _)
    ⦃⇓result => let (m, l) := result
                ⌜inbetween_float beta m e
                  ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)) /
                   (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta))) l⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hm1_pos, hm2_pos, hele⟩
  -- Evaluate the branch selected by the precondition e ≤ e1 - e2
  simp [Fdiv_core, hele, pure]
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
  set dR : ℝ := (F2R (FlocqFloat.mk q e : FlocqFloat beta))
  set uR : ℝ := (F2R (FlocqFloat.mk (q + 1) e : FlocqFloat beta))
  set xR : ℝ :=
    ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta))) /
    ((F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)))
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
    have := Int.mul_ediv_add_emod m1' m2
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
  have hZdiv : FloatSpec.Core.Zaux.Z_div_eucl m1' m2 = (q, r) := by
    simp [FloatSpec.Core.Zaux.Z_div_eucl, q, r,
      Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hm2_pos), Int.emod_def]
  have hr_nonneg : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hm2_pos)
  have hr_lt : r < m2 := Int.emod_lt_of_pos _ hm2_pos
  by_cases hm2gt : 1 < m2
  · let start : ℝ := (q : ℝ) * b ^ e
    let step : ℝ := b ^ e / (m2 : ℝ)
    have hstep : 0 < step := div_pos hbpow_pos hm2R_pos
    have hx_local :
        inbetween (start + (r : ℝ) * step)
          (start + ((r : ℝ) + 1) * step) xR Location.loc_Exact := by
      apply inbetween.inbetween_Exact
      rw [hxR_eq]
      dsimp [start, step]
      field_simp [ne_of_gt hm2R_pos]
      <;> ring
    have hnew :=
      (new_location_correct (start := start) (step := step) (nb_steps := m2)
        (x := xR) (k := r) (l := Location.loc_Exact)
        hm2gt ⟨hr_nonneg, hr_lt⟩ hx_local hstep)
        ⟨hr_nonneg, hr_lt, hx_local⟩
    have hnew_run :
        inbetween start (start + (m2 : ℝ) * step) xR
          (new_location m2 r Location.loc_Exact) := by
      simpa [wp, PostCond.noThrow, pure] using hnew
    have hstart : start = dR := by simpa [start] using hdR.symm
    have hend : start + (m2 : ℝ) * step = uR := by
      dsimp [start, step]
      rw [huR]
      field_simp [ne_of_gt hm2R_pos]
      <;> ring
    have hend' : dR + (m2 : ℝ) * step = uR := by
      rw [← hstart]
      exact hend
    have hglobal :
        inbetween dR uR xR (new_location m2 r Location.loc_Exact) := by
      simpa only [hstart, hend'] using hnew_run
    simpa [inbetween_float, dR, uR, xR, hZdiv] using hglobal
  · have hm2one : m2 = 1 := by omega
    subst m2
    have hrzero : r = 0 := by simp [r]
    have hx_eq : xR = dR := by
      calc
        xR = ((q : ℝ) + (r : ℝ) / (1 : ℝ)) * b ^ e := by
          simpa using hxR_eq
        _ = (q : ℝ) * b ^ e := by simp [hrzero]
        _ = dR := hdR.symm
    have hxexact : inbetween dR uR xR Location.loc_Exact :=
      inbetween.inbetween_Exact hx_eq
    simpa [inbetween_float, dR, uR, xR, b, hZdiv, hrzero,
      new_location, new_location_odd] using hxexact

/-- FLoCq `Fdiv_core_correct`: correctness for both exponent-scaling branches. -/
theorem Fdiv_core_correct (m1 e1 m2 e2 e : Int)
    (Hm1 : 0 < m1) (Hm2 : 0 < m2) (Hβ : 1 < beta) :
    ⦃⌜True⌝⦄
    (pure (Fdiv_core beta m1 e1 m2 e2 e) : Id _)
    ⦃⇓result => let (m, l) := result
                ⌜inbetween_float beta m e
                  ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)) /
                   (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta))) l⌝⦄ := by
  intro _
  by_cases hele : e ≤ e1 - e2
  · exact Fdiv_core_correct_left_branch
      (beta := beta) m1 e1 m2 e2 e Hm1 Hm2 Hβ ⟨Hm1, Hm2, hele⟩
  · let k : Int := e - (e1 - e2)
    let p : Int := beta ^ k.natAbs
    let m2' : Int := m2 * p
    let e2' : Int := e2 - k
    have hk : 0 < k := by
      dsimp [k]
      omega
    have hbetaPos : 0 < beta := lt_trans Int.zero_lt_one Hβ
    have hp : 0 < p := by
      dsimp [p]
      exact pow_pos hbetaPos _
    have hm2' : 0 < m2' := by
      dsimp [m2']
      exact mul_pos Hm2 hp
    have hleft : e ≤ e1 - e2' := by
      dsimp [e2', k]
      omega
    have hbpos : (0 : ℝ) < beta := by exact_mod_cast hbetaPos
    have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
    have hcastp : (p : ℝ) = (beta : ℝ) ^ k := by
      dsimp [p]
      rw [Int.cast_pow]
      have hnat : ((k.natAbs : Nat) : Int) = k :=
        Int.natAbs_of_nonneg (le_of_lt hk)
      rw [← hnat]
      exact (zpow_ofNat (beta : ℝ) k.natAbs).symm
    have hden :
        F2R (FlocqFloat.mk m2' e2' : FlocqFloat beta) =
          F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta) := by
      unfold FloatSpec.Core.Defs.F2R
      change (m2' : ℝ) * (beta : ℝ) ^ e2' =
        (m2 : ℝ) * (beta : ℝ) ^ e2
      rw [show (m2' : ℝ) = (m2 : ℝ) * (p : ℝ) by simp [m2']]
      rw [hcastp]
      calc
        ((m2 : ℝ) * (beta : ℝ) ^ k) * (beta : ℝ) ^ e2'
            = (m2 : ℝ) * ((beta : ℝ) ^ k * (beta : ℝ) ^ e2') := by ring
        _ = (m2 : ℝ) * (beta : ℝ) ^ (k + e2') := by
          rw [zpow_add₀ hbne]
        _ = (m2 : ℝ) * (beta : ℝ) ^ e2 := by
          congr 2
          dsimp [e2']
          omega
    have hdenRaw :
        (m2' : ℝ) * (beta : ℝ) ^ e2' =
          (m2 : ℝ) * (beta : ℝ) ^ e2 := by
      simpa [FloatSpec.Core.Defs.F2R] using hden
    have hdenScaled :
        ((m2 : ℝ) * (beta : ℝ) ^ k.natAbs) * (beta : ℝ) ^ e2' =
          (m2 : ℝ) * (beta : ℝ) ^ e2 := by
      simpa [m2', p, Int.cast_pow] using hdenRaw
    have hcore :
        Fdiv_core beta m1 e1 m2' e2' e =
          Fdiv_core beta m1 e1 m2 e2 e := by
      have hzero : e1 - e2' - e = 0 := by
        dsimp [e2', k]
        omega
      unfold Fdiv_core
      simp only [hleft, if_pos, hele, if_neg]
      simp [hzero, m2', p, k, hdenScaled]
    have h := Fdiv_core_correct_left_branch
      (beta := beta) m1 e1 m2' e2' e Hm1 hm2' Hβ
      ⟨Hm1, hm2', hleft⟩
    simpa [wp, PostCond.noThrow, pure, hcore, hdenRaw] using h

end CoreDivision

section MainDivision

/-- Main division function

    Computes the quotient of two floats with automatic exponent selection
-/
noncomputable def Fdiv (x y : FlocqFloat beta) : (Int × Int × Location) :=
  let m1 := x.Fnum
  let e1 := x.Fexp
  let m2 := y.Fnum
  let e2 := y.Fexp
  let d1 := Zdigits beta m1
  let d2 := Zdigits beta m2
  let e' := (d1 + e1) - (d2 + e2)
  let e := min (min (fexp e') (fexp (e' + 1))) (e1 - e2)
  let (m, l) := Fdiv_core beta m1 e1 m2 e2 e
  (m, e, l)

/-- Specification: Division correctness

    The division result accurately represents the quotient with proper location
-/
theorem Fdiv_correct (x y : FlocqFloat beta)
    (Hβ : 1 < beta)
    (Hx : 0 < (F2R x)) (Hy : 0 < (F2R y)) :
    ⦃⌜0 < (F2R x) ∧ 0 < (F2R y)⌝⦄
    (pure (Fdiv beta fexp x y) : Id _)
    ⦃⇓result => let (m, e, l) := result
                ⌜e ≤ cexp beta fexp ((F2R x) / (F2R y)) ∧
                  inbetween_float beta m e ((F2R x) / (F2R y)) l⌝⦄ := by
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
      simp (config := {zeta := true}) [Fdiv, bind, pure]
      -- Notations for digit counts, candidate exponent, and quotient
      set d1 : Int := (Zdigits beta m1)
      set d2 : Int := (Zdigits beta m2)
      set e' : Int := (d1 + e1) - (d2 + e2)
      set e  : Int := min (min (fexp e') (fexp (e' + 1))) (e1 - e2)
      set qR : ℝ :=
        ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)) /
         (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)))
      -- Inbetween property via core correctness; precondition e ≤ e1 - e2 by construction
      have hele : e ≤ e1 - e2 := by
        have : e ≤ (e1 - e2) := min_le_right _ _
        simpa [e] using this
      -- Apply core correctness and rewrite to obtain the inbetween property on the components
      have hinst :=
        (Fdiv_core_correct (beta := beta) (m1 := m1) (e1 := e1)
          (m2 := m2) (e2 := e2) (e := e) (Hm1 := hm1_pos) (Hm2 := hm2_pos) (Hβ := Hβ))
          trivial
      have hinSimple : inbetween_float beta (Fdiv_core beta m1 e1 m2 e2 e).fst e qR
            (Fdiv_core beta m1 e1 m2 e2 e).snd := by
        simpa [wp, PostCond.noThrow, pure] using hinst
      have hmag := mag_div_F2R (beta := beta) m1 e1 m2 e2 hm1_pos hm2_pos Hβ
        ⟨hm1_pos, hm2_pos⟩
      have hmag1 := FloatSpec.Core.Float_prop.Raux_mag_F2R_Zdigits
        (beta := beta) m1 e1 Hβ (ne_of_gt hm1_pos)
      have hmag2 := FloatSpec.Core.Float_prop.Raux_mag_F2R_Zdigits
        (beta := beta) m2 e2 Hβ (ne_of_gt hm2_pos)
      simp only [wp, PostCond.noThrow, pure] at hmag
      rw [hmag1, hmag2] at hmag
      have hbounds : e' ≤ mag beta qR ∧ mag beta qR ≤ e' + 1 := by
        simpa [qR, e', d1, d2, wp, PostCond.noThrow, pure] using hmag
      have hmag_cases : mag beta qR = e' ∨ mag beta qR = e' + 1 := by omega
      have he_cexp : e ≤ cexp beta fexp qR := by
        unfold cexp
        rcases hmag_cases with hm | hm
        · rw [hm]
          exact le_trans (min_le_left _ _) (min_le_left _ _)
        · rw [hm]
          exact le_trans (min_le_left _ _) (min_le_right _ _)
      simpa [qR, e, e', d1, d2] using And.intro he_cexp hinSimple

end MainDivision

end FloatSpec.Calc.Div
