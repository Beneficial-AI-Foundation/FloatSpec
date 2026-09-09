/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4, ported from Coq: https://flocq.gitlabpages.inria.fr/

Helper function and theorem for computing the rounded sum of two floating-point numbers
Translated from Coq file: flocq/src/Calc/Plus.v
-/

import FloatSpec.src.Core
import FloatSpec.src.Calc.Bracket
import FloatSpec.src.Calc.Round
import FloatSpec.src.Core.Digits
import FloatSpec.src.Core.Generic_fmt
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do
import FloatSpec.src.SimprocWP

open Real FloatSpec.Calc.Bracket FloatSpec.Core.Digits FloatSpec.Core.Defs FloatSpec.Core.Generic_fmt
open FloatSpec.Core.Generic_fmt
open Std.Do

namespace FloatSpec.Calc.Plus

variable (beta : Int) [ValidRadix beta]
variable (fexp : Int → Int)

section CoreAddition

/-- Re-expressing an integer mantissa at a lower exponent preserves its
    represented real value.  This is the arithmetic bridge used by the two
    source `Fplus` correctness proofs. -/
private theorem F2R_scale_to_lower (m e₁ e : Int) (he : e ≤ e₁) :
    (((m * beta ^ Int.natAbs (e₁ - e) : Int) : ℝ) * (beta : ℝ) ^ e) =
      F2R (FlocqFloat.mk m e₁ : FlocqFloat beta) := by
  have hβpos : (0 : Int) < beta := lt_trans (by decide) (ValidRadix.valid (beta := beta))
  have hβne : (beta : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hβpos)
  have hdiff : 0 ≤ e₁ - e := sub_nonneg.mpr he
  have hnat : ((Int.natAbs (e₁ - e) : Nat) : Int) = e₁ - e :=
    Int.natAbs_of_nonneg hdiff
  simp only [F2R, Int.cast_mul, Int.cast_pow]
  rw [show (beta : ℝ) ^ Int.natAbs (e₁ - e) =
      (beta : ℝ) ^ (e₁ - e) by rw [← zpow_natCast, hnat]]
  rw [mul_assoc, ← zpow_add₀ hβne]
  simp

/-- Core addition function with precision control

    Performs addition with specified target exponent and location tracking
-/
noncomputable def Fplus_core (m1 e1 m2 e2 e : Int) : (Int × Location) :=
  let k := e - e2
  let t :=
    if 0 < k then
      FloatSpec.Calc.Round.truncate_aux beta (m2, e2, Location.loc_Exact) k
    else
      (m2 * beta ^ Int.natAbs (-k), e, Location.loc_Exact)
  let m2' := t.1
  let l := t.2.2
  let m1' := m1 * beta ^ Int.natAbs (e1 - e)
  (m1' + m2', l)

/-- Coq `Fplus_core_correct`: the mantissa/location returned by `Fplus_core`
    brackets the exact real sum at the requested exponent. -/
theorem Fplus_core_correct (m1 e1 m2 e2 e : Int) (He1 : e ≤ e1) :
    let (m, l) := Fplus_core beta m1 e1 m2 e2 e
    inbetween_float beta m e
      (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta) +
       F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)) l := by
  have hβ : 1 < beta := ValidRadix.valid
  have hm1 := F2R_scale_to_lower (beta := beta) m1 e1 e He1
  by_cases hk : 0 < e - e2
  · let p : Int := beta ^ Int.natAbs (e - e2)
    have hbase : inbetween_float beta m2 e2
        (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)) Location.loc_Exact := by
      exact inbetween.inbetween_Exact rfl
    have htrunc := inbetween_float_new_location (beta := beta)
      (x := F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta))
      (m := m2) (e := e2) (l := Location.loc_Exact) (k := e - e2)
      hk hβ hbase
    have htranslated := inbetween_plus_compat
      (x := F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta))
      (d := ((m2 / p : Int) : ℝ) * (beta : ℝ) ^ e)
      (u := (((m2 / p + 1 : Int) : ℝ) * (beta : ℝ) ^ e))
      (l := Id.run (new_location (nb_steps := p) (k := m2 % p) Location.loc_Exact))
      (t := F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)) (by
        simpa [inbetween_float, p, add_assoc] using htrunc)
    have hk' : e2 < e := by omega
    have hm1' : ((m1 : ℝ) * (beta : ℝ) ^ Int.natAbs (e1 - e)) *
        (beta : ℝ) ^ e = (m1 : ℝ) * (beta : ℝ) ^ e1 := by
      simpa [F2R, Int.cast_mul, Int.cast_pow] using hm1
    simpa [Fplus_core, hk, hk', FloatSpec.Calc.Round.truncate_aux, p,
      inbetween_float, hm1', add_comm, add_left_comm, add_assoc,
      Int.cast_add, Int.cast_mul, Int.cast_pow, mul_add, add_mul] using htranslated
  · have he2 : e ≤ e2 := by omega
    have hm2 := F2R_scale_to_lower (beta := beta) m2 e2 e he2
    simp only [Fplus_core, hk, ite_false]
    apply inbetween.inbetween_Exact
    have hm1' : (((m1 * beta ^ Int.natAbs (e1 - e) : Int) : ℝ) * (beta : ℝ) ^ e) =
        (m1 : ℝ) * (beta : ℝ) ^ e1 := by simpa [F2R] using hm1
    have hm2' : (((m2 * beta ^ Int.natAbs (e2 - e) : Int) : ℝ) * (beta : ℝ) ^ e) =
        (m2 : ℝ) * (beta : ℝ) ^ e2 := by simpa [F2R] using hm2
    simp only [F2R, Int.cast_add, Int.cast_mul, Int.cast_pow]
    rw [← hm1', ← hm2']
    have hneg : -(e - e2) = e2 - e := by omega
    rw [hneg]
    simp only [Int.cast_mul, Int.cast_pow]
    ring

end CoreAddition

section MainAddition

variable [Monotone_exp fexp]

/-- Main addition function

    Adds two floats with intelligent exponent selection for precision.
    This follows the Coq Flocq implementation structure.
-/
noncomputable def Fplus (f1 f2 : FlocqFloat beta) : (Int × Int × Location) :=
  let m1 := f1.Fnum
  let e1 := f1.Fexp
  let m2 := f2.Fnum
  let e2 := f2.Fexp
  if m1 = 0 then
    (m2, e2, Location.loc_Exact)
  else if m2 = 0 then
    (m1, e1, Location.loc_Exact)
  else
    -- Evaluate digit counts
    let d1 := Zdigits beta m1
    let d2 := Zdigits beta m2
    let p1 := d1 + e1
    let p2 := d2 + e2
    if 2 ≤ Int.natAbs (p1 - p2) then
      let e := min (max e1 e2) (fexp (max p1 p2 - 1))
      let (m, l) :=
        if e1 < e then
          Fplus_core beta m2 e2 m1 e1 e
        else
          Fplus_core beta m1 e1 m2 e2 e
      (m, e, l)
    else
      -- When |p1 - p2| < 2, compute exact sum at minimum exponent
      let e_min := min e1 e2
      let result_m := m1 * beta ^ Int.natAbs (e1 - e_min) +
                      m2 * beta ^ Int.natAbs (e2 - e_min)
      (result_m, e_min, Location.loc_Exact)

/-- The proposition stated by upstream `Fplus_correct`, exposed separately for
    clients that want to name the contract. -/
def Fplus_correct_obligation (x y : FlocqFloat beta) : Prop :=
  let result := Fplus beta fexp x y
  let m := result.1
  let e := result.2.1
  let l := result.2.2
  (l = Location.loc_Exact ∨ e ≤ cexp beta fexp ((F2R x) + (F2R y))) ∧
    inbetween_float beta m e ((F2R x) + (F2R y)) l

/-- Coq `Fplus_correct`: the returned exponent is canonical whenever the
    location is inexact, and the returned float brackets the exact sum. -/
theorem Fplus_correct (x y : FlocqFloat beta) :
    Fplus_correct_obligation beta fexp x y := by
  have hβ : 1 < beta := ValidRadix.valid
  rcases x with ⟨m1, e1⟩
  rcases y with ⟨m2, e2⟩
  by_cases hm1 : m1 = 0
  · subst m1
    have hresult : Fplus beta fexp
        (FlocqFloat.mk 0 e1) (FlocqFloat.mk m2 e2) =
        (m2, e2, Location.loc_Exact) := by simp [Fplus]
    rw [Fplus_correct_obligation, hresult]
    simp only [F2R, Int.cast_zero, zero_mul, zero_add]
    constructor
    · exact Or.inl trivial
    · unfold inbetween_float
      exact inbetween.inbetween_Exact rfl
  · by_cases hm2 : m2 = 0
    · subst m2
      have hresult : Fplus beta fexp
          (FlocqFloat.mk m1 e1) (FlocqFloat.mk 0 e2) =
          (m1, e1, Location.loc_Exact) := by simp [Fplus, hm1]
      rw [Fplus_correct_obligation, hresult]
      simp only [F2R, Int.cast_zero, zero_mul, add_zero]
      constructor
      · exact Or.inl trivial
      · unfold inbetween_float
        exact inbetween.inbetween_Exact rfl
    · let p1 : Int := Zdigits beta m1 + e1
      let p2 : Int := Zdigits beta m2 + e2
      by_cases hp : 2 ≤ Int.natAbs (p1 - p2)
      · let e : Int := min (max e1 e2) (fexp (max p1 p2 - 1))
        let z : ℝ := F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta) +
          F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)
        have hmag1 : FloatSpec.Core.Raux.mag beta
              (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)) = p1 := by
          simpa [p1] using
            (FloatSpec.Core.Float_prop.Raux_mag_F2R_Zdigits
              (beta := beta) m1 e1 hβ hm1)
        have hmag2 : FloatSpec.Core.Raux.mag beta
              (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)) = p2 := by
          simpa [p2] using
            (FloatSpec.Core.Float_prop.Raux_mag_F2R_Zdigits
              (beta := beta) m2 e2 hβ hm2)
        have hnz1 : F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta) ≠ 0 :=
          FloatSpec.Core.Float_prop.F2R_neq_0
            (beta := beta) (FlocqFloat.mk m1 e1) hβ hm1
        have hnz2 : F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta) ≠ 0 :=
          FloatSpec.Core.Float_prop.F2R_neq_0
            (beta := beta) (FlocqFloat.mk m2 e2) hβ hm2
        have hmag : max p1 p2 - 1 ≤ FloatSpec.Core.Raux.mag beta z := by
          rcases le_total p1 p2 with hp12 | hp21
          · have hpcast : (2 : Int) ≤ (Int.natAbs (p1 - p2) : Int) := by
              exact_mod_cast hp
            have habs : (Int.natAbs (p1 - p2) : Int) = p2 - p1 := by
              rw [Int.ofNat_natAbs_of_nonpos (sub_nonpos.mpr hp12)]
              omega
            have hsmall : p1 ≤ p2 - 2 := by omega
            have hsmall' : FloatSpec.Core.Raux.mag beta
                  (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)) ≤
                FloatSpec.Core.Raux.mag beta
                  (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)) - 2 := by
              rw [hmag1, hmag2]
              exact hsmall
            have htrip := FloatSpec.Core.Raux.mag_plus_ge beta
              (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta))
              (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta))
              hβ hnz2 hsmall'
            have hrun := htrip (by trivial)
            have : p2 - 1 ≤ FloatSpec.Core.Raux.mag beta z := by
              rw [hmag2] at hrun
              simpa [z, add_comm, wp, PostCond.noThrow, pure] using hrun
            simpa [max_eq_right hp12] using this
          · have hpcast : (2 : Int) ≤ (Int.natAbs (p1 - p2) : Int) := by
              exact_mod_cast hp
            have habs : (Int.natAbs (p1 - p2) : Int) = p1 - p2 := by
              rw [Int.natAbs_of_nonneg (sub_nonneg.mpr hp21)]
            have hsmall : p2 ≤ p1 - 2 := by omega
            have hsmall' : FloatSpec.Core.Raux.mag beta
                  (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)) ≤
                FloatSpec.Core.Raux.mag beta
                  (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)) - 2 := by
              rw [hmag1, hmag2]
              exact hsmall
            have htrip := FloatSpec.Core.Raux.mag_plus_ge beta
              (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta))
              (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta))
              hβ hnz1 hsmall'
            have hrun := htrip (by trivial)
            have : p1 - 1 ≤ FloatSpec.Core.Raux.mag beta z := by
              rw [hmag1] at hrun
              simpa [z, wp, PostCond.noThrow, pure] using hrun
            simpa [max_eq_left hp21] using this
        have he_cexp : e ≤ cexp beta fexp z := by
          apply le_trans (min_le_right _ _)
          exact Monotone_exp.mono hmag
        by_cases he1 : e1 < e
        · have he2 : e ≤ e2 := by
            dsimp [e]
            omega
          have hcore := Fplus_core_correct (beta := beta) m2 e2 m1 e1 e he2
          have hresult : Fplus beta fexp
              (FlocqFloat.mk m1 e1) (FlocqFloat.mk m2 e2) =
              let r := Fplus_core beta m2 e2 m1 e1 e
              (r.1, e, r.2) := by
            simp [Fplus, hm1, hm2, p1, p2, hp, e, he1]
          rw [Fplus_correct_obligation, hresult]
          simpa [z, add_comm] using And.intro (Or.inr he_cexp) hcore
        · have he1' : e ≤ e1 := by omega
          have hcore := Fplus_core_correct (beta := beta) m1 e1 m2 e2 e he1'
          have hresult : Fplus beta fexp
              (FlocqFloat.mk m1 e1) (FlocqFloat.mk m2 e2) =
              let r := Fplus_core beta m1 e1 m2 e2 e
              (r.1, e, r.2) := by
            simp [Fplus, hm1, hm2, p1, p2, hp, e, he1]
          rw [Fplus_correct_obligation, hresult]
          simpa [z] using And.intro (Or.inr he_cexp) hcore
      · let e : Int := min e1 e2
        have he1 : e ≤ e1 := min_le_left _ _
        have he2 : e ≤ e2 := min_le_right _ _
        have hs1 := F2R_scale_to_lower (beta := beta) m1 e1 e he1
        have hs2 := F2R_scale_to_lower (beta := beta) m2 e2 e he2
        simp only [Fplus_correct_obligation, Fplus, hm1, hm2, ite_false, p1, p2,
          hp, e]
        constructor
        · exact Or.inl trivial
        · apply inbetween.inbetween_Exact
          simp only [F2R, Int.cast_add, Int.cast_mul, Int.cast_pow]
          have hs1' : ((m1 : ℝ) * (beta : ℝ) ^ Int.natAbs (e1 - e)) *
              (beta : ℝ) ^ e = (m1 : ℝ) * (beta : ℝ) ^ e1 := by
            simpa [F2R, Int.cast_mul, Int.cast_pow] using hs1
          have hs2' : ((m2 : ℝ) * (beta : ℝ) ^ Int.natAbs (e2 - e)) *
              (beta : ℝ) ^ e = (m2 : ℝ) * (beta : ℝ) ^ e2 := by
            simpa [F2R, Int.cast_mul, Int.cast_pow] using hs2
          rw [← hs1', ← hs2']
          ring

end MainAddition

end FloatSpec.Calc.Plus
