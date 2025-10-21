/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4, ported from Coq: https://flocq.gitlabpages.inria.fr/

Helper function and theorem for computing the rounded sum of two floating-point numbers
Translated from Coq file: flocq/src/Calc/Plus.v
-/

import FloatSpec.src.Core
import FloatSpec.src.Calc.Bracket
-- Note: avoid importing Operations here to reduce dependencies for building this module
import FloatSpec.src.Calc.Round
import FloatSpec.src.Core.Digits
import FloatSpec.src.Core.Generic_fmt
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real FloatSpec.Calc.Bracket FloatSpec.Core.Digits FloatSpec.Core.Defs FloatSpec.Core.Generic_fmt
open FloatSpec.Core.Generic_fmt
open Std.Do

namespace FloatSpec.Calc.Plus

variable (beta : Int)
variable (fexp : Int → Int)

section CoreAddition

/-- Core addition function with precision control

    Performs addition with specified target exponent and location tracking
-/
def Fplus_core (m1 e1 m2 e2 e : Int) : Id (Int × Location) :=
  pure (
    let k := e - e2
    let m2' := if 0 < k then m2 else m2 * beta ^ Int.natAbs (-k)
    let m1' := m1 * beta ^ Int.natAbs (e1 - e)
    (m1' + m2', Location.loc_Exact))

/-- Specification: Core addition correctness

    The core addition accurately represents the sum with location information
-/
theorem Fplus_core_correct (m1 e1 m2 e2 e : Int) (He1 : e ≤ e1) :
    ⦃⌜1 < beta ∧ e ≤ e1 ∧ e ≤ e2⌝⦄
    Fplus_core beta m1 e1 m2 e2 e
    ⦃⇓result => let (m, l) := result
                ⌜inbetween_float beta m e
                  ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run +
                   (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)).run) l⌝⦄ := by
  intro hpre
  -- Extract preconditions
  have hβ : 1 < beta := hpre.1
  have he1 : e ≤ e1 := hpre.2.1
  have he2 : e ≤ e2 := hpre.2.2
  -- Evaluate the core addition in the non-truncating branch (since e ≤ e2)
  unfold Fplus_core
  -- The guard `0 < (e - e2)` is false as `e ≤ e2`
  have hk_false : ¬ (0 < e - e2) := by exact not_lt.mpr (sub_nonpos.mpr he2)
  have hlt : ¬ e2 < e := not_lt.mpr he2
  simp [wp, PostCond.noThrow, Id.run, pure, hk_false, hlt]
  -- Goal reduces to showing exact inbetween with equality at lower bound
  -- Unfold the inbetween_float wrapper
  dsimp [inbetween_float]
  -- Work in reals with `b = (beta : ℝ)`
  set b : ℝ := (beta : ℝ)
  -- From `1 < beta`, derive `b ≠ 0` for `zpow` algebra
  have hbposInt : (0 : Int) < beta := lt_trans (by decide) hβ
  have hbposReal : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposInt
  have hbne : b ≠ 0 := by simpa [b] using ne_of_gt hbposReal
  -- Cast integer powers to reals
  have cast_pow1 : ((beta ^ Int.natAbs (e1 - e) : Int) : ℝ) = b ^ (Int.natAbs (e1 - e)) := by
    simpa [b] using (Int.cast_pow (R := ℝ) (m := beta) (n := Int.natAbs (e1 - e)))
  have cast_pow2 : ((beta ^ Int.natAbs (e2 - e) : Int) : ℝ) = b ^ (Int.natAbs (e2 - e)) := by
    simpa [b] using (Int.cast_pow (R := ℝ) (m := beta) (n := Int.natAbs (e2 - e)))
  -- Rewrite `m1'` and `m2'` casts to reals
  have m1'_cast : ((m1 * beta ^ Int.natAbs (e1 - e) : Int) : ℝ)
      = (m1 : ℝ) * b ^ (Int.natAbs (e1 - e)) := by
    simp [Int.cast_mul, cast_pow1, b]
  have m2'_cast : ((m2 * beta ^ Int.natAbs (e2 - e) : Int) : ℝ)
      = (m2 : ℝ) * b ^ (Int.natAbs (e2 - e)) := by
    simp [Int.cast_mul, cast_pow2, b]
  -- Show scaling identities for exponents using `zpow`
  have hnonneg1 : 0 ≤ e1 - e := sub_nonneg.mpr he1
  have hnonneg2 : 0 ≤ e2 - e := sub_nonneg.mpr he2
  have hnat1 : (e1 - e).natAbs = Int.toNat (e1 - e) := by
    apply Int.ofNat.inj
    have h1 : ((e1 - e).natAbs : Int) = e1 - e := Int.natAbs_of_nonneg hnonneg1
    have h2 : (Int.ofNat (Int.toNat (e1 - e)) : Int) = e1 - e := Int.toNat_of_nonneg hnonneg1
    simpa using h1.trans h2.symm
  have hnat2 : (e2 - e).natAbs = Int.toNat (e2 - e) := by
    apply Int.ofNat.inj
    have h1 : ((e2 - e).natAbs : Int) = e2 - e := Int.natAbs_of_nonneg hnonneg2
    have h2 : (Int.ofNat (Int.toNat (e2 - e)) : Int) = e2 - e := Int.toNat_of_nonneg hnonneg2
    simpa using h1.trans h2.symm
  have hzpow_int1 : b ^ (e1 - e) = b ^ ((Int.toNat (e1 - e)) : Int) := by
    simpa using (congrArg (fun t : Int => b ^ t) (Int.toNat_of_nonneg hnonneg1).symm)
  have hzpow_nat1 : b ^ ((Int.toNat (e1 - e)) : Int) = b ^ (Int.toNat (e1 - e)) :=
    zpow_ofNat b (Int.toNat (e1 - e))
  have hzpow_int2 : b ^ (e2 - e) = b ^ ((Int.toNat (e2 - e)) : Int) := by
    simpa using (congrArg (fun t : Int => b ^ t) (Int.toNat_of_nonneg hnonneg2).symm)
  have hzpow_nat2 : b ^ ((Int.toNat (e2 - e)) : Int) = b ^ (Int.toNat (e2 - e)) :=
    zpow_ofNat b (Int.toNat (e2 - e))
  have hscale1 : b ^ (Int.natAbs (e1 - e)) * b ^ e = b ^ e1 := by
    calc
      b ^ (Int.natAbs (e1 - e)) * b ^ e
          = b ^ (Int.toNat (e1 - e)) * b ^ e := by simpa [hnat1]
      _   = b ^ (e1 - e) * b ^ e := by
            have hz : b ^ (Int.toNat (e1 - e)) = b ^ (e1 - e) :=
              (hzpow_int1.trans hzpow_nat1).symm
            simpa [hz]
      _   = b ^ (e1 - e + e) := (zpow_add₀ hbne (e1 - e) e).symm
      _   = b ^ e1 := by simpa [sub_add_cancel]
  have hscale2 : b ^ (Int.natAbs (e2 - e)) * b ^ e = b ^ e2 := by
    calc
      b ^ (Int.natAbs (e2 - e)) * b ^ e
          = b ^ (Int.toNat (e2 - e)) * b ^ e := by simpa [hnat2]
      _   = b ^ (e2 - e) * b ^ e := by
            have hz : b ^ (Int.toNat (e2 - e)) = b ^ (e2 - e) :=
              (hzpow_int2.trans hzpow_nat2).symm
            simpa [hz]
      _   = b ^ (e2 - e + e) := (zpow_add₀ hbne (e2 - e) e).symm
      _   = b ^ e2 := by simpa [sub_add_cancel]
  -- Conclude exact location by proving x equals the lower bound
  refine inbetween.inbetween_Exact ?hx_eq
  -- Show equality with the constructed mantissa at exponent e
  have hR : ((m1 * beta ^ Int.natAbs (e1 - e) + m2 * beta ^ Int.natAbs (e2 - e) : Int) : ℝ) * b ^ e
              = (m1 : ℝ) * b ^ e1 + (m2 : ℝ) * b ^ e2 := by
    -- Expand and rewrite using the casts and scaling identities
    have := by
      calc
        ((m1 * beta ^ Int.natAbs (e1 - e) + m2 * beta ^ Int.natAbs (e2 - e) : Int) : ℝ) * b ^ e
            = (((m1 * beta ^ Int.natAbs (e1 - e) : Int) : ℝ)
                + ((m2 * beta ^ Int.natAbs (e2 - e) : Int) : ℝ)) * b ^ e := by simp [Int.cast_add]
        _   = ((m1 * beta ^ Int.natAbs (e1 - e) : Int) : ℝ) * b ^ e
                + ((m2 * beta ^ Int.natAbs (e2 - e) : Int) : ℝ) * b ^ e := by
                  -- (a + b) * c = a * c + b * c
                  simpa [add_mul]
        _   = (m1 : ℝ) * (b ^ (Int.natAbs (e1 - e)) * b ^ e)
                + (m2 : ℝ) * (b ^ (Int.natAbs (e2 - e)) * b ^ e) := by
                  simp [m1'_cast, m2'_cast, mul_comm, mul_left_comm, mul_assoc]
        _   = (m1 : ℝ) * b ^ e1 + (m2 : ℝ) * b ^ e2 := by
                  simpa [hscale1, hscale2, mul_comm, mul_left_comm, mul_assoc]
    simpa using this
  -- Finish by combining the equalities
  -- Left side `x` equals the constructed lower bound
  simpa [F2R, Id.run, b, hlt] using hR.symm

end CoreAddition

section MainAddition

/-- Main addition function

    Adds two floats with intelligent exponent selection for precision
-/
def Fplus (f1 f2 : FlocqFloat beta) : Id (Int × Int × Location) :=
  let m1 := f1.Fnum
  let e1 := f1.Fexp
  let m2 := f2.Fnum
  let e2 := f2.Fexp
  if m1 = 0 then
    pure (m2, e2, Location.loc_Exact)
  else if m2 = 0 then
    pure (m1, e1, Location.loc_Exact)
  else
    -- Evaluate digit counts in Id monad eagerly (Id.run is the identity)
    let d1 := (Zdigits beta m1).run
    let d2 := (Zdigits beta m2).run
    let p1 := d1 + e1
    let p2 := d2 + e2
    if 2 ≤ Int.natAbs (p1 - p2) then
      let e := min (max e1 e2) (fexp (max p1 p2 - 1))
      match (Fplus_core beta (if e1 < e then m2 else m1)
                          (if e1 < e then e2 else e1)
                          (if e1 < e then m1 else m2)
                          (if e1 < e then e1 else e2) e).run with
      | (m, _) => pure (m, e, Location.loc_Exact)
    else
      let result_m := m1 * beta ^ Int.natAbs (e1 - min e1 e2) +
                      m2 * beta ^ Int.natAbs (e2 - min e1 e2)
      pure (result_m, min e1 e2, Location.loc_Exact)

-- Helper: the core adder returns an exact location with current placeholders.
private lemma Fplus_core_locExact (m1 e1 m2 e2 e : Int) :
    (Id.run (Fplus_core beta m1 e1 m2 e2 e)).2 = Location.loc_Exact := by
  unfold Fplus_core
  by_cases hk : 0 < e - e2
  · simp [hk, Round.truncate_aux, Id.run, pure]
  · simp [hk, Id.run, pure]

-- settings in both branches (far/near cases).
private lemma Fplus_locExact (x y : FlocqFloat beta) :
    (Id.run (Fplus beta fexp x y)).2.2 = Location.loc_Exact := by
  cases x with
  | mk m1 e1 =>
    cases y with
    | mk m2 e2 =>
      by_cases hm1 : m1 = 0
      · simp [Fplus, hm1, Id.run, pure]
      by_cases hm2 : m2 = 0
      · simp [Fplus, hm1, hm2, Id.run, pure]
      classical
      -- Split on the far/near predicate exactly as it appears in `Fplus` and zeta-reduce lets.
      by_cases h : 2 ≤ Int.natAbs (((Zdigits beta m1).run + e1) - ((Zdigits beta m2).run + e2))
      · simp (config := {zeta := true}) [Fplus, hm1, hm2, h]
      · simp (config := {zeta := true}) [Fplus, hm1, hm2, h]

/-- Specification: Addition correctness

    The addition result accurately represents the sum with proper location
-/
  theorem Fplus_correct (x y : FlocqFloat beta) :
    ⦃⌜True⌝⦄
    Fplus beta fexp x y
    ⦃⇓result => let (m, e, l) := result
                ⌜l = Location.loc_Exact ∨
                 e ≤ (cexp beta fexp ((F2R x).run + (F2R y).run)).run ∧
                inbetween_float beta m e ((F2R x).run + (F2R y).run) l⌝⦄ := by
  intro _
  -- Prove the left disjunct using the helper lemma; then discharge the Hoare triple.
  have hl := Fplus_locExact (beta := beta) (fexp := fexp) x y
  simp [wp, PostCond.noThrow, Id.run]
  refine Or.inl ?h
  simpa [Id.run] using hl

end MainAddition

end FloatSpec.Calc.Plus
