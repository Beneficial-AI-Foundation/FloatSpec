/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4, ported from Coq: https://flocq.gitlabpages.inria.fr/

Basic operations on floats: alignment, addition, multiplication
Translated from Coq file: flocq/src/Calc/Operations.v
-/

import FloatSpec.src.Core.Zaux
import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Float_prop
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do
import FloatSpec.src.SimprocWP

open Real FloatSpec.Core.Defs
open Std.Do

namespace FloatSpec.Calc.Operations

variable (beta : Int)

section FloatAlignment

/-- Align two floats to the same exponent

    Adjusts mantissas of two floats so they share a common exponent,
    which is the minimum of the two original exponents. This enables
    direct mantissa operations while preserving values.
-/
def Falign (f1 f2 : FlocqFloat beta) : (Int × Int × Int) :=
  let m1 := f1.Fnum
  let e1 := f1.Fexp
  let m2 := f2.Fnum
  let e2 := f2.Fexp
  pure (if e1 ≤ e2 then
    (m1, m2 * beta ^ Int.natAbs (e2 - e1), e1)
  else
    (m1 * beta ^ Int.natAbs (e1 - e2), m2, e2))

/-- Specification: Alignment preserves float values

    After alignment, both floats maintain their original real values
    but are expressed with a common exponent
-/
@[spec]
theorem Falign_spec (f1 f2 : FlocqFloat beta) :
    ⦃⌜1 < beta⌝⦄
    Falign beta f1 f2
    ⦃⇓result => let (m1, m2, e) := result
                ⌜(F2R f1) = (F2R (FlocqFloat.mk m1 e : FlocqFloat beta)) ∧
                (F2R f2) = (F2R (FlocqFloat.mk m2 e : FlocqFloat beta))⌝⦄ := by
  intro hbeta
  -- Unfold Falign and simplify the wp goal
  unfold Falign
  simp only [pure, PostCond.noThrow, Id.run, F2R]
  -- Split cases based on which exponent is smaller
  by_cases hle : f1.Fexp ≤ f2.Fexp
  · -- Case: e1 ≤ e2, common exponent is e1
    simp only [hle, ite_true]
    have hbeta_pos : 1 < beta := hbeta
    have hpos : 0 < beta := lt_trans (by decide : (0:Int) < 1) hbeta_pos
    have hdiff_nonneg : 0 ≤ f2.Fexp - f1.Fexp := Int.sub_nonneg.mpr hle
    constructor
    · rfl  -- First float unchanged since we use its exponent
    · -- Second float: f2.Fnum * beta^e2 = (f2.Fnum * beta^(e2-e1)) * beta^e1
      -- Simplify tuple projection
      show (f2.Fnum : ℝ) * (beta : ℝ) ^ f2.Fexp =
           (f2.Fnum * beta ^ (f2.Fexp - f1.Fexp).natAbs : ℤ) * (beta : ℝ) ^ f1.Fexp
      have key : ((f2.Fexp - f1.Fexp).natAbs : ℤ) = f2.Fexp - f1.Fexp := Int.natAbs_of_nonneg hdiff_nonneg
      have hβne : (beta : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hpos : (0:ℝ) < beta)
      simp only [Int.cast_mul, Int.cast_pow]
      -- Convert Nat pow to zpow, then use the key to replace natAbs with the Int difference
      conv_rhs => rw [show (beta : ℝ) ^ (f2.Fexp - f1.Fexp).natAbs = (beta : ℝ) ^ (f2.Fexp - f1.Fexp) by
        rw [← zpow_natCast, key]]
      -- Now rhs is ↑f2.Fnum * ↑beta ^ (f2.Fexp - f1.Fexp) * ↑beta ^ f1.Fexp
      -- Reassociate and combine exponents
      rw [mul_assoc, ← zpow_add₀ hβne, sub_add_cancel]
  · -- Case: e1 > e2, common exponent is e2
    simp only [hle, ite_false]
    push_neg at hle
    have hbeta_pos : 1 < beta := hbeta
    have hpos : 0 < beta := lt_trans (by decide : (0:Int) < 1) hbeta_pos
    have hle' : f2.Fexp ≤ f1.Fexp := le_of_lt hle
    have hdiff_nonneg : 0 ≤ f1.Fexp - f2.Fexp := Int.sub_nonneg.mpr hle'
    constructor
    · -- First float: f1.Fnum * beta^e1 = (f1.Fnum * beta^(e1-e2)) * beta^e2
      show (f1.Fnum : ℝ) * (beta : ℝ) ^ f1.Fexp =
           (f1.Fnum * beta ^ (f1.Fexp - f2.Fexp).natAbs : ℤ) * (beta : ℝ) ^ f2.Fexp
      have key : ((f1.Fexp - f2.Fexp).natAbs : ℤ) = f1.Fexp - f2.Fexp := Int.natAbs_of_nonneg hdiff_nonneg
      have hβne : (beta : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hpos : (0:ℝ) < beta)
      simp only [Int.cast_mul, Int.cast_pow]
      -- Convert Nat pow to zpow, then use the key to replace natAbs with the Int difference
      conv_rhs => rw [show (beta : ℝ) ^ (f1.Fexp - f2.Fexp).natAbs = (beta : ℝ) ^ (f1.Fexp - f2.Fexp) by
        rw [← zpow_natCast, key]]
      -- Now rhs is ↑f1.Fnum * ↑beta ^ (f1.Fexp - f2.Fexp) * ↑beta ^ f2.Fexp
      -- Reassociate and combine exponents
      rw [mul_assoc, ← zpow_add₀ hβne, sub_add_cancel]
    · rfl  -- Second float unchanged since we use its exponent

/-- Extract aligned exponent

    Returns the common exponent after alignment
-/
def Falign_exp (f1 f2 : FlocqFloat beta) : Int :=
  Falign beta f1 f2 >>= fun (_, _, e) => pure e

/-- Specification: Aligned exponent is minimum

    The common exponent is the minimum of the two original exponents
-/
@[spec]
theorem Falign_spec_exp (f1 f2 : FlocqFloat beta) :
    ⦃⌜True⌝⦄
    Falign_exp beta f1 f2
    ⦃⇓result => ⌜result = min f1.Fexp f2.Fexp⌝⦄ := by
  intro _
  unfold Falign_exp
  cases f1 with
  | mk m1 e1 =>
    cases f2 with
    | mk m2 e2 =>
      by_cases hle : e1 ≤ e2
      · -- exponent chosen is e1, which is min when e1 ≤ e2
        simp [Falign, hle, pure, bind]
      · -- exponent chosen is e2, which is min when e2 ≤ e1
        have hle' : e2 ≤ e1 := le_of_lt (lt_of_not_ge hle)
        simp [Falign, hle, pure, bind, min_eq_right hle']

end FloatAlignment

section FloatNegation

/-- Negate a floating-point number

    Negation flips the sign of the mantissa while preserving the exponent
-/
def Fopp (f1 : FlocqFloat beta) : (FlocqFloat beta) :=
  (FlocqFloat.mk (-f1.Fnum) f1.Fexp)

/-- Specification: Negation produces arithmetic negative

    The real value of the negated float is the negative of the original
-/
theorem F2R_opp (f1 : FlocqFloat beta) :
    ⦃⌜True⌝⦄
    Fopp beta f1
    ⦃⇓result => ⌜(F2R result) = -((F2R f1))⌝⦄ := by
  intro _
  simp [Fopp, pure, F2R, neg_mul]

end FloatNegation

section FloatAbsoluteValue

/-- Compute absolute value of a float

    Takes the absolute value of the mantissa, keeping exponent unchanged
-/
def Fabs (f1 : FlocqFloat beta) : (FlocqFloat beta) :=
  (FlocqFloat.mk (Int.natAbs f1.Fnum) f1.Fexp)

/-- Specification: Absolute value is non-negative

    The real value of the absolute float is the absolute value of the original
-/
theorem F2R_abs (f1 : FlocqFloat beta) :
    ⦃⌜1 < beta⌝⦄
    Fabs beta f1
    ⦃⇓result => ⌜(F2R result) = |(F2R f1)|⌝⦄ := by
  intro hβ
  -- Evaluate both sides and reduce to an absolute-value algebraic identity
  simp [Fabs, pure, F2R]
  -- It suffices to show the base power is nonnegative, so |β^e| = β^e
  have hbposℤ : 0 < beta := lt_trans (by decide) hβ
  have hbposR : 0 < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbpow_nonneg : 0 ≤ (beta : ℝ) ^ f1.Fexp := le_of_lt (zpow_pos hbposR _)
  exact Or.inl (by simpa using (abs_of_nonneg hbpow_nonneg).symm)

end FloatAbsoluteValue

section FloatAddition

/-- Add two floating-point numbers

    Aligns the floats to a common exponent then adds their mantissas
-/
def Fplus (f1 f2 : FlocqFloat beta) : (FlocqFloat beta) :=
  Falign beta f1 f2 >>= fun (m1, m2, e) =>
  pure (FlocqFloat.mk (m1 + m2) e)

/-- Specification: Addition is arithmetically correct

    The real value of the sum equals the sum of the real values
-/
theorem F2R_plus (f1 f2 : FlocqFloat beta) :
    ⦃⌜1 < beta⌝⦄
    Fplus beta f1 f2
    ⦃⇓result => ⌜(F2R result) = (F2R f1) + (F2R f2)⌝⦄ := by
  intro hβ
  -- Unfold and case on alignment branch; then reduce arithmetically
  unfold Fplus
  cases f1 with
  | mk m1 e1 =>
    cases f2 with
    | mk m2 e2 =>
      -- Evaluate alignment depending on exponents
      by_cases hle : e1 ≤ e2
      · -- Aligned exponent is e1; second mantissa is scaled
        simp [Falign, hle, pure, bind, F2R, Int.cast_add,
          Int.cast_mul]
        -- Show scaling identity: b^(|e2-e1|) * b^e1 = b^e2
        set b : ℝ := (beta : ℝ)
        have hbposInt : (0 : Int) < beta := lt_trans (by decide) hβ
        have hbposReal : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposInt
        have hbpos : 0 < b := by simpa [b] using hbposReal
        have hbne : b ≠ 0 := ne_of_gt hbpos
        have hd_nonneg : 0 ≤ e2 - e1 := sub_nonneg.mpr hle
        have hofNat : ((Int.toNat (e2 - e1)) : Int) = e2 - e1 := by
          simpa using (Int.toNat_of_nonneg hd_nonneg)
        have hzpow_int : b ^ (e2 - e1) = b ^ ((Int.toNat (e2 - e1)) : Int) := by
          simpa using (congrArg (fun t : Int => b ^ t) hofNat.symm)
        have hzpow_nat : b ^ ((Int.toNat (e2 - e1)) : Int) = b ^ (Int.toNat (e2 - e1)) :=
          zpow_ofNat b (Int.toNat (e2 - e1))
        have hnat : (e2 - e1).natAbs = Int.toNat (e2 - e1) := by
          -- derive from cast equalities: natAbs_of_nonneg and toNat_of_nonneg
          apply Int.ofNat.inj
          have h1 : ((e2 - e1).natAbs : Int) = e2 - e1 := Int.natAbs_of_nonneg hd_nonneg
          have h2 : (Int.ofNat (Int.toNat (e2 - e1)) : Int) = e2 - e1 := Int.toNat_of_nonneg hd_nonneg
          simpa using h1.trans h2.symm
        have hscale : b ^ (Int.natAbs (e2 - e1)) * b ^ e1 = b ^ e2 := by
          calc
            b ^ (Int.natAbs (e2 - e1)) * b ^ e1
                = b ^ (Int.toNat (e2 - e1)) * b ^ e1 := by simpa [hnat]
            _   = b ^ (e2 - e1) * b ^ e1 := by
                  have hz : b ^ (Int.toNat (e2 - e1)) = b ^ (e2 - e1) :=
                    (hzpow_int.trans hzpow_nat).symm
                  simpa [hz]
            _   = b ^ (e2 - e1 + e1) := (zpow_add₀ hbne (e2 - e1) e1).symm
            _   = b ^ e2 := by simpa [sub_add_cancel]
        -- Finish by rewriting the scaled term with hscale
        -- algebraic rearrangement of the RHS to match LHS
        -- (m1 + m2 * b^(|e2-e1|)) * b^e1 = m1*b^e1 + m2*b^e2
        have : b ^ e1 * ((m1 : ℝ) + b ^ Int.natAbs (e2 - e1) * (m2 : ℝ))
              = b ^ e1 * (m1 : ℝ) + b ^ e2 * (m2 : ℝ) := by
          have := by
            calc
              b ^ e1 * ((m1 : ℝ) + b ^ Int.natAbs (e2 - e1) * (m2 : ℝ))
                  = b ^ e1 * (m1 : ℝ) + b ^ e1 * (b ^ Int.natAbs (e2 - e1) * (m2 : ℝ)) := by ring
              _ = b ^ e1 * (m1 : ℝ) + (b ^ Int.natAbs (e2 - e1) * b ^ e1) * (m2 : ℝ) := by ring
              _ = b ^ e1 * (m1 : ℝ) + b ^ e2 * (m2 : ℝ) := by simpa [hscale, mul_comm, mul_left_comm, mul_assoc]
          simpa [mul_add, mul_comm, mul_left_comm, mul_assoc] using this
        simpa [this, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      · -- Symmetric case: aligned exponent is e2; first mantissa is scaled
        have hle' : e2 ≤ e1 := le_of_lt (lt_of_not_ge hle)
        simp [Falign, hle, pure, bind, F2R, Int.cast_add,
          Int.cast_mul, add_comm]
        set b : ℝ := (beta : ℝ)
        have hbposInt : (0 : Int) < beta := lt_trans (by decide) hβ
        have hbposReal : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposInt
        have hbpos : 0 < b := by simpa [b] using hbposReal
        have hbne : b ≠ 0 := ne_of_gt hbpos
        have hd_nonneg : 0 ≤ e1 - e2 := sub_nonneg.mpr hle'
        have hofNat : ((Int.toNat (e1 - e2)) : Int) = e1 - e2 := by
          simpa using (Int.toNat_of_nonneg hd_nonneg)
        have hzpow_int : b ^ (e1 - e2) = b ^ ((Int.toNat (e1 - e2)) : Int) := by
          simpa using (congrArg (fun t : Int => b ^ t) hofNat.symm)
        have hzpow_nat : b ^ ((Int.toNat (e1 - e2)) : Int) = b ^ (Int.toNat (e1 - e2)) :=
          zpow_ofNat b (Int.toNat (e1 - e2))
        have hnat : (e1 - e2).natAbs = Int.toNat (e1 - e2) := by
          apply Int.ofNat.inj
          have h1 : ((e1 - e2).natAbs : Int) = e1 - e2 := Int.natAbs_of_nonneg hd_nonneg
          have h2 : (Int.ofNat (Int.toNat (e1 - e2)) : Int) = e1 - e2 := Int.toNat_of_nonneg hd_nonneg
          simpa using h1.trans h2.symm
        have hscale : b ^ (Int.natAbs (e1 - e2)) * b ^ e2 = b ^ e1 := by
          calc
            b ^ (Int.natAbs (e1 - e2)) * b ^ e2
                = b ^ (Int.toNat (e1 - e2)) * b ^ e2 := by simpa [hnat]
            _   = b ^ (e1 - e2) * b ^ e2 := by
                  have hz : b ^ (Int.toNat (e1 - e2)) = b ^ (e1 - e2) :=
                    (hzpow_int.trans hzpow_nat).symm
                  simpa [hz]
            _   = b ^ (e1 - e2 + e2) := (zpow_add₀ hbne (e1 - e2) e2).symm
            _   = b ^ e1 := by simpa [sub_add_cancel]
        have : b ^ e2 * ((m2 : ℝ) + b ^ Int.natAbs (e1 - e2) * (m1 : ℝ))
              = b ^ e2 * (m2 : ℝ) + b ^ e1 * (m1 : ℝ) := by
          have := by
            calc
              b ^ e2 * ((m2 : ℝ) + b ^ Int.natAbs (e1 - e2) * (m1 : ℝ))
                  = b ^ e2 * (m2 : ℝ) + b ^ e2 * (b ^ Int.natAbs (e1 - e2) * (m1 : ℝ)) := by ring
              _ = b ^ e2 * (m2 : ℝ) + (b ^ Int.natAbs (e1 - e2) * b ^ e2) * (m1 : ℝ) := by ring
              _ = b ^ e2 * (m2 : ℝ) + b ^ e1 * (m1 : ℝ) := by simpa [hscale, mul_comm, mul_left_comm, mul_assoc]
          simpa [mul_add, mul_comm, mul_left_comm, mul_assoc] using this
        simpa [this, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

/-- Add floats with same exponent

    Direct mantissa addition when exponents match
-/
def Fplus_same_exp (m1 m2 e : Int) : (FlocqFloat beta) :=
  Fplus beta (FlocqFloat.mk m1 e) (FlocqFloat.mk m2 e)

/-- Specification: Same-exponent addition

    Adding floats with identical exponents just adds mantissas
-/
@[spec]
theorem Fplus_same_exp_spec (m1 m2 e : Int) :
    ⦃⌜True⌝⦄
    Fplus_same_exp beta m1 m2 e
    ⦃⇓result => ⌜result = FlocqFloat.mk (m1 + m2) e⌝⦄ := by
  intro _
  unfold Fplus_same_exp Fplus
  -- With equal exponents, alignment keeps mantissas unchanged
  simp [Falign, pure, bind, Int.natAbs_zero, pow_zero, mul_one]

/-- Extract exponent of sum

    Returns the exponent of the sum of two floats
-/
def Fexp_Fplus (f1 f2 : FlocqFloat beta) : Int :=
  Fplus beta f1 f2 >>= fun f => pure f.Fexp

/-- Specification: Sum exponent is minimum

    The exponent of a sum is the minimum of the input exponents
-/
@[spec]
theorem Fexp_Fplus_spec (f1 f2 : FlocqFloat beta) :
    ⦃⌜True⌝⦄
    Fexp_Fplus beta f1 f2
    ⦃⇓result => ⌜result = min f1.Fexp f2.Fexp⌝⦄ := by
  intro _
  unfold Fexp_Fplus Fplus
  cases f1 with
  | mk m1 e1 =>
    cases f2 with
    | mk m2 e2 =>
      by_cases hle : e1 ≤ e2
      · -- exponent chosen is e1, which is min when e1 ≤ e2
        simp [Falign, hle, pure, bind]
      · -- exponent chosen is e2, which is min when e2 ≤ e1
        have hle' : e2 ≤ e1 := le_of_lt (lt_of_not_ge hle)
        simp [Falign, hle, pure, bind, min_eq_right hle']

end FloatAddition

section FloatSubtraction

/-- Subtract two floating-point numbers

    Subtraction is addition of the negation
-/
def Fminus (f1 f2 : FlocqFloat beta) : (FlocqFloat beta) :=
  Fopp beta f2 >>= fun neg_f2 =>
  Fplus beta f1 neg_f2

/-- Specification: Subtraction is arithmetically correct

    The real value of the difference equals the difference of real values
-/
theorem F2R_minus (f1 f2 : FlocqFloat beta) :
    ⦃⌜1 < beta⌝⦄
    Fminus beta f1 f2
    ⦃⇓result => ⌜(F2R result) = (F2R f1) - (F2R f2)⌝⦄ := by
  intro hβ
  -- Unfold subtraction as addition of the negation, then reduce arithmetically
  unfold Fminus
  cases f1 with
  | mk m1 e1 =>
    cases f2 with
    | mk m2 e2 =>
      -- After negation, alignment is identical to addition, with the second mantissa negated
      by_cases hle : e1 ≤ e2
      · -- Aligned exponent is e1; the second mantissa becomes scaled and negated
        simp [Fopp, Falign, hle, Fplus, pure, bind, F2R, Int.cast_add,
          Int.cast_mul, Int.cast_neg, sub_eq_add_neg, neg_mul]
        -- Reuse the same scaling identity as in F2R_plus
        set b : ℝ := (beta : ℝ)
        have hbposInt : (0 : Int) < beta := lt_trans (by decide) hβ
        have hbposReal : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposInt
        have hbpos : 0 < b := by simpa [b] using hbposReal
        have hbne : b ≠ 0 := ne_of_gt hbpos
        have hd_nonneg : 0 ≤ e2 - e1 := sub_nonneg.mpr hle
        have hofNat : ((Int.toNat (e2 - e1)) : Int) = e2 - e1 := by
          simpa using (Int.toNat_of_nonneg hd_nonneg)
        have hzpow_int : b ^ (e2 - e1) = b ^ ((Int.toNat (e2 - e1)) : Int) := by
          simpa using (congrArg (fun t : Int => b ^ t) hofNat.symm)
        have hzpow_nat : b ^ ((Int.toNat (e2 - e1)) : Int) = b ^ (Int.toNat (e2 - e1)) :=
          zpow_ofNat b (Int.toNat (e2 - e1))
        have hnat : (e2 - e1).natAbs = Int.toNat (e2 - e1) := by
          apply Int.ofNat.inj
          have h1 : ((e2 - e1).natAbs : Int) = e2 - e1 := Int.natAbs_of_nonneg hd_nonneg
          have h2 : (Int.ofNat (Int.toNat (e2 - e1)) : Int) = e2 - e1 := Int.toNat_of_nonneg hd_nonneg
          simpa using h1.trans h2.symm
        have hscale : b ^ (Int.natAbs (e2 - e1)) * b ^ e1 = b ^ e2 := by
          calc
            b ^ (Int.natAbs (e2 - e1)) * b ^ e1
                = b ^ (Int.toNat (e2 - e1)) * b ^ e1 := by simpa [hnat]
            _   = b ^ (e2 - e1) * b ^ e1 := by
                  have hz : b ^ (Int.toNat (e2 - e1)) = b ^ (e2 - e1) :=
                    (hzpow_int.trans hzpow_nat).symm
                  simpa [hz]
            _   = b ^ (e2 - e1 + e1) := (zpow_add₀ hbne (e2 - e1) e1).symm
            _   = b ^ e2 := by simpa [sub_add_cancel]
        -- Now rewrite the right-hand side using hscale and conclude
        have : b ^ e1 * ((m1 : ℝ) + b ^ Int.natAbs (e2 - e1) * (-(m2 : ℝ)))
              = b ^ e1 * (m1 : ℝ) - b ^ e2 * (m2 : ℝ) := by
          have := by
            calc
              b ^ e1 * ((m1 : ℝ) + b ^ Int.natAbs (e2 - e1) * (-(m2 : ℝ)))
                  = b ^ e1 * (m1 : ℝ) + b ^ e1 * (b ^ Int.natAbs (e2 - e1) * (-(m2 : ℝ))) := by ring
              _ = b ^ e1 * (m1 : ℝ) + (b ^ Int.natAbs (e2 - e1) * b ^ e1) * (-(m2 : ℝ)) := by ring
              _ = b ^ e1 * (m1 : ℝ) + b ^ e2 * (-(m2 : ℝ)) := by simpa [hscale, mul_comm, mul_left_comm, mul_assoc]
              _ = b ^ e1 * (m1 : ℝ) - b ^ e2 * (m2 : ℝ) := by ring
          simpa [mul_add, mul_comm, mul_left_comm, mul_assoc] using this
        simpa [this, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
               mul_comm, mul_left_comm, mul_assoc]
      · -- Symmetric case: aligned exponent is e2; the first mantissa is scaled
        have hle' : e2 ≤ e1 := le_of_lt (lt_of_not_ge hle)
        simp [Fopp, Falign, hle, Fplus, pure, bind, F2R, Int.cast_add,
          Int.cast_mul, Int.cast_neg, sub_eq_add_neg, add_comm]
        set b : ℝ := (beta : ℝ)
        have hbposInt : (0 : Int) < beta := lt_trans (by decide) hβ
        have hbposReal : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposInt
        have hbpos : 0 < b := by simpa [b] using hbposReal
        have hbne : b ≠ 0 := ne_of_gt hbpos
        have hd_nonneg : 0 ≤ e1 - e2 := sub_nonneg.mpr hle'
        have hofNat : ((Int.toNat (e1 - e2)) : Int) = e1 - e2 := by
          simpa using (Int.toNat_of_nonneg hd_nonneg)
        have hzpow_int : b ^ (e1 - e2) = b ^ ((Int.toNat (e1 - e2)) : Int) := by
          simpa using (congrArg (fun t : Int => b ^ t) hofNat.symm)
        have hzpow_nat : b ^ ((Int.toNat (e1 - e2)) : Int) = b ^ (Int.toNat (e1 - e2)) :=
          zpow_ofNat b (Int.toNat (e1 - e2))
        have hnat : (e1 - e2).natAbs = Int.toNat (e1 - e2) := by
          apply Int.ofNat.inj
          have h1 : ((e1 - e2).natAbs : Int) = e1 - e2 := Int.natAbs_of_nonneg hd_nonneg
          have h2 : (Int.ofNat (Int.toNat (e1 - e2)) : Int) = e1 - e2 := Int.toNat_of_nonneg hd_nonneg
          simpa using h1.trans h2.symm
        have hscale : b ^ (Int.natAbs (e1 - e2)) * b ^ e2 = b ^ e1 := by
          calc
            b ^ (Int.natAbs (e1 - e2)) * b ^ e2
                = b ^ (Int.toNat (e1 - e2)) * b ^ e2 := by simpa [hnat]
            _   = b ^ (e1 - e2) * b ^ e2 := by
                  have hz : b ^ (Int.toNat (e1 - e2)) = b ^ (e1 - e2) :=
                    (hzpow_int.trans hzpow_nat).symm
                  simpa [hz]
            _   = b ^ (e1 - e2 + e2) := (zpow_add₀ hbne (e1 - e2) e2).symm
            _   = b ^ e1 := by simpa [sub_add_cancel]
        have : b ^ e2 * ((-(m2 : ℝ)) + b ^ Int.natAbs (e1 - e2) * (m1 : ℝ))
              = - (b ^ e2 * (m2 : ℝ)) + b ^ e1 * (m1 : ℝ) := by
          have := by
            calc
              b ^ e2 * ((-(m2 : ℝ)) + b ^ Int.natAbs (e1 - e2) * (m1 : ℝ))
                  = b ^ e2 * (-(m2 : ℝ)) + b ^ e2 * (b ^ Int.natAbs (e1 - e2) * (m1 : ℝ)) := by ring
              _ = - (b ^ e2 * (m2 : ℝ)) + (b ^ Int.natAbs (e1 - e2) * b ^ e2) * (m1 : ℝ) := by ring
              _ = - (b ^ e2 * (m2 : ℝ)) + b ^ e1 * (m1 : ℝ) := by simpa [hscale, mul_comm, mul_left_comm, mul_assoc]
          simpa [mul_add, mul_comm, mul_left_comm, mul_assoc] using this
        simpa [this, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
               mul_comm, mul_left_comm, mul_assoc]

/-- Subtract floats with same exponent

    Direct mantissa subtraction when exponents match
-/
def Fminus_same_exp (m1 m2 e : Int) : (FlocqFloat beta) :=
  Fminus beta (FlocqFloat.mk m1 e) (FlocqFloat.mk m2 e)

/-- Specification: Same-exponent subtraction

    Subtracting floats with identical exponents just subtracts mantissas
-/
@[spec]
theorem Fminus_same_exp_spec (m1 m2 e : Int) :
    ⦃⌜True⌝⦄
    Fminus_same_exp beta m1 m2 e
    ⦃⇓result => ⌜result = FlocqFloat.mk (m1 - m2) e⌝⦄ := by
  intro _
  unfold Fminus_same_exp Fminus Fplus
  -- With equal exponents, alignment keeps mantissas unchanged; then apply negation
  simp [Fopp, Falign, pure, bind, Int.natAbs_zero, pow_zero, mul_one,
    sub_eq_add_neg]

end FloatSubtraction

section FloatMultiplication

/-- Multiply two floating-point numbers

    Multiplication multiplies mantissas and adds exponents
-/
def Fmult (f1 f2 : FlocqFloat beta) : (FlocqFloat beta) :=
  (FlocqFloat.mk (f1.Fnum * f2.Fnum) (f1.Fexp + f2.Fexp))

/-- Specification: Multiplication is arithmetically correct

    The real value of the product equals the product of real values
-/
theorem F2R_mult (f1 f2 : FlocqFloat beta) :
    ⦃⌜1 < beta⌝⦄
    Fmult beta f1 f2
    ⦃⇓result => ⌜(F2R result) = (F2R f1) * (F2R f2)⌝⦄ := by
  intro hβ
  -- Evaluate both sides and reduce to algebraic identities on ℝ
  simp [Fmult, pure, F2R, Int.cast_mul]
  -- Set base and obtain non-zeroness to use zpow_add₀
  set b : ℝ := (beta : ℝ)
  have hbposInt : (0 : Int) < beta := lt_trans (by decide) hβ
  have hbposReal : 0 < (beta : ℝ) := by exact_mod_cast hbposInt
  have hbpos : 0 < b := by simpa [b] using hbposReal
  have hbne : b ≠ 0 := ne_of_gt hbpos
  -- Use exponent addition rule for integer powers
  have hz : b ^ (f1.Fexp + f2.Fexp) = b ^ f1.Fexp * b ^ f2.Fexp :=
    zpow_add₀ hbne _ _
  -- Finish by straightforward rearrangement
  simpa [b, hz, mul_comm, mul_left_comm, mul_assoc]

end FloatMultiplication

end FloatSpec.Calc.Operations
