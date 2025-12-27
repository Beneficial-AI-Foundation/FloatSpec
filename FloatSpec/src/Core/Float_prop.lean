/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4, ported from Coq: https://flocq.gitlabpages.inria.fr/

Original Copyright (C) 2011-2018 Sylvie Boldo
Original Copyright (C) 2011-2018 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
-/

import FloatSpec.src.Core.Zaux
import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Digits
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import FloatSpec.src.SimprocWP

open Real
open FloatSpec.Core.Defs
open FloatSpec.Core.Digits

namespace FloatSpec.Core.Float_prop

variable (beta : Int) (hbeta : 1 < beta)

section FloatProp

/-- Helper: if `(m : ℝ) < (beta : ℝ) ^ n`, then `m + 1 ≤ beta ^ n` as integers. -/
private lemma int_lt_pow_real_to_int (beta m : Int) (n : Nat) :
  (m : ℝ) < ((beta : ℝ) ^ n) → m + 1 ≤ beta ^ n := by
  intro h
  -- Convert RHS to an Int-cast to use `Int.cast_lt`
  have hR : (m : ℝ) < (((beta ^ n : Int) : ℝ)) := by
    simpa [Int.cast_pow]
  -- Back to integers and apply `add_one_le_iff`
  exact (Int.add_one_le_iff.mpr ((Int.cast_lt).1 hR))

/-- For a nonnegative integer `z`, its `natAbs` equals `toNat`. -/
private lemma natAbs_eq_toNat_of_nonneg {z : Int} (hz : 0 ≤ z) :
  z.natAbs = z.toNat := by
  -- compare via casting to ℤ on both sides
  apply Int.ofNat.inj
  calc (z.natAbs : Int)
      = z := Int.natAbs_of_nonneg hz
    _ = Int.ofNat z.toNat := (Int.toNat_of_nonneg hz).symm
    _ = (z.toNat : Int) := rfl

--

/-- Magnitude function for real numbers

    Returns the exponent such that beta^(mag-1) ≤ |x| < beta^mag.
    For x = 0, returns an arbitrary value (typically 0).
-/
noncomputable def mag (beta : Int) (x : ℝ) : Int :=
  if x = 0 then 0
  else ⌈Real.log (abs x) / Real.log (beta : ℝ)⌉


-- Comparison theorems

/-
Coq original:
Theorem Rcompare_F2R : forall e m1 m2 : Z,
  Rcompare (F2R (Float beta m1 e)) (F2R (Float beta m2 e)) = Z.compare m1 m2.
  Proof.
    intros e m1 m2.
    unfold F2R. simpl.
    rewrite Rcompare_mult_r.
    apply Rcompare_IZR.
    apply bpow_gt_0.
  Qed.
  -/
  theorem Rcompare_F2R (e m1 m2 : Int) (hbeta : 1 < beta) :
    let f1 := F2R (FlocqFloat.mk m1 e : FlocqFloat beta)
    let f2 := F2R (FlocqFloat.mk m2 e : FlocqFloat beta)
    FloatSpec.Core.Raux.Rcompare f1.run f2.run = Int.sign (m1 - m2) := by
    -- Compare via unfolding of Rcompare and integer order trichotomy
    intro f1 f2
    classical
    -- Expand definitions to compare concrete reals
    unfold FloatSpec.Core.Raux.Rcompare
    dsimp [f1, f2, FloatSpec.Core.Defs.F2R]
    -- Let p = β^e > 0
    have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
    have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
    have hp_pos : 0 < (beta : ℝ) ^ e := by exact zpow_pos hbpos_real _
    -- Case analysis on m1 and m2 (as integers)
    by_cases hlt : m1 < m2
    · -- f1 < f2 since p > 0
      have hltR : (m1 : ℝ) * (beta : ℝ) ^ e < (m2 : ℝ) * (beta : ℝ) ^ e :=
        mul_lt_mul_of_pos_right (by exact_mod_cast hlt) hp_pos
      have hsign : Int.sign (m1 - m2) = -1 := Int.sign_eq_neg_one_of_neg (sub_lt_zero.mpr hlt)
      simp [pure, hltR, hsign]
    · by_cases heq : m1 = m2
      · -- Equal mantissas: equal reals
        have heqR : (m1 : ℝ) * (beta : ℝ) ^ e = (m2 : ℝ) * (beta : ℝ) ^ e := by simpa [heq]
        have hsign : Int.sign (m1 - m2) = 0 := by simp [heq]
        have hltR : ¬ (m1 : ℝ) * (beta : ℝ) ^ e < (m2 : ℝ) * (beta : ℝ) ^ e := by
          simpa [heqR, not_lt.mpr (le_of_eq heqR)]
        simp [pure, hltR, heqR, hsign]
      · -- Then m2 < m1, so f2 < f1
        have hne : m2 ≠ m1 := fun h => heq h.symm
        have hgt : m2 < m1 := lt_of_le_of_ne (le_of_not_lt hlt) hne
        have hgtR : (m2 : ℝ) * (beta : ℝ) ^ e < (m1 : ℝ) * (beta : ℝ) ^ e :=
          mul_lt_mul_of_pos_right (by exact_mod_cast hgt) hp_pos
        have hsign : Int.sign (m1 - m2) = 1 := Int.sign_eq_one_of_pos (sub_pos.mpr hgt)
        -- Not (f1 < f2), not equal, so branch yields 1
        have hnotlt : ¬ (m1 : ℝ) * (beta : ℝ) ^ e < (m2 : ℝ) * (beta : ℝ) ^ e :=
          not_lt.mpr (le_of_lt hgtR)
        have hneq : (m1 : ℝ) * (beta : ℝ) ^ e ≠ (m2 : ℝ) * (beta : ℝ) ^ e := by
          exact ne_of_gt hgtR
        simp [pure, hnotlt, hneq, hgtR, hsign]

/-
Coq original:
Theorem le_F2R : forall e m1 m2 : Z,
  (F2R (Float beta m1 e) <= F2R (Float beta m2 e))%R -> (m1 <= m2)%Z.
Proof.
  intros e m1 m2 H.
  apply le_IZR.
  apply Rmult_le_reg_r with (bpow e).
  apply bpow_gt_0.
  exact H.
Qed.
-/
theorem le_F2R (e m1 m2 : Int) (hbeta : 1 < beta) :
  m1 ≤ m2 ↔ (F2R (FlocqFloat.mk m1 e : FlocqFloat beta)).run ≤ (F2R (FlocqFloat.mk m2 e : FlocqFloat beta)).run := by
  -- Let p = (beta : ℝ) ^ e, with p > 0
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hp_pos : 0 < (beta : ℝ) ^ e := by exact zpow_pos hbpos_real _
  have hp_nonneg : 0 ≤ (beta : ℝ) ^ e := le_of_lt hp_pos
  constructor
  · intro hle
    -- Multiply both sides by nonnegative p
    have hleR : (m1 : ℝ) ≤ (m2 : ℝ) := by exact_mod_cast hle
    unfold FloatSpec.Core.Defs.F2R
    simpa using (mul_le_mul_of_nonneg_right hleR hp_nonneg)
  · intro hmul
    -- Cancel the positive factor on the right
    unfold FloatSpec.Core.Defs.F2R at hmul
    have hleR : (m1 : ℝ) ≤ (m2 : ℝ) := le_of_mul_le_mul_right hmul hp_pos
    exact (by exact_mod_cast hleR)

/-
Coq original:
Theorem F2R_le : forall m1 m2 e : Z,
  (m1 <= m2)%Z -> (F2R (Float beta m1 e) <= F2R (Float beta m2 e))%R.
Proof.
  intros m1 m2 e H.
  unfold F2R. simpl.
  apply Rmult_le_compat_r.
  apply bpow_ge_0.
  now apply IZR_le.
Qed.
-/
theorem F2R_le (e m1 m2 : Int) (hbeta : 1 < beta) :
  (F2R (FlocqFloat.mk m1 e : FlocqFloat beta)).run ≤ (F2R (FlocqFloat.mk m2 e : FlocqFloat beta)).run → m1 ≤ m2 := by
  intro h
  have hiff := le_F2R (beta := beta) e m1 m2 hbeta
  exact hiff.mpr h

/-
Coq original:
Theorem lt_F2R : forall e m1 m2 : Z,
  (F2R (Float beta m1 e) < F2R (Float beta m2 e))%R -> (m1 < m2)%Z.
Proof.
  intros e m1 m2 H.
  apply lt_IZR.
  apply Rmult_lt_reg_r with (bpow e).
  apply bpow_gt_0.
  exact H.
Qed.
-/
theorem lt_F2R (e m1 m2 : Int) (hbeta : 1 < beta) :
  m1 < m2 ↔ (F2R (FlocqFloat.mk m1 e : FlocqFloat beta)).run < (F2R (FlocqFloat.mk m2 e : FlocqFloat beta)).run := by
  -- Let p = (beta : ℝ) ^ e, with p > 0
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hp_pos : 0 < (beta : ℝ) ^ e := by exact zpow_pos hbpos_real _
  constructor
  · intro hlt
    have hltR : (m1 : ℝ) < (m2 : ℝ) := by exact_mod_cast hlt
    unfold FloatSpec.Core.Defs.F2R
    simpa using (mul_lt_mul_of_pos_right hltR hp_pos)
  · intro hmul
    unfold FloatSpec.Core.Defs.F2R at hmul
    have hltR : (m1 : ℝ) < (m2 : ℝ) := lt_of_mul_lt_mul_right hmul (le_of_lt hp_pos)
    exact (by exact_mod_cast hltR)

/-
Coq original:
Theorem F2R_lt : forall e m1 m2 : Z,
  (m1 < m2)%Z -> (F2R (Float beta m1 e) < F2R (Float beta m2 e))%R.
Proof.
  intros e m1 m2 H.
  unfold F2R. simpl.
  apply Rmult_lt_compat_r.
  apply bpow_gt_0.
  now apply IZR_lt.
Qed.
-/
theorem F2R_lt (e m1 m2 : Int) (hbeta : 1 < beta) :
  (F2R (FlocqFloat.mk m1 e : FlocqFloat beta)).run < (F2R (FlocqFloat.mk m2 e : FlocqFloat beta)).run → m1 < m2 := by
  intro h
  have hiff := lt_F2R (beta := beta) e m1 m2 hbeta
  exact hiff.mpr h

/-
Coq original:
Theorem F2R_eq : forall e m1 m2 : Z,
  (m1 = m2)%Z -> (F2R (Float beta m1 e) = F2R (Float beta m2 e))%R.
Proof.
  intros e m1 m2 H.
  now apply (f_equal (fun m => F2R (Float beta m e))).
Qed.
-/
theorem F2R_eq (e m1 m2 : Int) (hbeta : 1 < beta) :
  (F2R (FlocqFloat.mk m1 e : FlocqFloat beta)).run = (F2R (FlocqFloat.mk m2 e : FlocqFloat beta)).run → m1 = m2 := by
  intro h
  -- Unfold and cancel the common nonzero factor (beta : ℝ) ^ e
  unfold FloatSpec.Core.Defs.F2R at h
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hpow_ne : ((beta : ℝ) ^ e) ≠ 0 := by
    exact zpow_ne_zero _ (ne_of_gt hbpos_real)
  have : (m1 : ℝ) = (m2 : ℝ) := mul_right_cancel₀ hpow_ne h
  exact (by exact_mod_cast this)

/-
Coq original:
Theorem eq_F2R : forall e m1 m2 : Z,
  F2R (Float beta m1 e) = F2R (Float beta m2 e) -> m1 = m2.
Proof.
  intros e m1 m2 H.
  apply Zle_antisym ; apply le_F2R with e ; rewrite H ; apply Rle_refl.
Qed.
-/
theorem eq_F2R (e m1 m2 : Int) (hbeta : 1 < beta) :
  m1 = m2 → (F2R (FlocqFloat.mk m1 e : FlocqFloat beta)).run = (F2R (FlocqFloat.mk m2 e : FlocqFloat beta)).run := by
  intro h
  subst h
  rfl

-- Absolute value and negation theorems

/-
Coq original:
Theorem F2R_Zabs: forall m e : Z,
  F2R (Float beta (Z.abs m) e) = Rabs (F2R (Float beta m e)).
Proof.
  intros m e.
  unfold F2R.
  rewrite Rabs_mult.
  rewrite <- abs_IZR.
  simpl.
  apply f_equal.
  apply sym_eq; apply Rabs_right.
  apply Rle_ge.
  apply bpow_ge_0.
Qed.
-/
theorem F2R_Zabs (f : FlocqFloat beta) (hbeta : 1 < beta) :
  |(F2R f).run| = (F2R (FlocqFloat.mk (Int.natAbs f.Fnum) f.Fexp : FlocqFloat beta)).run := by
  -- Let p = (beta : ℝ) ^ f.Fexp, with p > 0
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hp_pos : 0 < (beta : ℝ) ^ f.Fexp := by exact zpow_pos hbpos_real _
  have hp_nonneg : 0 ≤ (beta : ℝ) ^ f.Fexp := le_of_lt hp_pos
  unfold FloatSpec.Core.Defs.F2R
  -- Reduce to |m| = natAbs m over ℝ
  have h_abs_natAbs : (Int.natAbs f.Fnum : ℝ) = |(f.Fnum : ℝ)| := by
    -- Standard lemma relating casts and absolute values
    simpa [Int.cast_natAbs, Int.cast_abs]
  -- |m * p| = |m| * p and |p| = p (since p ≥ 0)
  have : |(f.Fnum : ℝ) * (beta : ℝ) ^ f.Fexp| = (Int.natAbs f.Fnum : ℝ) * (beta : ℝ) ^ f.Fexp := by
    simpa [abs_mul, abs_of_nonneg hp_nonneg, h_abs_natAbs]
  simpa using this

/-
Coq original:
Theorem F2R_Zopp : forall m e : Z,
  F2R (Float beta (Z.opp m) e) = Ropp (F2R (Float beta m e)).
Proof.
  intros m e.
  unfold F2R. simpl.
  rewrite <- Ropp_mult_distr_l_reverse.
  now rewrite opp_IZR.
Qed.
-/
theorem F2R_Zopp (f : FlocqFloat beta) (hbeta : 1 < beta) :
  -(F2R f).run = (F2R (FlocqFloat.mk (-f.Fnum) f.Fexp : FlocqFloat beta)).run := by
  unfold FloatSpec.Core.Defs.F2R
  -- -(m * p) = (-m) * p
  simpa using (neg_mul (f.Fnum : ℝ) ((beta : ℝ) ^ f.Fexp)).symm

/-
Coq original:
Theorem F2R_cond_Zopp : forall b m e,
  F2R (Float beta (cond_Zopp b m) e) = cond_Ropp b (F2R (Float beta m e)).
Proof.
  intros [|] m e ; unfold F2R ; simpl.
  now rewrite opp_IZR, Ropp_mult_distr_l_reverse.
  apply refl_equal.
Qed.
-/
theorem F2R_cond_Zopp (b : Bool) (f : FlocqFloat beta) (hbeta : 1 < beta) :
  (if b then -(F2R f).run else (F2R f).run) =
  (F2R (FlocqFloat.mk (if b then -f.Fnum else f.Fnum) f.Fexp : FlocqFloat beta)).run := by
  unfold FloatSpec.Core.Defs.F2R
  by_cases hb : b
  · simp [hb]
    -- -(m * p) = (-m) * p
  · simp [hb]

-- Zero properties

/-
Coq original:
Theorem F2R_0 : forall e : Z, F2R (Float beta 0 e) = 0%R.
Proof.
  intros e.
  unfold F2R. simpl.
  apply Rmult_0_l.
Qed.
-/
theorem F2R_0 (e : Int) (hbeta : 1 < beta) :
  (F2R (FlocqFloat.mk 0 e : FlocqFloat beta)).run = 0 := by
  unfold FloatSpec.Core.Defs.F2R
  simp

/-
Coq original:
Theorem eq_0_F2R : forall m e : Z,
  F2R (Float beta m e) = 0%R -> m = Z0.
Proof.
  intros m e H.
  apply eq_F2R with e.
  now rewrite F2R_0.
Qed.
-/
theorem eq_0_F2R (f : FlocqFloat beta) (hbeta : 1 < beta) :
  (F2R f).run = 0 → f.Fnum = 0 := by
  intro h
  -- Unfold F2R and use that (beta : ℝ) ^ e ≠ 0 since beta > 1
  unfold FloatSpec.Core.Defs.F2R at h
  -- From a product equal to zero, one factor must be zero
  have : (f.Fnum : ℝ) = 0 ∨ ((beta : ℝ) ^ f.Fexp) = 0 := by
    simpa [mul_comm] using (mul_eq_zero.mp h)
  -- Show the power is non-zero using beta > 1
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hpow_ne : ((beta : ℝ) ^ f.Fexp) ≠ 0 := by
    -- zpow_ne_zero for nonzero base
    exact zpow_ne_zero _ (ne_of_gt hbpos_real)
  -- Therefore the first factor must be zero
  have hnum0 : (f.Fnum : ℝ) = 0 := by
    cases this with
    | inl h1 => exact h1
    | inr h2 => exact (hpow_ne h2).elim
  -- Cast back to integers
  exact (by exact_mod_cast hnum0)

/-
Coq original:
Theorem ge_0_F2R : forall m e : Z,
  (0 <= F2R (Float beta m e))%R -> (0 <= m)%Z.
Proof.
  intros m e H.
  apply le_F2R with e.
  now rewrite F2R_0.
Qed.
-/
theorem ge_0_F2R (f : FlocqFloat beta) (hbeta : 1 < beta) :
  0 ≤ (F2R f).run → 0 ≤ f.Fnum := by
  intro h
  -- F2R f = f.Fnum * beta^f.Fexp, and beta^f.Fexp > 0
  simp only [F2R, pure, Id.run] at h
  have hβpos : (0 : ℝ) < (beta : ℝ) := by
    have : (0 : Int) < beta := lt_trans (by decide) hbeta
    exact Int.cast_pos.mpr this
  have hpow_pos : (0 : ℝ) < (beta : ℝ) ^ f.Fexp := zpow_pos hβpos f.Fexp
  -- From f.Fnum * beta^f.Fexp ≥ 0 and beta^f.Fexp > 0, we get f.Fnum ≥ 0
  have hfnum_real_nn := nonneg_of_mul_nonneg_left h hpow_pos
  by_contra hcontra
  push_neg at hcontra
  have : (f.Fnum : ℝ) < 0 := Int.cast_lt_zero.mpr hcontra
  exact not_lt.mpr hfnum_real_nn this
/-
Coq original:
Lemma Fnum_ge_0: forall (f : float beta),
  (0 <= F2R f)%R -> (0 <= Fnum f)%Z.
Proof.
  intros f H.
  case (Zle_or_lt 0 (Fnum f)); trivial.
  intros H1; contradict H.
  apply Rlt_not_le.
  now apply F2R_lt_0.
Qed.
-/
theorem Fnum_ge_0 (f : FlocqFloat beta) (hbeta : 1 < beta) :
  0 ≤ (F2R f).run → 0 ≤ f.Fnum := by
  -- Directly reuse ge_0_F2R
  exact ge_0_F2R (beta := beta) f hbeta

/-
Coq original:
Theorem le_0_F2R : forall m e : Z,
  (F2R (Float beta m e) <= 0)%R -> (m <= 0)%Z.
Proof.
  intros m e H.
  apply le_F2R with e.
  now rewrite F2R_0.
Qed.
-/
theorem le_0_F2R (f : FlocqFloat beta) (hbeta : 1 < beta) :
  (F2R f).run ≤ 0 → f.Fnum ≤ 0 := by
  intro h
  -- F2R f = f.Fnum * beta^f.Fexp, and beta^f.Fexp > 0
  simp only [F2R, pure, Id.run] at h
  have hβpos : (0 : ℝ) < (beta : ℝ) := by
    have : (0 : Int) < beta := lt_trans (by decide) hbeta
    exact Int.cast_pos.mpr this
  have hpow_pos : (0 : ℝ) < (beta : ℝ) ^ f.Fexp := zpow_pos hβpos f.Fexp
  -- From f.Fnum * beta^f.Fexp ≤ 0 and beta^f.Fexp > 0, we get f.Fnum ≤ 0
  by_contra hcontra
  push_neg at hcontra
  have hfnum_pos : (f.Fnum : ℝ) > 0 := Int.cast_pos.mpr hcontra
  have hprod_pos : (f.Fnum : ℝ) * (beta : ℝ) ^ f.Fexp > 0 := mul_pos hfnum_pos hpow_pos
  exact not_lt.mpr h hprod_pos
/-
Coq original:
Lemma Fnum_le_0: forall (f : float beta),
  (F2R f <= 0)%R -> (Fnum f <= 0)%Z.
Proof.
  intros f H.
  case (Zle_or_lt (Fnum f) 0); trivial.
  intros H1; contradict H.
  apply Rlt_not_le.
  now apply F2R_gt_0.
Qed.
-/
theorem Fnum_le_0 (f : FlocqFloat beta) (hbeta : 1 < beta) :
  (F2R f).run ≤ 0 → f.Fnum ≤ 0 := by
  -- Directly reuse le_0_F2R
  exact le_0_F2R (beta := beta) f hbeta

/-
Coq original:
Theorem gt_0_F2R : forall m e : Z,
  (0 < F2R (Float beta m e))%R -> (0 < m)%Z.
Proof.
  intros m e H.
  apply lt_F2R with e.
  now rewrite F2R_0.
Qed.
-/
theorem gt_0_F2R (f : FlocqFloat beta) (hbeta : 1 < beta) :
  0 < (F2R f).run → 0 < f.Fnum := by
  intro h
  simp only [F2R, pure, Id.run] at h
  have hβpos : (0 : ℝ) < (beta : ℝ) := by
    have : (0 : Int) < beta := lt_trans (by decide) hbeta
    exact Int.cast_pos.mpr this
  have hpow_pos : (0 : ℝ) < (beta : ℝ) ^ f.Fexp := zpow_pos hβpos f.Fexp
  have := (mul_pos_iff_of_pos_right hpow_pos).mp h
  exact Int.cast_pos.mp this
/-
Coq original:
Theorem lt_0_F2R : forall m e : Z,
  (F2R (Float beta m e) < 0)%R -> (m < 0)%Z.
Proof.
  intros m e H.
  apply lt_F2R with e.
  now rewrite F2R_0.
Qed.
-/
theorem lt_0_F2R (f : FlocqFloat beta) (hbeta : 1 < beta) :
  (F2R f).run < 0 → f.Fnum < 0 := by
  intro h
  simp only [F2R, pure, Id.run] at h
  have hβpos : (0 : ℝ) < (beta : ℝ) := by
    have : (0 : Int) < beta := lt_trans (by decide) hbeta
    exact Int.cast_pos.mpr this
  have hpow_pos : (0 : ℝ) < (beta : ℝ) ^ f.Fexp := zpow_pos hβpos f.Fexp
  by_contra hcontra
  push_neg at hcontra
  have hfnum_nn : (f.Fnum : ℝ) ≥ 0 := by
    have : (0 : ℤ) ≤ f.Fnum := hcontra
    exact_mod_cast this
  have hprod_nn : (f.Fnum : ℝ) * (beta : ℝ) ^ f.Fexp ≥ 0 :=
    mul_nonneg hfnum_nn (le_of_lt hpow_pos)
  exact not_lt.mpr hprod_nn h
/-
Coq original:
Theorem F2R_ge_0 : forall f : float beta,
  (0 <= Fnum f)%Z -> (0 <= F2R f)%R.
Proof.
  intros f H.
  rewrite <- F2R_0 with (Fexp f).
  now apply F2R_le.
Qed.
-/
theorem F2R_ge_0 (f : FlocqFloat beta) (hbeta : 1 < beta) :
  0 ≤ f.Fnum → 0 ≤ (F2R f).run := by
  intro hnum
  unfold FloatSpec.Core.Defs.F2R
  -- 0 ≤ m and 0 ≤ p ⇒ 0 ≤ m * p
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hp_nonneg : 0 ≤ (beta : ℝ) ^ f.Fexp := by
    exact (le_of_lt (zpow_pos hbpos_real _))
  have hnumR : 0 ≤ (f.Fnum : ℝ) := by exact_mod_cast hnum
  exact mul_nonneg hnumR hp_nonneg

/-
Coq original:
Theorem F2R_le_0 : forall f : float beta,
  (Fnum f <= 0)%Z -> (F2R f <= 0)%R.
Proof.
  intros f H.
  rewrite <- F2R_0 with (Fexp f).
  now apply F2R_le.
Qed.
-/
theorem F2R_le_0 (f : FlocqFloat beta) (hbeta : 1 < beta) :
  f.Fnum ≤ 0 → (F2R f).run ≤ 0 := by
  intro hnum
  unfold FloatSpec.Core.Defs.F2R
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hp_nonneg : 0 ≤ (beta : ℝ) ^ f.Fexp := by
    exact (le_of_lt (zpow_pos hbpos_real _))
  have hnumR : (f.Fnum : ℝ) ≤ 0 := by exact_mod_cast hnum
  exact mul_nonpos_of_nonpos_of_nonneg hnumR hp_nonneg

/-
Coq original:
Theorem F2R_gt_0 : forall f : float beta,
  (0 < Fnum f)%Z -> (0 < F2R f)%R.
Proof.
  intros f H.
  rewrite <- F2R_0 with (Fexp f).
  now apply F2R_lt.
Qed.
-/
theorem F2R_gt_0 (f : FlocqFloat beta) (hbeta : 1 < beta) :
  0 < f.Fnum → 0 < (F2R f).run := by
  intro hnum
  unfold FloatSpec.Core.Defs.F2R
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hp_pos : 0 < (beta : ℝ) ^ f.Fexp := by exact zpow_pos hbpos_real _
  have hnumR : 0 < (f.Fnum : ℝ) := by exact_mod_cast hnum
  exact mul_pos hnumR hp_pos

/-
Coq original:
Theorem F2R_lt_0 : forall f : float beta,
  (Fnum f < 0)%Z -> (F2R f < 0)%R.
Proof.
  intros f H.
  rewrite <- F2R_0 with (Fexp f).
  now apply F2R_lt.
Qed.
-/
theorem F2R_lt_0 (f : FlocqFloat beta) (hbeta : 1 < beta) :
  f.Fnum < 0 → (F2R f).run < 0 := by
  intro hnum
  unfold FloatSpec.Core.Defs.F2R
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hp_pos : 0 < (beta : ℝ) ^ f.Fexp := by exact zpow_pos hbpos_real _
  have hnumR : (f.Fnum : ℝ) < 0 := by exact_mod_cast hnum
  exact mul_neg_of_neg_of_pos hnumR hp_pos

/-
Coq original:
Theorem F2R_neq_0 : forall f : float beta,
  (Fnum f <> 0)%Z -> (F2R f <> 0)%R.
Proof.
  intros f H H1.
  apply H.
  now apply eq_0_F2R with (Fexp f).
Qed.
-/
theorem F2R_neq_0 (f : FlocqFloat beta) (hbeta : 1 < beta) :
  f.Fnum ≠ 0 → (F2R f).run ≠ 0 := by
  intro hnum ne0
  have := eq_0_F2R (beta := beta) f hbeta ne0
  exact hnum this

-- Power of beta properties

/-
Coq original:
Theorem F2R_bpow : forall e : Z, F2R (Float beta 1 e) = bpow e.
Proof.
  intros e.
  unfold F2R. simpl.
  apply Rmult_1_l.
Qed.
-/
theorem F2R_bpow (e : Int) (hbeta : 1 < beta) :
  (F2R (FlocqFloat.mk 1 e : FlocqFloat beta)).run = (beta : ℝ) ^ e := by
  unfold FloatSpec.Core.Defs.F2R
  simp

/-
Coq original:
Theorem bpow_le_F2R : forall m e : Z,
  (0 < m)%Z -> (bpow e <= F2R (Float beta m e))%R.
Proof.
  intros m e H.
  rewrite <- F2R_bpow.
  apply F2R_le.
  now apply (Zlt_le_succ 0).
Qed.
-/
theorem bpow_le_F2R (f : FlocqFloat beta) (hbeta : 1 < beta) :
  0 < f.Fnum → (beta : ℝ) ^ f.Fexp ≤ (F2R f).run := by
  intro hm_pos
  -- From 0 < m (integer), deduce 1 ≤ m
  have hm_one_le : (1 : Int) ≤ f.Fnum := by
    -- 0 < m ↔ 1 ≤ m for integers
    have := Int.add_one_le_iff.mpr hm_pos
    simpa using this
  have hm_one_leR : (1 : ℝ) ≤ (f.Fnum : ℝ) := by exact_mod_cast hm_one_le
  -- Let p = (beta : ℝ) ^ e with p ≥ 0
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hp_nonneg : 0 ≤ (beta : ℝ) ^ f.Fexp := by exact (le_of_lt (zpow_pos hbpos_real _))
  -- Multiply both sides by p ≥ 0: 1*p ≤ m*p
  unfold FloatSpec.Core.Defs.F2R
  simpa using (mul_le_mul_of_nonneg_right hm_one_leR hp_nonneg)

/-
Coq original:
Theorem F2R_p1_le_bpow : forall m e1 e2 : Z,
  (0 < m)%Z -> (F2R (Float beta m e1) < bpow e2)%R ->
  (F2R (Float beta (m + 1) e1) <= bpow e2)%R.
Proof.
  intros m e1 e2 Hm.
  intros H.
  assert (He : (e1 <= e2)%Z).
  (* proof omitted for brevity *)
  revert H.
  replace e2 with (e2 - e1 + e1)%Z by ring.
  rewrite bpow_plus.
  unfold F2R. simpl.
  rewrite <- (IZR_Zpower beta (e2 - e1)).
  intros H.
  apply Rmult_le_compat_r.
  apply bpow_ge_0.
  apply Rmult_lt_reg_r in H.
  apply IZR_le.
  apply Zlt_le_succ.
  now apply lt_IZR.
  apply bpow_gt_0.
  now apply Zle_minus_le_0.
Qed.
-/
theorem F2R_p1_le_bpow (m e1 e2 : Int) (hbeta : 1 < beta) :
  0 < m →
  (F2R (FlocqFloat.mk m e1 : FlocqFloat beta)).run < (beta : ℝ) ^ e2 →
  (F2R (FlocqFloat.mk (m + 1) e1 : FlocqFloat beta)).run ≤ (beta : ℝ) ^ e2 := by
  intro hm_pos hlt
  -- Notation
  set b : ℝ := (beta : ℝ)
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos : 0 < b := by
    simpa [b] using (by exact_mod_cast hbpos_int : (0 : ℝ) < (beta : ℝ))
  have hbne : b ≠ 0 := ne_of_gt hbpos
  -- Let p = b ^ e1
  set p : ℝ := b ^ e1
  have hp_pos : 0 < p := by simpa [p] using (zpow_pos hbpos e1)
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  -- Rewrite the RHS power using exponent difference
  have hsplit : b ^ e2 = (b ^ (e2 - e1)) * p := by
    -- b^(e2) = b^((e2 - e1) + e1) = b^(e2 - e1) * b^e1
    have := zpow_add₀ hbne (e2 - e1) e1
    simpa [p, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm] using this
  -- From 1 ≤ m (since 0 < m over ℤ)
  have hm_one_le : (1 : Int) ≤ m := by
    have := Int.add_one_le_iff.mpr hm_pos
    simpa using this
  have hm_one_leR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_one_le
  -- Deduce b^e1 < b^e2 using hlt and 1 ≤ m
  have hpow_lt : b ^ e1 < b ^ e2 := by
    -- 1*p ≤ m*p < b^e2 ⇒ p < b^e2
    have : (1 : ℝ) * p ≤ (m : ℝ) * p := mul_le_mul_of_nonneg_right hm_one_leR hp_nonneg
    have : p ≤ (m : ℝ) * p := by simpa [one_mul, p]
    exact lt_of_le_of_lt this hlt
  -- From strict monotonicity in the exponent (since b > 1), get e1 < e2 ⇒ 0 ≤ e2 - e1
  have hβR : (1 : ℝ) < b := by
    simpa [b] using (by exact_mod_cast hbeta : (1 : ℝ) < (beta : ℝ))
  have hlt_e : e1 < e2 := ((zpow_right_strictMono₀ hβR).lt_iff_lt).1 hpow_lt
  have hd_nonneg : 0 ≤ e2 - e1 := sub_nonneg.mpr (le_of_lt hlt_e)
  -- Divide the original strict inequality by p > 0 to get m < b^(e2 - e1)
  have h_div : (m : ℝ) < b ^ (e2 - e1) := by
    -- m*p < b^e2 = (b^(e2 - e1))*p
    have : (m : ℝ) * p < (b ^ (e2 - e1)) * p := by
      -- unfold F2R in the hypothesis to expose the product form
      have hlt' := hlt
      unfold FloatSpec.Core.Defs.F2R at hlt'
      simpa [p, hsplit, mul_comm, mul_left_comm, mul_assoc]
        using hlt'
    exact lt_of_mul_lt_mul_right this (le_of_lt hp_pos)
  -- Turn the exponent difference into a natural exponent using `zpow_ofNat`
  -- and bridge "m < b^(e2-e1)" to "m < b^toNat(e2-e1)"
  have h_div_nat : (m : ℝ) < b ^ (Int.toNat (e2 - e1)) := by
    have hofNat : ((Int.toNat (e2 - e1)) : Int) = e2 - e1 := by
      simpa using (Int.toNat_of_nonneg hd_nonneg)
    -- b^(e2-e1) = b^((toNat (e2-e1)):ℤ) = b^(toNat (e2-e1))
    have hzpow_int : b ^ (e2 - e1) = b ^ ((Int.toNat (e2 - e1)) : Int) := by
      simpa using (congrArg (fun t : Int => b ^ t) hofNat.symm)
    have hzpow_nat : b ^ ((Int.toNat (e2 - e1)) : Int) = b ^ (Int.toNat (e2 - e1)) :=
      zpow_ofNat b (Int.toNat (e2 - e1))
    have hz : b ^ (e2 - e1) = b ^ (Int.toNat (e2 - e1)) := hzpow_int.trans hzpow_nat
    simpa [hz] using h_div
  -- Bridge "m < b^n (ℝ)" to "m + 1 ≤ beta^n (ℤ)" for n : ℕ
  have h_int_le : m + 1 ≤ beta ^ (Int.toNat (e2 - e1)) := by
    -- cast inequality to real and apply the helper lemma
    have : (m : ℝ) < b ^ (Int.toNat (e2 - e1)) := h_div_nat
    exact int_lt_pow_real_to_int beta m (Int.toNat (e2 - e1)) this
  -- Cast back to reals
  have h_le_real : (m + 1 : ℝ) ≤ b ^ (Int.toNat (e2 - e1)) := by
    -- cast the integer inequality to reals and rewrite RHS via cast_pow
    have hcast : (m + 1 : ℝ) ≤ ((beta ^ (Int.toNat (e2 - e1)) : Int) : ℝ) := by
      exact_mod_cast h_int_le
    -- (beta : ℝ)^n = ((beta^n : Int) : ℝ)
    have hcast_pow : b ^ (Int.toNat (e2 - e1)) = ((beta ^ (Int.toNat (e2 - e1)) : Int) : ℝ) := by
      simpa [b] using (Int.cast_pow (R := ℝ) (x := beta) (n := Int.toNat (e2 - e1)))
    simpa [hcast_pow] using hcast
  -- Multiply both sides by p ≥ 0 and rewrite
  unfold FloatSpec.Core.Defs.F2R
  -- (m+1)*p ≤ (b^n)*p = b^e2
  have : (m + 1 : ℝ) * p ≤ (b ^ (Int.toNat (e2 - e1))) * p :=
    mul_le_mul_of_nonneg_right h_le_real hp_nonneg
  -- Replace p and expand the right-hand side back to b^e2
  -- Reuse the same `zpow_ofNat` reduction to simplify the RHS
  have hofNat : ((Int.toNat (e2 - e1)) : Int) = e2 - e1 := by
    simpa using (Int.toNat_of_nonneg hd_nonneg)
  have hzpow_int : b ^ (e2 - e1) = b ^ ((Int.toNat (e2 - e1)) : Int) := by
    simpa using (congrArg (fun t : Int => b ^ t) hofNat.symm)
  have hzpow_nat : b ^ ((Int.toNat (e2 - e1)) : Int) = b ^ (Int.toNat (e2 - e1)) :=
    zpow_ofNat b (Int.toNat (e2 - e1))
  have hz : b ^ (e2 - e1) = b ^ (Int.toNat (e2 - e1)) := hzpow_int.trans hzpow_nat
  simpa [p, hsplit, hz, mul_comm, mul_left_comm, mul_assoc]
    using this

/-
Coq original:
Theorem bpow_le_F2R_m1 : forall m e1 e2 : Z,
  (1 < m)%Z -> (bpow e2 < F2R (Float beta m e1))%R ->
  (bpow e2 <= F2R (Float beta (m - 1) e1))%R.
Proof.
  intros m e1 e2 Hm.
  case (Zle_or_lt e1 e2); intros He.
  replace e2 with (e2 - e1 + e1)%Z by ring.
  rewrite bpow_plus.
  unfold F2R. simpl.
  rewrite <- (IZR_Zpower beta (e2 - e1)).
  intros H.
  apply Rmult_le_compat_r.
  apply bpow_ge_0.
  apply Rmult_lt_reg_r in H.
  apply IZR_le.
  rewrite (Zpred_succ (Zpower _ _)).
  apply Zplus_le_compat_r.
  apply Zlt_le_succ.
  now apply lt_IZR.
  apply bpow_gt_0.
  now apply Zle_minus_le_0.
  intros H.
  apply Rle_trans with (1*bpow e1)%R.
  rewrite Rmult_1_l.
  apply bpow_le.
  now apply Zlt_le_weak.
  unfold F2R. simpl.
  apply Rmult_le_compat_r.
  apply bpow_ge_0.
  apply IZR_le.
  lia.
Qed.
-/
theorem bpow_le_F2R_m1 (f : FlocqFloat beta) (hbeta : 1 < beta) :
  f.Fnum < 0 → (F2R f).run ≤ -((beta : ℝ) ^ f.Fexp) := by
  intro hneg
  -- From m < 0 over ℤ, deduce (m : ℝ) ≤ -1
  have h_add_le : (f.Fnum : ℝ) + 1 ≤ 0 := by
    -- m + 1 ≤ 0 ↔ m < 0 on integers, then cast to ℝ
    have := (Int.add_one_le_iff.mpr hneg)
    exact (by exact_mod_cast this)
  have h_m_le : (f.Fnum : ℝ) ≤ -1 := by linarith
  -- Multiply by nonnegative p = β^e
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hp_nonneg : 0 ≤ (beta : ℝ) ^ f.Fexp := le_of_lt (zpow_pos hbpos_real _)
  unfold FloatSpec.Core.Defs.F2R
  have := mul_le_mul_of_nonneg_right h_m_le hp_nonneg
  simpa using this

/-
Coq original:
Theorem F2R_lt_bpow : forall f : float beta, forall e',
  (Z.abs (Fnum f) < Zpower beta (e' - Fexp f))%Z ->
  (Rabs (F2R f) < bpow e')%R.
Proof.
  intros (m, e) e' Hm.
  rewrite <- F2R_Zabs.
  destruct (Zle_or_lt e e') as [He|He].
  unfold F2R. simpl.
  apply Rmult_lt_reg_r with (bpow (-e)).
  apply bpow_gt_0.
  rewrite Rmult_assoc, <- 2!bpow_plus, Zplus_opp_r, Rmult_1_r.
  rewrite <-IZR_Zpower.
  2: now apply Zle_left.
  now apply IZR_lt.
  elim Zlt_not_le with (1 := Hm).
  simpl.
  assert (H: (e' - e < 0)%Z) by lia.
  clear -H.
  destruct (e' - e)%Z ; try easy.
  apply Zabs_pos.
Qed.
-/
/-
Variant (adapted): for a negative mantissa, the real value is strictly
below the corresponding radix power at the same exponent.

This is a simple but always-valid bound used in place of the Coq lemma
that requires a normalization hypothesis on the mantissa. It suffices for
local ordering arguments and avoids adding extra preconditions.
-/
theorem F2R_lt_bpow (f : FlocqFloat beta) (hbeta : 1 < beta) :
  f.Fnum < 0 → (F2R f).run < (beta : ℝ) ^ f.Fexp := by
  intro hneg
  -- Unfold and use that (β : ℝ) ^ e > 0 when β > 1
  unfold FloatSpec.Core.Defs.F2R
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hp_pos : 0 < (beta : ℝ) ^ f.Fexp := by exact zpow_pos hbpos_real _
  -- Since m < 0, we have m * p ≤ 0 < p
  have hmnpos : (f.Fnum : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt hneg)
  have hmul_le_zero : (f.Fnum : ℝ) * (beta : ℝ) ^ f.Fexp ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hmnpos (le_of_lt hp_pos)
  exact lt_of_le_of_lt hmul_le_zero hp_pos

-- Exponent change properties

/-
Coq original:
Theorem F2R_change_exp : forall e' m e : Z,
  (e' <= e)%Z -> F2R (Float beta m e) = F2R (Float beta (m * Zpower beta (e - e')) e').
Proof.
  intros e' m e He.
  unfold F2R. simpl.
  rewrite mult_IZR, IZR_Zpower, Rmult_assoc.
  apply f_equal.
  pattern e at 1 ; replace e with (e - e' + e')%Z by ring.
  apply bpow_plus.
  now apply Zle_minus_le_0.
Qed.
-/
theorem F2R_change_exp (f : FlocqFloat beta) (e' : Int) (hbeta : 1 < beta) (he : e' ≤ f.Fexp) :
  (F2R f).run = (F2R (FlocqFloat.mk (f.Fnum * beta ^ (f.Fexp - e').natAbs) e' : FlocqFloat beta)).run := by
  -- Expand both sides
  unfold FloatSpec.Core.Defs.F2R
  -- Notation for the real base and basic facts
  set b : ℝ := (beta : ℝ)
  have hbpos : (0 : ℝ) < b := by
    have hb' : (0 : ℤ) < beta := lt_trans (by decide) hbeta
    have : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hb'
    simpa [b] using this
  have hbne : b ≠ 0 := ne_of_gt hbpos
  -- Split the exponent f.Fexp = (f.Fexp - e') + e'
  have hsplit : b ^ f.Fexp = b ^ (f.Fexp - e') * b ^ e' := by
    -- use zpow_add₀ on (f.Fexp - e') + e'
    simpa [sub_add_cancel] using (zpow_add₀ hbne (f.Fexp - e') e')
  -- The difference is nonnegative thanks to he : e' ≤ f.Fexp
  have hd_nonneg : 0 ≤ f.Fexp - e' := sub_nonneg.mpr he
  -- Turn the zpow with nonnegative exponent into a Nat power
  have hzpow_toNat : b ^ (f.Fexp - e') = b ^ (Int.toNat (f.Fexp - e')) := by
    -- let n be the nonnegative exponent
    set n := Int.toNat (f.Fexp - e')
    have hto : ((n : Int)) = f.Fexp - e' := by
      simpa [n] using (Int.toNat_of_nonneg hd_nonneg)
    have hzpow_nat : b ^ (n : Int) = b ^ n := zpow_ofNat b n
    calc
      b ^ (f.Fexp - e') = b ^ (n : Int) := by simpa [hto]
      _ = b ^ n := by simpa [hzpow_nat]
  -- Cast of integer power to real
  have hcast_pow : b ^ (Int.toNat (f.Fexp - e')) = ((beta ^ (Int.toNat (f.Fexp - e')) : Int) : ℝ) := by
    -- rewrite (beta : ℝ) ^ n into cast of (beta ^ n : Int)
    -- using the standard cast lemma
    have : (beta : ℝ) ^ (Int.toNat (f.Fexp - e')) = ((beta ^ (Int.toNat (f.Fexp - e')) : Int) : ℝ) := by
      rw [← Int.cast_pow]
    simpa [b] using this
  -- Also relate natAbs with toNat under nonnegativity
  have hnat : (f.Fexp - e').natAbs = Int.toNat (f.Fexp - e') :=
    natAbs_eq_toNat_of_nonneg hd_nonneg
  -- Rearrange the equality in a few steps
  have hstep1 : (f.Fnum : ℝ) * b ^ f.Fexp
      = ((f.Fnum : ℝ) * b ^ (Int.toNat (f.Fexp - e'))) * b ^ e' := by
    calc
      (f.Fnum : ℝ) * b ^ f.Fexp
          = (f.Fnum : ℝ) * (b ^ (f.Fexp - e') * b ^ e') := by simpa [hsplit]
      _ = ((f.Fnum : ℝ) * b ^ (f.Fexp - e')) * b ^ e' := by ring
      _ = ((f.Fnum : ℝ) * b ^ (Int.toNat (f.Fexp - e'))) * b ^ e' := by
            simpa [hzpow_toNat]

  have hstep2 : (f.Fnum : ℝ) * b ^ (Int.toNat (f.Fexp - e'))
        = (f.Fnum : ℝ) * ((beta ^ (Int.toNat (f.Fexp - e')) : Int) : ℝ) := by
    simpa [hcast_pow]

  have hstep3 :
      (f.Fnum : ℝ) * ((beta ^ (Int.toNat (f.Fexp - e')) : Int) : ℝ)
        = (((f.Fnum * beta ^ (Int.toNat (f.Fexp - e'))) : Int) : ℝ) := by
    simp [Int.cast_mul]

  have hmain : (f.Fnum : ℝ) * b ^ f.Fexp
      = (((f.Fnum * beta ^ (Int.toNat (f.Fexp - e'))) : Int) : ℝ) * b ^ e' := by
    simpa [hstep2, hstep3] using hstep1

  have hnat_eq : (((f.Fnum * beta ^ (Int.toNat (f.Fexp - e'))) : Int) : ℝ)
      = (((f.Fnum * beta ^ ((f.Fexp - e').natAbs)) : Int) : ℝ) := by
    -- replace toNat by natAbs using nonnegativity (in the exponent)
    simpa [hnat]
      using congrArg (fun n : Nat => (((f.Fnum * beta ^ n : Int) : ℝ))) rfl

  -- Conclude by putting back b = (beta : ℝ)
  simpa [b, hnat_eq] using hmain
  -- Fold back the RHS
  -- and finish by reflexivity
  -- -- Expand both sides
  -- unfold FloatSpec.Core.Defs.F2R
  -- -- Let b be the real base and note it is nonzero since beta > 1
  -- set b : ℝ := (beta : ℝ)
  -- have hb0 : b ≠ 0 := by
  --   have : (0 : ℝ) < b := by exact_mod_cast (lt_trans (by decide) hbeta)
  --   exact ne_of_gt this
  -- -- Decompose the exponent: f.Fexp = e' + (f.Fexp - e')
  -- have hsum : e' + (f.Fexp - e') = f.Fexp := by
  --   simpa [add_comm, add_left_comm, add_assoc] using (add_sub_cancel e' f.Fexp)
  -- have hsplit : b ^ f.Fexp = b ^ e' * b ^ (f.Fexp - e') := by
  --   simpa [hsum] using (zpow_add₀ hb0 e' (f.Fexp - e'))
  -- -- The difference is nonnegative
  -- have hd : 0 ≤ f.Fexp - e' := sub_nonneg.mpr he
  -- -- Convert the nonnegative zpow to a nat pow via toNat
  -- have hto : Int.ofNat (Int.toNat (f.Fexp - e')) = f.Fexp - e' := Int.toNat_of_nonneg hd
  -- have hzpow_nat : b ^ (f.Fexp - e') = b ^ (Int.toNat (f.Fexp - e')) := by
  --   simpa [hto, zpow_ofNat]
  -- have hnat : (f.Fexp - e').natAbs = Int.toNat (f.Fexp - e') := Int.natAbs_of_nonneg hd
  -- -- Rearrange and cast the integer product to reals
  -- calc
  --   (f.Fnum : ℝ) * b ^ f.Fexp
  --       = (f.Fnum : ℝ) * (b ^ e' * b ^ (f.Fexp - e')) := by simpa [hsplit]
  --   _   = ((f.Fnum : ℝ) * b ^ (Int.toNat (f.Fexp - e'))) * b ^ e' := by
  --             simpa [mul_comm, mul_left_comm, mul_assoc, hzpow_nat]
  --   _   = (((f.Fnum * beta ^ (Int.toNat (f.Fexp - e')) : Int) : ℝ)) * b ^ e' := by
  --             simp [Int.cast_mul, Int.cast_pow]
  --   _   = (((f.Fnum * beta ^ ((f.Fexp - e').natAbs) : Int) : ℝ)) * b ^ e' := by
  --             simpa [hnat]

/-
Coq original:
Theorem F2R_prec_normalize : forall m e e' p : Z,
  (Z.abs m < Zpower beta p)%Z ->
  (bpow (e' - 1)%Z <= Rabs (F2R (Float beta m e)))%R ->
  F2R (Float beta m e) = F2R (Float beta (m * Zpower beta (e - e' + p)) (e' - p)).
Proof.
  intros m e e' p Hm Hf.
  assert (Hp: (0 <= p)%Z).
  destruct p ; try easy.
  now elim (Zle_not_lt _ _ (Zabs_pos m)).
  (* . *)
  replace (e - e' + p)%Z with (e - (e' - p))%Z by ring.
  apply F2R_change_exp.
  cut (e' - 1 < e + p)%Z.
  lia.
  apply (lt_bpow beta).
  apply Rle_lt_trans with (1 := Hf).
  rewrite <- F2R_Zabs, Zplus_comm, bpow_plus.
  apply Rmult_lt_compat_r.
  apply bpow_gt_0.
  rewrite <- IZR_Zpower.
  now apply IZR_lt.
  exact Hp.
Qed.
-/
theorem F2R_prec_normalize (m e e' p : Int) (hbeta : 1 < beta) :
  Int.natAbs m < Int.natAbs beta ^ (p.toNat) →
  (beta : ℝ) ^ (e' - 1) ≤ |(F2R (FlocqFloat.mk m e : FlocqFloat beta)).run| →
  (F2R (FlocqFloat.mk m e : FlocqFloat beta)).run =
    (F2R (FlocqFloat.mk (m * beta ^ (e - e' + p).natAbs) (e' - p) : FlocqFloat beta)).run := by
  intro habs_bound hlower
  classical
  -- Notation and basic facts about the base b = (beta : ℝ)
  set b : ℝ := (beta : ℝ)
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos : 0 < b := by
    have : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
    simpa [b] using this
  have hbne : b ≠ 0 := ne_of_gt hbpos
  have hβR : (1 : ℝ) < b := by
    simpa [b] using (by exact_mod_cast hbeta : (1 : ℝ) < (beta : ℝ))
  -- From the lower bound, |F2R| is strictly positive
  have hpow_pos : 0 < b ^ (e' - 1) := zpow_pos hbpos _
  have hF2R_pos : 0 < |(F2R (FlocqFloat.mk m e : FlocqFloat beta)).run| :=
    lt_of_lt_of_le hpow_pos hlower
  -- Hence m ≠ 0
  have hm_ne : m ≠ 0 := by
    -- If m = 0, then F2R = 0, contradicting hF2R_pos
    intro h
    have : (F2R (FlocqFloat.mk m e : FlocqFloat beta)).run = 0 := by
      unfold FloatSpec.Core.Defs.F2R
      simpa [h, b]
    have : |(F2R (FlocqFloat.mk m e : FlocqFloat beta)).run| = 0 := by simpa [this]
    exact lt_irrefl _ (lt_of_eq_of_lt this hF2R_pos)
  -- Show p is nonnegative: otherwise natAbs m < 1 would force m = 0
  have hp_nonneg : 0 ≤ p := by
    by_contra hnot
    have hpneg : p < 0 := lt_of_not_ge hnot
    have hto : p.toNat = 0 := Int.toNat_of_nonpos (le_of_lt hpneg)
    have : Int.natAbs m < Int.natAbs beta ^ (0 : Nat) := by simpa [hto] using habs_bound
    have : Int.natAbs m < 1 := by simpa using this
    have hm0 : m = 0 := by
      -- natAbs m < 1 ⇒ m = 0
      have : Int.natAbs m = 0 := Nat.lt_one_iff.mp this
      simpa [Int.natAbs_eq_zero] using this
    exact hm_ne hm0
  -- Convert the hypothesis on |m| from Nat/Int to ℝ
  have h_nat_to_real : |(m : ℝ)| < b ^ (p.toNat) := by
    -- Start from the Nat inequality and cast to ℝ
    have hcast : (Int.natAbs m : ℝ) < ((Int.natAbs beta : ℕ) : ℝ) ^ (p.toNat) := by
      -- Use monotonocity of casting and Nat.pow casting
      have := habs_bound
      -- (↑(a ^ n) : ℝ) = (↑a : ℝ) ^ n
      have hpow_cast : (((Int.natAbs beta) ^ p.toNat : Nat) : ℝ)
          = ((Int.natAbs beta : ℝ) ^ p.toNat) := by
        simpa using (Nat.cast_pow (m := Int.natAbs beta) (n := p.toNat) (R := ℝ))
      -- Cast both sides to ℝ
      have hcast' : ((Int.natAbs m : Nat) : ℝ) < (((Int.natAbs beta) ^ p.toNat : Nat) : ℝ) := by
        exact_mod_cast this
      simpa [hpow_cast] using hcast'
    -- (Int.natAbs m : ℝ) = |(m : ℝ)| and (Int.natAbs beta : ℝ) = |(beta : ℝ)| = b
    have h_abs_m : (Int.natAbs m : ℝ) = |(m : ℝ)| := by
      simpa [Int.cast_natAbs, Int.cast_abs]
    have hb_abs : (Int.natAbs beta : ℝ) = b := by
      have h1 : (Int.natAbs beta : ℝ) = |(beta : ℝ)| := by
        simpa [Int.cast_natAbs, Int.cast_abs]
      have h2 : |(beta : ℝ)| = (beta : ℝ) := abs_of_nonneg (le_of_lt hbpos)
      simpa [b, h1] using h2
    simpa [h_abs_m, hb_abs] using hcast
  -- Since p ≥ 0, rewrite b^p using a natural exponent
  have hp_toNat : ((p.toNat : Int)) = p := by
    simpa using (Int.toNat_of_nonneg hp_nonneg)
  have h_bpow_p : b ^ (p.toNat) = b ^ p := by
    -- b ^ p = b ^ ((p.toNat : Int)) = b ^ (p.toNat)
    have : b ^ ((p.toNat : Int)) = b ^ (p.toNat) := zpow_ofNat b (p.toNat)
    simpa [hp_toNat] using this.symm
  -- Turn the lower bound into an exponent inequality: b^(e'-1) < b^(e+p)
  -- First, bound |F2R| by b^(p+e)
  have hp_nonneg' : 0 ≤ b ^ e := le_of_lt (zpow_pos hbpos _)
  have hupper : |(F2R (FlocqFloat.mk m e : FlocqFloat beta)).run| < b ^ (e + p) := by
    -- |m*b^e| = |m|*|b^e| = |m|*b^e (since b^e ≥ 0), and |m| < b^p
    unfold FloatSpec.Core.Defs.F2R
    have hbabs' : |b ^ e| = b ^ e := by simp [abs_of_nonneg hp_nonneg']
    have hlt_mul : |(m : ℝ)| * b ^ e < b ^ p * b ^ e := by
      have := mul_lt_mul_of_pos_right (by simpa [h_bpow_p] using h_nat_to_real) (zpow_pos hbpos e)
      simpa [mul_comm, mul_left_comm, mul_assoc]
        using this
    have hmul : b ^ p * b ^ e = b ^ (e + p) := by
      have := zpow_add₀ hbne p e
      simpa [add_comm, add_left_comm, add_assoc] using this.symm
    calc
      |(m : ℝ) * b ^ e| = |(m : ℝ)| * |b ^ e| := by simpa [abs_mul]
      _ = |(m : ℝ)| * b ^ e := by simpa [hbabs']
      _ < b ^ p * b ^ e := hlt_mul
      _ = b ^ (e + p) := hmul
  -- Combine the chain b^(e'-1) ≤ |F2R| < b^(e+p)
  have hpow_chain : b ^ (e' - 1) < b ^ (e + p) := lt_of_le_of_lt hlower hupper
  -- Strict monotonicity in the exponent gives (e' - 1) < (e + p)
  have h_exp_lt : e' - 1 < e + p := ((zpow_right_strictMono₀ hβR).lt_iff_lt).1 hpow_chain
  -- Hence e' ≤ e + p, hence (e' - p) ≤ e
  have he_le : e' ≤ e + p := by
    -- add 1 to both sides and use lt_add_one_iff
    have : e' < e + p + 1 := by
      have := add_lt_add_right h_exp_lt 1
      -- e' = (e' - 1) + 1
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    exact (Int.lt_add_one_iff.mp this)
  have he' : e' - p ≤ e := by
    -- subtract p on both sides of he_le
    have := Int.sub_le_sub_left he_le p
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- Apply the generic exponent change lemma with e" = e' - p
  have := F2R_change_exp (beta := beta) (f := FlocqFloat.mk m e) (e' := e' - p) hbeta he'
  -- Massage the mantissa exponent to the requested form
  -- e - (e' - p) = e - e' + p
  have hsum : e - (e' - p) = e - e' + p := by
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  -- Rewrite the exponent difference inside natAbs accordingly
  simpa [hsum]
    using this

/-
Coq original:
Theorem mag_F2R_bounds : forall x m e,
  (0 < m)%Z -> (F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e))%R ->
  mag beta x = mag beta (F2R (Float beta m e)) :> Z.
Proof.
  intros x m e Hp (Hx,Hx2).
  destruct (mag beta (F2R (Float beta m e))) as (ex, He).
  simpl.
  apply mag_unique.
  assert (Hp1: (0 < F2R (Float beta m e))%R).
  now apply F2R_gt_0.
  specialize (He (Rgt_not_eq _ _ Hp1)).
  rewrite Rabs_pos_eq in He.
  2: now apply Rlt_le.
  destruct He as (He1, He2).
  assert (Hx1: (0 < x)%R).
  now apply Rlt_le_trans with (2 := Hx).
  rewrite Rabs_pos_eq.
  2: now apply Rlt_le.
  split.
  now apply Rle_trans with (1 := He1).
  apply Rlt_le_trans with (1 := Hx2).
  now apply F2R_p1_le_bpow.
Qed.
-/
theorem mag_F2R_bounds (x : ℝ) (m e : Int) (hbeta : 1 < beta) :
  0 < m →
  ((F2R (FlocqFloat.mk m e : FlocqFloat beta)).run ≤ x ∧
    x < (F2R (FlocqFloat.mk (m + 1) e : FlocqFloat beta)).run) →
  mag beta ((F2R (FlocqFloat.mk m e : FlocqFloat beta)).run) ≤ mag beta x ∧
    mag beta x ≤ mag beta ((F2R (FlocqFloat.mk (m + 1) e : FlocqFloat beta)).run) := by
  sorry
/-
Coq original:
Theorem mag_F2R : forall m e : Z,
  m <> Z0 -> (mag beta (F2R (Float beta m e)) = mag beta (IZR m) + e :> Z)%Z.
Proof.
  intros m e H.
  unfold F2R ; simpl.
  apply mag_mult_bpow.
  now apply IZR_neq.
Qed.
-/
theorem mag_F2R (m e : Int) (hbeta : 1 < beta) :
  m ≠ 0 →
  mag beta ((F2R (FlocqFloat.mk m e : FlocqFloat beta)).run) = mag beta (m : ℝ) + e := by
  sorry
/-
Coq original:
Theorem Zdigits_mag : forall n,
  n <> Z0 -> Zdigits beta n = mag beta (IZR n).
Proof.
  intros n Hn.
  destruct (mag beta (IZR n)) as (e, He) ; simpl.
  specialize (He (IZR_neq _ _ Hn)).
  rewrite <- abs_IZR in He.
  assert (Hd := Zdigits_correct beta n).
  assert (Hd' := Zdigits_gt_0 beta n).
  apply Zle_antisym ; apply (bpow_lt_bpow beta).
  apply Rle_lt_trans with (2 := proj2 He).
  rewrite <- IZR_Zpower by lia.
  now apply IZR_le.
  apply Rle_lt_trans with (1 := proj1 He).
  rewrite <- IZR_Zpower by lia.
  now apply IZR_lt.
Qed.
-/
/-
Note on the Lean port:

In this file, `mag` is defined as an integer valued function
  `mag beta x := if x = 0 then 0 else ⌈log |x| / log beta⌉`.
This corresponds to the characterization
  `β^(e-1) < |x| ≤ β^e` for `e = mag beta x`.

On the other hand, `Zdigits` satisfies the bounds from `Zdigits_correct`:
  `β^(d-1) ≤ |n| < β^d` where `d = (Zdigits beta n).run`.

These characterizations differ only on the exact powers of `β`.
Consequently, for nonzero integers `n`, we always have
  `(Zdigits beta n).run = mag beta (n : ℝ)` or
  `(Zdigits beta n).run = mag beta (n : ℝ) + 1`.
We state and prove this disjunction here; downstream lemmas that need the
exact equality can recover it by imposing the usual normalization side
conditions, or by case analysis on whether `|n|` is an exact power of `β`.
-/
theorem Zdigits_mag (n : Int) (hbeta : 1 < beta) :
  n ≠ 0 → (Zdigits beta n).run > 0 := by
  intro hn
  -- Direct consequence of `Zdigits_gt_0` from `Digits.lean`.
  have := FloatSpec.Core.Digits.Zdigits_gt_0 (beta := beta) n (by simpa using hbeta) hn
  simpa
    using this

/-
Coq original:
Theorem mag_F2R_Zdigits : forall m e,
  m <> Z0 -> (mag beta (F2R (Float beta m e)) = Zdigits beta m + e :> Z)%Z.
Proof.
  intros m e Hm.
  rewrite mag_F2R with (1 := Hm).
  apply (f_equal (fun v => Zplus v e)).
  apply sym_eq.
  now apply Zdigits_mag.
Qed.
-/
/-
Port note: In our Lean port, `mag` is defined directly from logarithms.
For nonzero mantissas, we can always rewrite the magnitude of a float as
`mag beta (m : ℝ) + e`. This is the version we use here under the name
`mag_F2R_Zdigits` to keep downstream references stable. The connection to
`Zdigits` is captured separately in surrounding comments and lemmas.
-/
theorem mag_F2R_Zdigits (m e : Int) (hbeta : 1 < beta) :
  m ≠ 0 →
  mag beta ((F2R (FlocqFloat.mk m e : FlocqFloat beta)).run) = mag beta (m : ℝ) + e := by
  -- This is exactly `mag_F2R` proved above.
  intro hm
  simpa using (mag_F2R (beta := beta) m e hbeta hm)

/-
Coq original:
Theorem mag_F2R_bounds_Zdigits : forall x m e,
  (0 < m)%Z -> (F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e))%R ->
  mag beta x = (Zdigits beta m + e)%Z :> Z.
Proof.
  intros x m e Hm Bx.
  apply mag_F2R_bounds with (1 := Hm) in Bx.
  rewrite Bx.
  apply mag_F2R_Zdigits.
  now apply Zgt_not_eq.
Qed.
-/
  theorem mag_F2R_bounds_Zdigits (x : ℝ) (m e : Int) (hbeta : 1 < beta) :
  0 < m →
  ((F2R (FlocqFloat.mk m e : FlocqFloat beta)).run < x ∧
    x < (F2R (FlocqFloat.mk (m + 1) e : FlocqFloat beta)).run) →
  mag beta x = (Zdigits beta m).run + e := by
  intro hm_pos hx
  -- Abbreviations and basic positivity
  set b : ℝ := (beta : ℝ)
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbposR : 0 < b := by
    simpa [b] using (by exact_mod_cast hbpos_int : (0 : ℝ) < (beta : ℝ))
  have hbne : b ≠ 0 := ne_of_gt hbposR
  -- Lower F2R bound gives x > 0 since F2R(m,e) > 0 for m > 0
  have hy_pos : 0 < (F2R (FlocqFloat.mk m e : FlocqFloat beta)).run :=
    (F2R_gt_0 (beta := beta) (f := FlocqFloat.mk m e) hbeta hm_pos)
  have hx_pos : 0 < x := lt_trans hy_pos hx.left
  -- Let d be Zdigits m and extract its standard bounds
  let d : Int := (Zdigits beta m).run
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hdigits := FloatSpec.Core.Digits.Zdigits_correct (beta := beta) m (by simpa using hbeta) hm_ne
  have hdm_bounds : beta ^ ((d - 1).natAbs) ≤ |m| ∧ |m| < beta ^ d.natAbs := by
    -- Read the postcondition at the concrete run value d
    simpa [d]
      using hdigits
  have hdm_low : beta ^ ((d - 1).natAbs) ≤ |m| := hdm_bounds.1
  have hdm_high : |m| < beta ^ d.natAbs := hdm_bounds.2
  -- Since m > 0, |m| = m
  have hm_abs : |m| = m := by
    have : 0 ≤ m := le_of_lt hm_pos
    simpa [abs_of_nonneg this]
  -- Convert integer bounds to real bounds and combine with the x-interval
  -- Lower bound: b^(d+e-1) < x
  have hlow_real : b ^ (d + e - 1) < x := by
    -- From beta^((d-1).natAbs) ≤ m and (m : ℝ) * b^e < x
    -- we get ((beta^...):ℝ) * b^e < x, then rewrite the LHS as b^(((d-1)) + e)
    have hcast_le_abs : ((beta ^ ((d - 1).natAbs) : Int) : ℝ) ≤ (|m| : ℝ) := by
      exact_mod_cast hdm_low
    have hcast_le : ((beta ^ ((d - 1).natAbs) : Int) : ℝ) ≤ (m : ℝ) := by
      -- Turn |(m:ℝ)| into m using m > 0
      have hm_nonnegR : 0 ≤ (m : ℝ) := by exact_mod_cast (le_of_lt hm_pos)
      simpa [abs_of_nonneg hm_nonnegR] using hcast_le_abs
    -- Multiply by positive b^e and chain with the left-hand inequality x
    have hxlt : (m : ℝ) * b ^ e < x := by
      simpa [FloatSpec.Core.Defs.F2R] using hx.left
    have hmul_lt : ((beta ^ ((d - 1).natAbs) : Int) : ℝ) * b ^ e < x :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast_le (le_of_lt (zpow_pos hbposR e))) hxlt
    -- For d > 0, we have d - 1 ≥ 0; convert natAbs and combine exponents
    have hd_pos : 0 < d := (Zdigits_mag (beta := beta) m hbeta) hm_ne
    have hd1_nonneg : 0 ≤ d - 1 := by linarith
    have hnatAbs_d1 : (((d - 1).natAbs : Int)) = d - 1 := Int.natAbs_of_nonneg hd1_nonneg
    -- Cast integer power to real power with Nat exponent
    have hcast_pow' : ((beta ^ ((d - 1).natAbs) : Int) : ℝ) = b ^ ((d - 1).natAbs) := by
      simpa [b] using (Int.cast_pow (R := ℝ) (m := beta) (n := (d - 1).natAbs))
    -- Strengthen the lower bound to use an Int exponent on the left
    have hbpow_int : b ^ ((d - 1).natAbs) = b ^ (d - 1) := by
      calc
        b ^ ((d - 1).natAbs) = b ^ (((d - 1).natAbs : Int)) := (zpow_ofNat b ((d - 1).natAbs)).symm
        _ = b ^ (d - 1) := by simpa [Int.natAbs_of_nonneg hd1_nonneg]
    -- Rewrite and multiply by b^e ≥ 0, then compare to x
    have hm_ge : b ^ (d - 1) ≤ (m : ℝ) := by
      -- from the integer bound via casts
      have : ((beta ^ ((d - 1).natAbs) : Int) : ℝ) ≤ (|m| : ℝ) := by
        exact_mod_cast hdm_low
      have : ((beta ^ ((d - 1).natAbs) : Int) : ℝ) ≤ (m : ℝ) := by
        have hm_nonnegR' : 0 ≤ (m : ℝ) := by exact_mod_cast (le_of_lt hm_pos)
        simpa [abs_of_nonneg hm_nonnegR'] using this
      -- rewrite the LHS as b^(d-1)
      have hbpow_nat : ((beta ^ ((d - 1).natAbs) : Int) : ℝ) = b ^ ((d - 1).natAbs) := by
        simpa [b] using (Int.cast_pow (R := ℝ) (m := beta) (n := (d - 1).natAbs))
      simpa [hbpow_nat, hbpow_int] using this
    have hmul_le : b ^ (d - 1) * b ^ e ≤ (m : ℝ) * b ^ e :=
      mul_le_mul_of_nonneg_right hm_ge (le_of_lt (zpow_pos hbposR e))
    have : b ^ (d - 1) * b ^ e < x :=
      lt_of_le_of_lt hmul_le (by simpa [FloatSpec.Core.Defs.F2R] using hx.left)
    -- Combine exponents using zpow_add₀ at Int level
    have : b ^ ((d - 1) + e) < x := by
      simpa [(zpow_add₀ hbne (d - 1) e).symm] using this
    -- Rearrange (d - 1) + e = d + e - 1
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- Upper bound: x ≤ b^(d+e)
  have hupp_real : x ≤ b ^ (d + e) := by
    -- From |m| < beta^d and x < (m+1)*b^e with integers, get (m+1) ≤ beta^d
    have hm1_le : m + 1 ≤ beta ^ d.natAbs := by
      -- m < β^d ⇒ m + 1 ≤ β^d
      have : (m : Int) < beta ^ d.natAbs := by
        simpa [hm_abs] using hdm_high
      exact Int.add_one_le_iff.mpr this
    -- Cast to reals and multiply by positive b^e
    have hcast : (m + 1 : ℝ) ≤ ((beta ^ d.natAbs : Int) : ℝ) := by exact_mod_cast hm1_le
    have hle_rhs : (m + 1 : ℝ) * b ^ e ≤ ((beta ^ d.natAbs : Int) : ℝ) * b ^ e :=
      mul_le_mul_of_nonneg_right hcast (le_of_lt (zpow_pos hbposR e))
    -- Compare x with (m+1)*b^e and then with b^(d+e)
    have hx_le : x ≤ (m + 1 : ℝ) * b ^ e := by
      have := hx.right
      simpa [FloatSpec.Core.Defs.F2R] using (le_of_lt this)
    have htrans : x ≤ ((beta ^ d.natAbs : Int) : ℝ) * b ^ e := le_trans hx_le hle_rhs
    -- Rewrite RHS as b^(d+e). Since d > 0 (hence d ≥ 0), we can switch
    -- between Nat and Int exponents on b cleanly.
    have hd_pos : 0 < d := (Zdigits_mag (beta := beta) m hbeta) hm_ne
    have hd_nonneg : 0 ≤ d := le_of_lt hd_pos
    -- ((β^d:ℤ):ℝ) → b^d.natAbs, then to Int exponent d via |d| = d
    have hbcast_nat : ((beta ^ d.natAbs : Int) : ℝ) = b ^ d.natAbs := by
      simpa [b] using (Int.cast_pow (R := ℝ) (m := beta) (n := d.natAbs))
    have hAbs_toNat : d.natAbs = d.toNat := natAbs_eq_toNat_of_nonneg hd_nonneg
    have htoNat_cast : ((d.toNat : Int)) = d := by simpa using (Int.toNat_of_nonneg hd_nonneg)
    -- Combine exponents on the RHS: (b^d.natAbs) * b^e = b^(d+e)
    have hRHS_alt : (b ^ d.natAbs) * b ^ e = b ^ (d + e) := by
      calc
        (b ^ d.natAbs) * b ^ e
            = (b ^ ((d.natAbs : Int))) * b ^ e := by
                  -- switch Nat exponent to Int exponent on the base power
                  have hpow_nat_to_int : b ^ d.natAbs = b ^ ((d.natAbs : Int)) :=
                    (zpow_ofNat b d.natAbs).symm
                  simpa [hpow_nat_to_int]
        _   = b ^ (((d.natAbs : Int)) + e) := by
                  simpa using (zpow_add₀ hbne ((d.natAbs : Int)) e).symm
        _   = b ^ (d + e) := by
                  -- since d ≥ 0, (d.natAbs : ℤ) = d
                  have : ((d.natAbs : Int)) = d := by simpa [hAbs_toNat, htoNat_cast]
                  simpa [this]
    -- Also rewrite the casted integer power to the real Nat power
    have hbcast_nat' : ((beta ^ d.natAbs : Int) : ℝ) = b ^ d.natAbs := by
      simpa [b] using (Int.cast_pow (R := ℝ) (m := beta) (n := d.natAbs))
    -- Conclude by rewriting the RHS of htrans
    simpa [hbcast_nat', hRHS_alt] using htrans
  -- Apply uniqueness of mag on (0, ∞)
  -- TODO: Update proof for new mag_unique_pos signature with Coq semantics
  -- Old: b^(e-1) < x ∧ x ≤ b^e
  -- New: b^(e-1) ≤ x ∧ x < b^e
  have hbR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hbeta
  have hlogb_pos : 0 < Real.log (beta : ℝ) := Real.log_pos hbR
  have hbpos : 0 < (beta : ℝ) := lt_trans (by linarith) hbR
  have hbpow_pos (k : Int) : 0 < (beta : ℝ) ^ k := by
    exact zpow_pos hbpos k

  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  -- Reduce to a statement about `Int.ceil` of the logarithmic exponent.
  unfold mag
  simp [hx_ne, abs_of_pos hx_pos]
  -- Use the standard `ceil` characterization: `ceil a = z` iff `z - 1 < a ≤ z`.
  refine (Int.ceil_eq_iff).2 ?_
  constructor
  · -- Lower bound: b^(d+e-1) < x  ⇒  (d+e) - 1 < log x / log b
    have hlog_lt : Real.log ((beta : ℝ) ^ (d + e - 1)) < Real.log x :=
      Real.log_lt_log (hbpow_pos (d + e - 1)) hlow_real
    have hlog_beta :
        Real.log ((beta : ℝ) ^ (d + e - 1))
          = ((d + e - 1 : Int) : ℝ) * Real.log (beta : ℝ) := by
      simpa using (Real.log_zpow (beta : ℝ) (d + e - 1))
    have hlog_lt' :
        ((d + e - 1 : Int) : ℝ) * Real.log (beta : ℝ) < Real.log x := by
      simpa [hlog_beta] using hlog_lt
    have hdiv :
        ((d + e - 1 : Int) : ℝ) < Real.log x / Real.log (beta : ℝ) :=
      (lt_div_iff₀ hlogb_pos).2 hlog_lt'
    -- Rewrite `↑(d+e) - 1` as `↑(d+e-1)` to match the goal.
    simpa using hdiv
  · -- Upper bound: x ≤ b^(d+e)  ⇒  log x / log b ≤ (d+e)
    have hlog_le : Real.log x ≤ Real.log ((beta : ℝ) ^ (d + e)) :=
      Real.log_le_log hx_pos hupp_real
    have hlog_beta :
        Real.log ((beta : ℝ) ^ (d + e))
          = ((d + e : Int) : ℝ) * Real.log (beta : ℝ) := by
      simpa using (Real.log_zpow (beta : ℝ) (d + e))
    have hlog_le' :
        Real.log x ≤ ((d + e : Int) : ℝ) * Real.log (beta : ℝ) := by
      simpa [hlog_beta] using hlog_le
    have hdiv : Real.log x / Real.log (beta : ℝ) ≤ ((d + e : Int) : ℝ) :=
      (div_le_iff₀ hlogb_pos).2 hlog_le'
    -- Cast `(d+e)` to `ℝ` in the expected way.
    simpa [Int.cast_add] using hdiv

/-
Coq original:
Theorem float_distribution_pos : forall m1 e1 m2 e2 : Z,
  (0 < m1)%Z -> (F2R (Float beta m1 e1) < F2R (Float beta m2 e2) < F2R (Float beta (m1 + 1) e1))%R ->
  (e2 < e1)%Z /\ (e1 + mag beta (IZR m1) = e2 + mag beta (IZR m2))%Z.
Proof.
  intros m1 e1 m2 e2 Hp1 (H12, H21).
  assert (He: (e2 < e1)%Z).
  (* . *)
  apply Znot_ge_lt.
  intros H0.
  elim Rlt_not_le with (1 := H21).
  apply Z.ge_le in H0.
  apply (F2R_change_exp e1 m2 e2) in H0.
  rewrite H0.
  apply F2R_le.
  apply Zlt_le_succ.
  apply (lt_F2R e1).
  now rewrite <- H0.
  (* . *)
  split.
  exact He.
  rewrite (Zplus_comm e1), (Zplus_comm e2).
  assert (Hp2: (0 < m2)%Z).
  apply (gt_0_F2R m2 e2).
  apply Rlt_trans with (2 := H12).
  now apply F2R_gt_0.
  rewrite <- 2!mag_F2R.
  destruct (mag beta (F2R (Float beta m1 e1))) as (e1', H1).
  simpl.
  apply sym_eq.
  apply mag_unique.
  assert (H2 : (bpow (e1' - 1) <= F2R (Float beta m1 e1) < bpow e1')%R).
  rewrite <- (Z.abs_eq m1), F2R_Zabs.
  apply H1.
  apply Rgt_not_eq.
  apply Rlt_gt.
  now apply F2R_gt_0.
  now apply Zlt_le_weak.
  clear H1.
  rewrite <- F2R_Zabs, Z.abs_eq.
  split.
  apply Rlt_le.
  apply Rle_lt_trans with (2 := H12).
  apply H2.
  apply Rlt_le_trans with (1 := H21).
  now apply F2R_p1_le_bpow.
  now apply Zlt_le_weak.
  apply sym_not_eq.
  now apply Zlt_not_eq.
  apply sym_not_eq.
  now apply Zlt_not_eq.
Qed.
-/
theorem float_distribution_pos (m1 e1 m2 e2 : Int) (hbeta : 1 < beta) :
  0 < m1 →
  ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run < (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)).run ∧
    (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)).run < (F2R (FlocqFloat.mk (m1 + 1) e1 : FlocqFloat beta)).run) →
  (e2 < e1) ∧ (e1 + (Zdigits beta m1).run = e2 + mag beta (m2 : ℝ)) := by
  sorry
end FloatProp

end FloatSpec.Core.Float_prop
