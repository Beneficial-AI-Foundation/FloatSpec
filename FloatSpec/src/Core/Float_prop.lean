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
  -- Use the ≤-equivalence with m1=0, m2=f.Fnum
  have hiff := le_F2R (beta := beta) f.Fexp 0 f.Fnum hbeta
  -- Rewrite F2R 0 = 0
  have : (F2R (FlocqFloat.mk 0 f.Fexp : FlocqFloat beta)).run ≤ (F2R (FlocqFloat.mk f.Fnum f.Fexp : FlocqFloat beta)).run := by
    simpa [F2R_0 (beta := beta) (e := f.Fexp) hbeta]
  exact hiff.mpr this

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
  -- Use the ≤-equivalence with m1=f.Fnum, m2=0
  have hiff := le_F2R (beta := beta) f.Fexp f.Fnum 0 hbeta
  have : (F2R (FlocqFloat.mk f.Fnum f.Fexp : FlocqFloat beta)).run ≤ (F2R (FlocqFloat.mk 0 f.Fexp : FlocqFloat beta)).run := by
    simpa [F2R_0 (beta := beta) (e := f.Fexp) hbeta]
  exact hiff.mpr this

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
  -- Use the <-equivalence with m1=0, m2=f.Fnum
  have hiff := lt_F2R (beta := beta) f.Fexp 0 f.Fnum hbeta
  have : (F2R (FlocqFloat.mk 0 f.Fexp : FlocqFloat beta)).run < (F2R (FlocqFloat.mk f.Fnum f.Fexp : FlocqFloat beta)).run := by
    simpa [F2R_0 (beta := beta) (e := f.Fexp) hbeta]
  exact hiff.mpr this

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
  -- Use the <-equivalence with m1=f.Fnum, m2=0
  have hiff := lt_F2R (beta := beta) f.Fexp f.Fnum 0 hbeta
  have : (F2R (FlocqFloat.mk f.Fnum f.Fexp : FlocqFloat beta)).run < (F2R (FlocqFloat.mk 0 f.Fexp : FlocqFloat beta)).run := by
    simpa [F2R_0 (beta := beta) (e := f.Fexp) hbeta]
  exact hiff.mpr this

-- Forward direction sign properties

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
  sorry

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
theorem F2R_lt_bpow (f : FlocqFloat beta) (hbeta : 1 < beta) :
  f.Fnum < 0 → -((beta : ℝ) ^ (f.Fexp + 1)) < (F2R f).run := by
  sorry

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
  sorry
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
  sorry

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
  mag beta x = mag beta ((F2R (FlocqFloat.mk m e : FlocqFloat beta)).run) := by
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
theorem Zdigits_mag (n : Int) (hbeta : 1 < beta) :
  n ≠ 0 → (Zdigits beta n).run = mag beta (n : ℝ) := by
  sorry

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
theorem mag_F2R_Zdigits (m e : Int) (hbeta : 1 < beta) :
  m ≠ 0 →
  mag beta ((F2R (FlocqFloat.mk m e : FlocqFloat beta)).run) = (Zdigits beta m).run + e := by
  sorry

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
  ((F2R (FlocqFloat.mk m e : FlocqFloat beta)).run ≤ x ∧
    x < (F2R (FlocqFloat.mk (m + 1) e : FlocqFloat beta)).run) →
  mag beta x = (Zdigits beta m).run + e := by
  sorry

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
  (e2 < e1) ∧ (e1 + mag beta (m1 : ℝ) = e2 + mag beta (m2 : ℝ)) := by
  sorry

end FloatProp

end FloatSpec.Core.Float_prop
