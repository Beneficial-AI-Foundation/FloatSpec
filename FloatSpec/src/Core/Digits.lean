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
import FloatSpecRoles
import FloatSpec.VersoExt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Std.Do.Triple
import Std.Tactic.Do
import FloatSpec.src.SimprocWP

open Real
open Std.Do
open scoped Int

namespace FloatSpec.Core.Digits

universe u

section DigitOperations

variable (beta : Int) (h_beta : beta > 1)

/-- Number of bits of a positive integer

    Computes the number of bits required to represent a positive natural number.
    Uses recursive division by 2 until the number becomes 0.
-/
def digits2_Pnat : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let prev := digits2_Pnat ((n + 1) / 2)
    1 + prev

/-- A pure helper with the same recursion, convenient for proofs. -/
def bits : Nat → Nat
  | 0     => 0
  | n + 1 => 1 + bits ((n + 1) / 2)

/-- Basic positivity: for n > 0, bits n > 0. -/
lemma bits_pos {n : Nat} (hn : 0 < n) : 0 < bits n := by
  cases' n with k
  · cases hn
  · simp [bits]

/-- Standard split: {lean}`n = 2 * (n / 2) + n % 2` and {lean}`n % 2 < 2`. -/
lemma split2 (n : Nat) : n = 2 * (n / 2) + n % 2 ∧ n % 2 < 2 := by
  refine ⟨?h1, ?h2⟩
  · -- The fix is to wrap the lemma in `Eq.symm` to flip the equality.
    simpa [two_mul, Nat.mul_comm] using (Eq.symm (Nat.div_add_mod n 2))
  · exact Nat.mod_lt _ (by decide)

/-- Bits of a successor: unfold recursion. -/
lemma bits_succ (k : Nat) : bits (k + 1) = 1 + bits ((k + 1) / 2) := by
  simp [bits]

/-- Equality of the program and the pure helper. -/
lemma digits2_eq_bits (n : Nat) : digits2_Pnat n = bits n := by
  refine Nat.strongRecOn n (motive := fun n => digits2_Pnat n = bits n) ?step
  intro n ih
  cases' n with k
  · simp [digits2_Pnat, bits]
  · have ih_half : digits2_Pnat ((k + 1) / 2) = bits ((k + 1) / 2) := by
      have hlt : ((k + 1) / 2) < (k + 1) := by exact Nat.div_lt_self (Nat.succ_pos _) (by decide)
      exact ih ((k + 1) / 2) hlt
    simp [digits2_Pnat, bits, ih_half]

/-- Main bounds for bits: for m > 0, 2^(bits m - 1) ≤ m < 2^(bits m). -/
lemma bits_bounds (m : Nat) (hm : 0 < m) :
    let d := bits m
    2 ^ (d - 1) ≤ m ∧ m < 2 ^ d := by
  refine (Nat.strongRecOn m (motive := fun m => 0 < m → let d := bits m; 2 ^ (d - 1) ≤ m ∧ m < 2 ^ d) ?step) hm
  intro m ih hmpos
  cases' m with k
  · cases hmpos
  · cases' k with k0
    · -- m = 1
      have hb : bits 1 = 1 := by simp [bits]
      constructor
      · -- lower bound
        simp [hb]
      · -- upper bound
        simp [hb]
    · -- m = k0 + 2 ≥ 2
      -- Decompose by division by 2
      have hsplit := split2 (k0 + 2)
      let m2 := (k0 + 2) / 2
      have hdecomp : (k0 + 2) = 2 * m2 + (k0 + 2) % 2 := (hsplit).1
      have hrem_lt2 : (k0 + 2) % 2 < 2 := (hsplit).2
      have hlt : m2 < (k0 + 2) := by exact Nat.div_lt_self (Nat.succ_pos _) (by decide)
      -- m2 > 0 since k0+2 ≥ 2
      have hge2 : 2 ≤ k0 + 2 := by exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k0))
      have hm2pos : 0 < m2 := Nat.div_pos hge2 (by decide)
      -- Apply IH to m2
      have ih_m2 := ih m2 hlt hm2pos
      -- Notations
      set b := bits m2 with hbdef
      have bits_succ2 : bits (k0 + 2) = 1 + bits m2 := by
        -- use the general successor lemma and rewrite the divisor
        simpa [m2, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (bits_succ (k := k0 + 1))
      -- Lower bound: 2^b ≤ k0+2
      have hbpos : 0 < b := by simpa [hbdef] using (bits_pos (n := m2) hm2pos)
      have low_m2 : 2 ^ (b - 1) ≤ m2 := by
        simpa [hbdef] using (ih_m2).1
      have low_pow : 2 ^ b ≤ 2 * m2 := by
        -- 2^(b) = 2 * 2^(b-1) and 2^(b-1) ≤ m2
        have h2_mul : 2 * (2 ^ (b - 1)) ≤ 2 * m2 := Nat.mul_le_mul_left 2 low_m2
        have hpow : 2 * 2 ^ (b - 1) = 2 ^ b := by
          have hb' : (b - 1) + 1 = b := Nat.sub_add_cancel (Nat.succ_le_of_lt hbpos)
          calc
            2 * 2 ^ (b - 1) = 2 ^ (b - 1) * 2 := by simp [Nat.mul_comm]
            _ = 2 ^ ((b - 1) + 1) := by simp [Nat.pow_succ]
            _ = 2 ^ b := by simp [hb']
        simpa [hpow] using h2_mul
      have low_n : 2 ^ b ≤ (k0 + 2) := by
        have hle_n : 2 * m2 ≤ k0 + 2 := by
          -- rewrite RHS using decomposition, then apply monotonicity
          rw [hdecomp]
          exact Nat.le_add_right _ _
        exact le_trans low_pow hle_n
      -- Upper bound: k0+2 < 2^(b+1)
      have m2_lt_pow : m2 < 2 ^ b := by simpa [hbdef] using (ih_m2).2
      have two_m2_add_r_lt : 2 * m2 + (k0 + 2) % 2 < 2 * (m2 + 1) := by
        have hrem_le_one : (k0 + 2) % 2 ≤ 1 := Nat.le_of_lt_succ hrem_lt2
        have hlt_add : 2 * m2 + (k0 + 2) % 2 < 2 * m2 + 2 :=
          Nat.add_lt_add_left (lt_of_le_of_lt hrem_le_one (by decide)) _
        -- rewrite 2*m2 + 2 = 2*(m2+1)
        have hco : 2 * m2 + 2 = 2 * (m2 + 1) := by
          calc
            2 * m2 + 2 = 2 * m2 + 2 * 1 := by simp
            _ = 2 * (m2 + 1) := by
              have := (Nat.mul_add 2 m2 1)
              simpa [two_mul] using this.symm
        simpa [hco] using hlt_add
      have up_n : (k0 + 2) < 2 ^ (b + 1) := by
        have h1 : (k0 + 2) < 2 * (m2 + 1) := by
          calc
            (k0 + 2) = 2 * m2 + (k0 + 2) % 2 := hdecomp
            _ < 2 * (m2 + 1) := two_m2_add_r_lt
        have h2 : 2 * (m2 + 1) ≤ 2 * (2 ^ b) := by exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt m2_lt_pow)
        have h3 : (k0 + 2) < 2 * (2 ^ b) := lt_of_lt_of_le h1 h2
        have : 2 * 2 ^ b = 2 ^ (b + 1) := by simp [Nat.pow_succ, Nat.mul_comm]
        exact (lt_of_lt_of_eq h3 this)
      -- Translate bounds via bits (k0+2) = 1 + bits m2
      have hidx : bits (k0 + 2) - 1 = bits m2 := by
        -- (1 + bits m2) - 1 = bits m2
        simp [bits_succ2]
      have low_n' : 2 ^ (bits (k0 + 2) - 1) ≤ (k0 + 2) := by
        -- rewrite exponent index using hidx
        simpa [hidx] using low_n
      have up_n' : (k0 + 2) < 2 ^ (bits (k0 + 2)) := by
        -- rewrite exponent using bits_succ2 and b = bits m2
        simpa [bits_succ2, hbdef, Nat.add_comm] using up_n
      exact ⟨low_n', up_n'⟩

/-- Correctness of binary bit count

Coq theorem and proof:
```raw
Theorem digits2_Pnat_correct :
  forall n,
  let d := digits2_Pnat n in
  (Zpower_nat 2 d <= Zpos n < Zpower_nat 2 (S d))%Z.
Proof.
intros n d. unfold d. clear.
assert (Hp: forall m, (Zpower_nat 2 (S m) = 2 * Zpower_nat 2 m)%Z) by easy.
induction n ; simpl digits2_Pnat.
rewrite Zpos_xI, 2!Hp.
lia.
rewrite (Zpos_xO n), 2!Hp.
lia.
now split.
Qed.
```
-/
theorem digits2_Pnat_correct (n : Nat) :
    ⦃⌜n > 0⌝⦄
    (pure (digits2_Pnat n) : Id _)
    ⦃⇓d => ⌜d > 0 ∧ 2 ^ (d - 1) ≤ n ∧ n < 2 ^ d⌝⦄ := by
  intro hn
  have hb := bits_bounds n hn
  have dpos := bits_pos (n := n) hn
  -- Reduce the program to the pure helper and discharge the proposition
  simpa [digits2_eq_bits n] using And.intro dpos (And.intro hb.1 hb.2)

/-- Extract the k-th digit of a number n in the given radix

    Note: Lean's {name}`Int.ediv` and {name}`Int.emod` (notation / and %) use
    Euclidean semantics. The original Flocq proofs for digits rely on
    truncation-toward-zero for the division when bounding by powers. To match
    that proof style (e.g., {lit}`Z.quot_small`), we use truncated division
    {name}`Int.tdiv` here. This ensures that for |n| < beta^k with 0 ≤ k,
    the quotient is 0, and hence the digit is 0.
-/
def Zdigit (n k : Int) : Int :=
  (if k ≥ 0 then (Int.tdiv n (beta ^ k.natAbs)) % beta else 0)

/-- Digits with negative index are zero

Coq theorem and proof:
```raw
Theorem Zdigit_lt :
  forall n k,
  (k < 0)%Z ->
  Zdigit n k = Z0.
Proof.
intros n [|k|k] Hk ; try easy.
now case n.
Qed.
```
-/
theorem Zdigit_lt (n k : Int) :
    ⦃⌜k < 0⌝⦄
    (pure (Zdigit beta n k) : Id _)
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro hk
  unfold Zdigit
  simp [show ¬(k ≥ 0) from not_le.mpr hk]

/-- Digit of zero is always zero

Coq theorem and proof:
```raw
Theorem Zdigit_0 :
  forall k, Zdigit 0 k = Z0.
Proof.
intros k.
unfold Zdigit.
rewrite Zquot_0_l.
apply Zrem_0_l.
Qed.
```
-/
theorem Zdigit_0 (k : Int) :
    ⦃⌜True⌝⦄
    (pure (Zdigit beta 0 k) : Id _)
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro _
  unfold Zdigit
  split <;> simp

/-- Digit of opposite number

Coq theorem and proof:
```raw
Theorem Zdigit_opp :
  forall n k,
  Zdigit (-n) k = Z.opp (Zdigit n k).
Proof.
intros n k.
unfold Zdigit.
rewrite Zquot_opp_l.
apply Zrem_opp_l.
Qed.
```
-/
theorem Zdigit_opp (n k : Int) :
    ⦃⌜True⌝⦄
    (pure (Zdigit beta (-n) k) : Id _)
    ⦃⇓result => ⌜∃ orig_result, Zdigit beta n k = orig_result ∧
                  result = if k ≥ 0 then (Int.tdiv (-n) (beta ^ k.natAbs)) % beta else 0⌝⦄ := by
  intro _
  unfold Zdigit
  use (if k ≥ 0 then (Int.tdiv n (beta ^ k.natAbs)) % beta else 0)
  constructor
  · rfl
  · simp

/-- Digit is zero for large indices

Coq theorem and proof:
```raw
Theorem Zdigit_ge_Zpower_pos :
  forall e n,
  (0 <= n < Zpower beta e)%Z ->
  forall k, (e <= k)%Z -> Zdigit n k = Z0.
Proof.
intros e n Hn k Hk.
unfold Zdigit.
rewrite Z.quot_small.
apply Zrem_0_l.
split.
apply Hn.
apply Z.lt_le_trans with (1 := proj2 Hn).
replace k with (e + (k - e))%Z by ring.
rewrite Zpower_plus.
rewrite <- (Zmult_1_r (beta ^ e)) at 1.
apply Zmult_le_compat_l.
apply (Zlt_le_succ 0).
apply Zpower_gt_0.
now apply Zle_minus_le_0.
apply Zlt_le_weak.
now apply Z.le_lt_trans with n.
generalize (Z.le_lt_trans _ _ _ (proj1 Hn) (proj2 Hn)).
clear.
now destruct e as [|e|e].
now apply Zle_minus_le_0.
Qed.
```
-/
theorem Zdigit_ge_Zpower_pos (n e : Int) :
    ⦃⌜0 ≤ n ∧ n < beta ^ e.natAbs ∧ 0 ≤ e⌝⦄
    (pure (Zdigit beta n e) : Id _)
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro ⟨hn_pos, hn_bound, he_pos⟩
  unfold Zdigit
  -- With k = e ≥ 0, the branch is active; truncated quotient is 0 under the bound
  simp [he_pos, Int.tdiv_eq_zero_of_lt hn_pos hn_bound]

/-- Digit is zero for large indices (general case)

Coq theorem and proof:
```raw
Theorem Zdigit_ge_Zpower :
  forall e n,
  (Z.abs n < Zpower beta e)%Z ->
  forall k, (e <= k)%Z -> Zdigit n k = Z0.
Proof.
intros e n Hn k Hk.
destruct (Zle_or_lt 0 n) as [H|H].
apply Zdigit_ge_Zpower_pos.
now split.
exact Hk.
destruct (Zle_or_lt 0 k) as [H0|H0].
unfold Zdigit.
rewrite Z.quot_small.
apply Zrem_0_l.
split.
apply Z.opp_le_mono in Hn.
rewrite Z.opp_involutive in Hn.
apply Zle_trans with (2 := Hn).
apply Zopp_le_cancel.
rewrite Z.opp_involutive.
generalize (Zpower_ge_0 beta e).
clear -H ; lia.
apply Z.opp_lt_mono in Hn.
rewrite Z.opp_involutive in Hn.
apply Z.lt_le_trans with (1 := Hn).
apply Zpower_le.
exact Hk.
now rewrite Zdigit_lt.
Qed.
```
-/
theorem Zdigit_ge_Zpower (n e : Int) :
    ⦃⌜Int.natAbs n < beta ^ e.natAbs ∧ 0 ≤ e⌝⦄
    (pure (Zdigit beta n e) : Id _)
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro ⟨hn_bound, he_pos⟩
  unfold Zdigit
  simp [he_pos]
  -- Let b = beta^e
  set b := beta ^ e.natAbs with hb
  have hquot0 : Int.tdiv n b = 0 := by
    -- Prove truncated quotient is zero using a sign split on n
    by_cases hn : 0 ≤ n
    · -- Nonnegative case: natAbs n = n, so n < b by the hypothesis
      have : n < b := by
        -- coe (natAbs n) = n under hn
        simpa [hb, Int.natAbs_of_nonneg hn] using hn_bound
      exact Int.tdiv_eq_zero_of_lt hn this
    · -- Negative case: use truncated-division sign law and apply the bound to -n
      have hnlt : n < 0 := lt_of_not_ge hn
      have hneg_nonneg : 0 ≤ -n := by exact (neg_nonneg.mpr (le_of_lt hnlt))
      have hlt_neg : -n < b := by
        -- coe (natAbs n) = -n when n < 0
        have : (n.natAbs : Int) = -n := by
          -- from natAbs_neg and natAbs_of_nonneg applied to -n
          have := Int.natAbs_neg n
          -- ((-n).natAbs = n.natAbs) so coe both sides:
          -- ↑((-n).natAbs) = ↑(n.natAbs)
          -- but ↑((-n).natAbs) = -n since -n ≥ 0
          have hcoe : ((-n).natAbs : Int) = -n := Int.natAbs_of_nonneg hneg_nonneg
          -- combine equalities to rewrite
          simpa [this] using hcoe
        simpa [this, hb] using hn_bound
      -- Now apply truncated division bound to -n, then use neg_tdiv
      have : Int.tdiv (-n) b = 0 := Int.tdiv_eq_zero_of_lt hneg_nonneg hlt_neg
      -- (-n).tdiv b = - n.tdiv b, so n.tdiv b = 0
      simpa [Int.neg_tdiv] using this
  -- With zero quotient, the digit is 0 % beta = 0
  simp [hquot0]


/-- beta is positive from 1 < beta. -/
private lemma beta_pos {beta : Int} (hβ : 1 < beta) : 0 < beta :=
  lt_trans (show (0 : Int) < 1 by decide) hβ

/-- Power of a positive integer is positive. -/
private lemma pow_pos_int {beta : Int} (hβ : 0 < beta) (k : Nat) :
    0 < beta ^ k := by
  simpa using (pow_pos hβ k)

/-- Evaluate the 0-th digit: it is exactly n % beta. -/
private lemma Zdigit_at_zero (beta n : Int) :
    Zdigit beta n 0 = n % beta := by
  unfold Zdigit
  simp  -- `tdiv n 1 = n` and `0 ≥ 0` discharges the `if`

-- For nonnegative `n` and positive divisor `d`,
-- `Int.tdiv n d` equals Euclidean `n / d`.
/-- General evaluation of {name}`Zdigit` for nonnegative n and nonnegative k. -/
private lemma Zdigit_eval_nonneg
    (beta n k : Int) (_hn : 0 ≤ n) (_hb : 0 < beta) (hk : 0 ≤ k) :
    Zdigit beta n k =
      (Int.tdiv n (beta ^ k.natAbs)) % beta := by
  unfold Zdigit
  simp [hk]

/-- For 0 ≤ n and 0 < d, truncated division gives zero iff n < d. -/
private lemma tdiv_zero_iff_lt_of_nonneg_pos {n d : Int}
    (hn : 0 ≤ n) (hd : 0 < d) : Int.tdiv n d = 0 ↔ n < d := by
  constructor
  · -- If tdiv n d = 0, then n < d
    intro h_div_eq_zero
    -- Use the division algorithm: n = d * (n.tdiv d) + (n.tmod d)
    have hdiv_algo := Int.mul_tdiv_add_tmod n d
    rw [h_div_eq_zero] at hdiv_algo
    simp at hdiv_algo
    -- We have n = n.tmod d
    rw [← hdiv_algo]
    -- And 0 ≤ n.tmod d < |d| = d (since d > 0)
    have hmod_bounds := Int.tmod_lt_of_pos n hd
    exact hmod_bounds
  · -- If n < d, then tdiv n d = 0
    intro h_lt
    exact Int.tdiv_eq_zero_of_lt hn h_lt

/-- Divide-by-β associativity for truncated division on nonnegative numerators.
For n ≥ 0, beta > 0, and any k, dividing by beta^(k+1) equals
first dividing by beta and then by beta^k.
-/
private lemma tdiv_pow_succ_assoc
    (n beta : Int) (hn : 0 ≤ n) (hb : 0 < beta) (k : Nat) :
    Int.tdiv n (beta ^ (k + 1)) = Int.tdiv (Int.tdiv n beta) (beta ^ k) := by
    -- For non-negative n and positive divisors, tdiv = ediv
  have hbeta_pow : 0 < beta ^ k := pow_pos hb k
  have hbeta_pow_succ : 0 < beta ^ (k + 1) := pow_pos hb (k + 1)

  -- Convert both `tdiv` into Euclidean division using nonnegativity
  -- Left side: `tdiv n (beta^(k+1)) = n / (beta^(k+1))`
  have hL : Int.tdiv n (beta ^ (k + 1)) = n / (beta ^ (k + 1)) := by
    simpa using (Int.tdiv_eq_ediv_of_nonneg hn :
      Int.tdiv n (beta ^ (k + 1)) = n / (beta ^ (k + 1)))
  -- Right side: `tdiv (tdiv n beta) (beta^k) = (tdiv n beta) / (beta^k)`
  have hR : Int.tdiv (Int.tdiv n beta) (beta ^ k)
      = (Int.tdiv n beta) / (beta ^ k) := by
    have htdiv_nonneg : 0 ≤ Int.tdiv n beta :=
      Int.tdiv_nonneg hn (Int.le_of_lt hb)
    simpa using (Int.tdiv_eq_ediv_of_nonneg htdiv_nonneg :
      Int.tdiv (Int.tdiv n beta) (beta ^ k) = (Int.tdiv n beta) / (beta ^ k))
  -- It remains to show the Euclidean-division identity on the rhs
  -- `(n / beta) / (beta^k) = n / (beta^(k+1))`
  have hmid' : (n / beta) / (beta ^ k) = n / (beta ^ (k + 1)) := by
    -- Use `(a / b) / c = a / (b * c)` requiring `0 ≤ b` (here `b = beta`).
    have hb_nonneg : 0 ≤ beta := le_of_lt hb
    have hassoc : (n / beta) / (beta ^ k) = n / (beta * (beta ^ k)) := by
      simpa using (Int.ediv_ediv_of_nonneg hb_nonneg)
    -- Normalize powers
    simpa [pow_succ, mul_comm] using hassoc
  have hmid : n / (beta ^ (k + 1)) = (n / beta) / (beta ^ k) := hmid'.symm
  -- Replace `(tdiv n beta)` by `(n / beta)` in the right-hand expression
  have hdiv_eq : Int.tdiv n beta = n / beta := by
    simpa using (Int.tdiv_eq_ediv_of_nonneg hn : Int.tdiv n beta = n / beta)
  -- Assemble the chain of equalities
  calc
    Int.tdiv n (beta ^ (k + 1))
        = n / (beta ^ (k + 1)) := hL
    _   = (n / beta) / (beta ^ k) := hmid
    _   = (Int.tdiv n beta) / (beta ^ k) := by simpa [hdiv_eq]
    _   = Int.tdiv (Int.tdiv n beta) (beta ^ k) := by
      simpa using hR.symm

-- Base monotonicity of powers for nonnegative integers.
private lemma pow_base_mono (k : Nat) {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) :
    a ^ k ≤ b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ha_pow : 0 ≤ a ^ k := by
      have : 0 ≤ a := ha
      simpa using pow_nonneg this _
    have hb_nonneg : 0 ≤ b := le_trans ha hab
    have hb_pow : 0 ≤ b ^ k := by
      simpa using pow_nonneg hb_nonneg _
    calc
      a ^ (k + 1) = a ^ k * a := by rw [pow_succ]
      _ ≤ a ^ k * b := by exact mul_le_mul_of_nonneg_left hab ha_pow
      _ ≤ b ^ k * b := by exact mul_le_mul_of_nonneg_right ih (le_trans ha hab)
      _ = b ^ (k + 1) := by rw [pow_succ]

/-- For beta ≥ 2 and n ≠ 0, we have |n| < beta^(1 + natAbs n). -/
private lemma abs_lt_beta_pow_succ_natAbs (n : Int) (hβ : beta > 1) (_hn : n ≠ 0) :
    |n| < beta ^ (1 + n.natAbs) := by
  have hβge2 : (2 : Int) ≤ beta := by linarith
  have h_two : (n.natAbs : Int) < (2 : Int) ^ n.natAbs := by
    have : n.natAbs < 2 ^ n.natAbs := n.natAbs.lt_two_pow_self
    simpa using Int.ofNat_lt.mpr this
  have h_mono : (2 : Int) ^ n.natAbs ≤ beta ^ n.natAbs := by
    have h2_nonneg : 0 ≤ (2 : Int) := by decide
    exact pow_base_mono n.natAbs h2_nonneg hβge2
  have h_abs_nat : (n.natAbs : Int) = |n| := Int.natCast_natAbs n
  have h0 : |n| < beta ^ n.natAbs := by
    exact lt_of_lt_of_le (by simpa [h_abs_nat] using h_two) h_mono
  have hb_pos : 0 < beta := lt_trans (by decide : (0 : Int) < 1) hβ
  have pow_pos : 0 < beta ^ n.natAbs := pow_pos hb_pos _
  have step : beta ^ n.natAbs < beta ^ n.natAbs * beta := by
    have := mul_lt_mul_of_pos_left hβ pow_pos
    simpa using this
  have : |n| < beta ^ n.natAbs * beta := lt_trans h0 step
  simpa [pow_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, mul_comm]
    using this


/-- Helper lemma: For positive n, there exists k ≥ 0 such that Zdigit beta n k ≠ 0 -/
private lemma exists_nonzero_digit (beta n : Int) (hβ : beta > 1) (hn : 0 < n) :
    ∃ k, 0 ≤ k ∧ Zdigit beta n k ≠ 0 := by
  have hbpos : 0 < beta := beta_pos hβ
  have hn_nonneg : 0 ≤ n := le_of_lt hn
  have hneq : n ≠ 0 := ne_of_gt hn
  -- Pick a large enough power so truncated division is zero.
  have hlt : n < beta ^ (1 + n.natAbs) := by
    have h := abs_lt_beta_pow_succ_natAbs (beta := beta) (n := n) hβ hneq
    simpa [abs_of_nonneg hn_nonneg] using h
  have hex : ∃ k : Nat, Int.tdiv n (beta ^ k) = 0 := by
    exact ⟨1 + n.natAbs, Int.tdiv_eq_zero_of_lt hn_nonneg hlt⟩
  let k0 := Nat.find hex
  have hk0 : Int.tdiv n (beta ^ k0) = 0 := Nat.find_spec hex
  have hk0_ne : k0 ≠ 0 := by
    intro hk0_zero
    have : n = 0 := by
      simpa [hk0_zero] using hk0
    exact hneq this
  obtain ⟨k, hk0_eq⟩ := Nat.exists_eq_succ_of_ne_zero hk0_ne
  have hk_lt : k < k0 := by
    simpa [hk0_eq] using Nat.lt_succ_self k
  have hk_not_zero : Int.tdiv n (beta ^ k) ≠ 0 := by
    have hmin := Nat.find_min hex hk_lt
    simpa using hmin
  set q : Int := Int.tdiv n (beta ^ k) with hq
  have hpow_nonneg : 0 ≤ beta ^ k := by
    have hb_nonneg : 0 ≤ beta := le_of_lt hbpos
    exact pow_nonneg hb_nonneg _
  have hq_nonneg : 0 ≤ q := by
    simpa [hq] using (Int.tdiv_nonneg hn_nonneg hpow_nonneg)
  have hk0' : Int.tdiv n (beta ^ (k + 1)) = 0 := by
    simpa [hk0_eq] using hk0
  -- Associate division by beta^(k+1) as division by beta^k then beta.
  have h_assoc : Int.tdiv n (beta ^ (k + 1)) = Int.tdiv q beta := by
    have hL : Int.tdiv n (beta ^ (k + 1)) = n / (beta ^ (k + 1)) := by
      simpa using (Int.tdiv_eq_ediv_of_nonneg hn_nonneg :
        Int.tdiv n (beta ^ (k + 1)) = n / (beta ^ (k + 1)))
    have h_tdiv_eq : Int.tdiv n (beta ^ k) = n / (beta ^ k) := by
      simpa using (Int.tdiv_eq_ediv_of_nonneg hn_nonneg :
        Int.tdiv n (beta ^ k) = n / (beta ^ k))
    have hq_nonneg' : 0 ≤ n / (beta ^ k) := by
      simpa [h_tdiv_eq, hq] using hq_nonneg
    have hR : Int.tdiv q beta = (n / (beta ^ k)) / beta := by
      have hR' : Int.tdiv (n / (beta ^ k)) beta = (n / (beta ^ k)) / beta := by
        simpa using (Int.tdiv_eq_ediv_of_nonneg hq_nonneg')
      simpa [hq, h_tdiv_eq] using hR'
    have h_ediv_assoc : (n / (beta ^ k)) / beta = n / (beta ^ (k + 1)) := by
      have htmp : (n / (beta ^ k)) / beta = n / (beta ^ k * beta) := by
        simpa using (Int.ediv_ediv_of_nonneg hpow_nonneg :
          (n / (beta ^ k)) / beta = n / (beta ^ k * beta))
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using htmp
    calc
      Int.tdiv n (beta ^ (k + 1)) = n / (beta ^ (k + 1)) := hL
      _ = (n / (beta ^ k)) / beta := h_ediv_assoc.symm
      _ = Int.tdiv q beta := by simpa [hR]
  have hq_div_zero : Int.tdiv q beta = 0 := by
    simpa [h_assoc] using hk0'
  have hq_lt : q < beta :=
    (tdiv_zero_iff_lt_of_nonneg_pos hq_nonneg hbpos).1 hq_div_zero
  have hq_mod : q % beta = q := Int.emod_eq_of_lt hq_nonneg hq_lt
  have hq_ne : q ≠ 0 := by
    simpa [hq] using hk_not_zero
  refine ⟨(k : Int), ?_, ?_⟩
  · exact Int.natCast_nonneg k
  · have hk_nonneg : 0 ≤ (k : Int) := by
      exact Int.natCast_nonneg k
    have hzd : Zdigit beta n (k : Int) = q % beta := by
      simpa [hq] using
        (Zdigit_eval_nonneg (beta := beta) (n := n) (k := (k : Int))
          hn_nonneg hbpos hk_nonneg)
    intro hzero
    have hq_zero : q = 0 := by
      have : q % beta = 0 := by simpa [hzd] using hzero
      simpa [hq_mod] using this
    exact hq_ne hq_zero
theorem Zdigit_not_0_pos (n : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜0 < n⌝⦄
    (pure (Zdigit beta n 0) : Id _)
    ⦃⇓_ => ⌜∃ k, 0 ≤ k ∧ Zdigit beta n k ≠ 0⌝⦄ := by
  intro hn
  exact exists_nonzero_digit beta n hβ hn


/-- Non-zero digit exists for non-zero numbers

Coq theorem and proof:
```raw
Theorem Zdigit_not_0 :
  forall n, n <> Z0 ->
  exists k, (0 <= k)%Z /\ Zdigit n k <> Z0.
Proof.
intros n Hn.
destruct (Zle_or_lt 0 n) as [H|H].
destruct (Zle_lt_or_eq _ _ H) as [H'|H'].
now apply Zdigit_not_0_pos.
now elim Hn.
destruct (Zdigit_not_0_pos (-n)%Z) as [k Hk].
now apply Zopp_lt_cancel.
exists k.
rewrite Zdigit_opp.
intros H'.
apply -> Z.opp_eq_0_iff in H'.
exact (proj2 Hk H').
Qed.
```
-/
theorem Zdigit_not_0 (n : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜n ≠ 0⌝⦄
    (pure (Zdigit beta n 0) : Id _)
    ⦃⇓_ => ⌜∃ k, 0 ≤ k ∧ Zdigit beta n k ≠ 0⌝⦄ := by
  intro hn0
  by_cases hnn : 0 ≤ n
  · have hnpos : 0 < n := lt_of_le_of_ne hnn (Ne.symm hn0)
    exact exists_nonzero_digit beta n hβ hnpos
  · have hneg : n < 0 := lt_of_not_ge hnn
    have hpos : 0 < -n := by exact neg_pos.mpr hneg
    obtain ⟨k, hk_nonneg, hk_ne⟩ := exists_nonzero_digit beta (-n) hβ hpos
    refine ⟨k, hk_nonneg, ?_⟩
    intro hzero
    have hk_ge : 0 ≤ k := hk_nonneg
    have hzero' : (Int.tdiv n (beta ^ k.natAbs)) % beta = 0 := by
      simpa [Zdigit, hk_ge] using hzero
    have hdiv : beta ∣ Int.tdiv n (beta ^ k.natAbs) := by
      exact (Int.dvd_iff_emod_eq_zero).2 hzero'
    have hdiv_neg : beta ∣ -Int.tdiv n (beta ^ k.natAbs) := by
      exact (Int.dvd_neg).2 hdiv
    have hzero_neg : (Int.tdiv (-n) (beta ^ k.natAbs)) % beta = 0 := by
      have hzero_q : (-Int.tdiv n (beta ^ k.natAbs)) % beta = 0 :=
        Int.emod_eq_zero_of_dvd hdiv_neg
      simpa [Int.neg_tdiv] using hzero_q
    have hz_neg : Zdigit beta (-n) k = 0 := by
      simpa [Zdigit, hk_ge] using hzero_neg
    exact hk_ne hz_neg
/-- Digit of multiplied number

Coq theorem and proof:
```raw
Theorem Zdigit_mul_pow :
  forall n k k', (0 <= k')%Z ->
  Zdigit (n * Zpower beta k') k = Zdigit n (k - k').
Proof.
intros n k k' Hk'.
destruct (Zle_or_lt k' k) as [H|H].
revert k H.
pattern k' ; apply Zlt_0_ind with (2 := Hk').
clear k' Hk'.
intros k' IHk' Hk' k H.
unfold Zdigit.
apply (f_equal (fun x => Z.rem x beta)).
pattern k at 1 ; replace k with (k - k' + k')%Z by ring.
rewrite Zpower_plus with (2 := Hk').
apply Zquot_mult_cancel_r.
apply Zgt_not_eq.
now apply Zpower_gt_0.
now apply Zle_minus_le_0.
destruct (Zle_or_lt 0 k) as [H0|H0].
rewrite (Zdigit_lt n) by lia.
unfold Zdigit.
replace k' with (k' - k + k)%Z by ring.
rewrite Zpower_plus with (2 := H0).
rewrite Zmult_assoc, Z_quot_mult.
replace (k' - k)%Z with (k' - k - 1 + 1)%Z by ring.
rewrite Zpower_exp by lia.
rewrite Zmult_assoc.
change (Zpower beta 1) with (beta * 1)%Z.
rewrite Zmult_1_r.
apply Z_rem_mult.
apply Zgt_not_eq.
now apply Zpower_gt_0.
apply Zle_minus_le_0.
now apply Zlt_le_weak.
rewrite Zdigit_lt with (1 := H0).
apply sym_eq.
apply Zdigit_lt.
lia.
Qed.
```
-/
theorem Zdigit_mul_pow (n k l : Int) (hβ : beta > 1 := h_beta):
    ⦃⌜0 ≤ l⌝⦄
    (pure (Zdigit beta (n * beta ^ l.natAbs) k) : Id _)
    ⦃⇓result => ⌜∃ shifted, Zdigit beta n (k - l) = shifted ∧ result = shifted⌝⦄ := by
  intro hl
  -- We will produce the shifted digit explicitly and prove equality by cases
  classical
  use (if k - l ≥ 0 then (Int.tdiv n (beta ^ (k - l).natAbs)) % beta else 0)
  constructor
  · -- Right side is definitionally this value
    unfold Zdigit; simp only []
  · -- Now, show the left side reduces to the same by case analysis on k and l ≤ k
    unfold Zdigit
    by_cases hk : 0 ≤ k
    · -- k ≥ 0: active branch, compare quotients
      simp [hk]
      have hb : 0 < beta := beta_pos (beta := beta) hβ
      have hbK : 0 < beta ^ k.natAbs := pow_pos hb _
      have hbL : 0 < beta ^ l.natAbs := pow_pos hb _
      by_cases hle : l ≤ k
      · -- Case l ≤ k: then k - l ≥ 0 and exponents add up
        have hkl_nonneg : 0 ≤ k - l := sub_nonneg.mpr hle
        have hk_as : (k.natAbs : Int) = k := by simp [Int.natAbs_of_nonneg hk]
        have hl_as : (l.natAbs : Int) = l := by simp [Int.natAbs_of_nonneg hl]
        have hkl_as : ((k - l).natAbs : Int) = k - l := by simp [Int.natAbs_of_nonneg hkl_nonneg]
        -- Show k.natAbs = (k - l).natAbs + l.natAbs by injecting the Int equality k = (k-l) + l
        have hsum_nat : (k - l).natAbs + l.natAbs = k.natAbs := by
          -- cast to Int and use injectivity
          have : ((k - l).natAbs : Int) + (l.natAbs : Int) = (k.natAbs : Int) := by
            rw [hkl_as, hl_as, hk_as]
            ring
          -- Apply injectivity directly
          exact Nat.cast_injective this
        -- Rewrite the divisor using the sum of exponents
        have hdiv_rewrite : beta ^ k.natAbs = beta ^ ((k - l).natAbs + l.natAbs) := by
          simp [hsum_nat]
        -- Now cancel the common factor beta^l in truncating division
        have : Int.tdiv (n * beta ^ l.natAbs) (beta ^ k.natAbs)
                 = Int.tdiv n (beta ^ (k - l).natAbs) := by
          -- Use the fact that beta^k = beta^(k-l) * beta^l
          rw [hdiv_rewrite]
          -- Now we have (n * β^l) / (β^(k-l) * β^l)
          rw [pow_add]
          -- Apply Int.mul_tdiv_mul_of_pos_left to cancel beta^l
          exact Int.mul_tdiv_mul_of_pos_left n (beta ^ (k - l).natAbs) hbL
        simp [this]  -- also discharges the RHS if-condition
        -- Prove that k < l leads to a contradiction since we have l ≤ k
        intro h_absurd
        exact absurd h_absurd (not_lt.mpr hle)
      · -- Case k < l: then k - l < 0, so RHS is 0. LHS quotient is a multiple of beta hence 0 mod beta
        have hneg : ¬(k - l ≥ 0) := by
          push_neg
          exact sub_neg.mpr (lt_of_not_ge hle)
        -- show that (tdiv ((n * β^l)) (β^k)) % β = 0 by showing the quotient is a multiple of β
        have hk_nonneg : 0 ≤ k := hk
        -- Since l > k ≥ 0, we can write l = k + t with t ≥ 1 at the level of Nat exponents
        have hk_as : (k.natAbs : Int) = k := by simp [Int.natAbs_of_nonneg hk]
        have hl_as : (l.natAbs : Int) = l := by simp [Int.natAbs_of_nonneg hl]
        have hkl_pos : 0 < l - k := sub_pos.mpr (lt_of_not_ge hle)
        have hkltl_nat : ∃ t : Nat, t.succ + k.natAbs = l.natAbs := by
          -- derive existence using Int-level equality l = k + (l-k)
          have hsumInt : k + (l - k) = l := by ring
          -- Convert to Nat by injectivity; obtain (l - k) as a positive Nat
          have hposNat : 0 < (l - k).natAbs := by
            have : (0 : Int) < (l - k) := hkl_pos
            simp [Int.natAbs_pos.mpr this.ne']
          -- Then (l - k).natAbs = t.succ for some t
          rcases Nat.exists_eq_succ_of_ne_zero (by exact_mod_cast (ne_of_gt hposNat) : (l - k).natAbs ≠ 0) with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          -- Cast the Int equality to Nat and finish
          calc t.succ + k.natAbs
              = (l - k).natAbs + k.natAbs := by rw [← ht]
            _ = k.natAbs + (l - k).natAbs := by rw [Nat.add_comm]
            _ = l.natAbs := by
                have eq_int : (k.natAbs : Int) + ((l - k).natAbs : Int) = (l.natAbs : Int) := by
                  rw [hk_as, hl_as]
                  have hlk_pos : 0 < l - k := hkl_pos
                  simp only [Int.natAbs_of_nonneg (le_of_lt hlk_pos)]
                  ring
                exact Nat.cast_injective eq_int
        rcases hkltl_nat with ⟨t, ht⟩
        -- Compute the quotient explicitly:
        have hpow_split : beta ^ l.natAbs = beta ^ (k.natAbs + Nat.succ t) := by rw [← ht]; simp [Nat.add_comm]
        have hpow_split' : beta ^ l.natAbs = (beta ^ (Nat.succ t)) * (beta ^ k.natAbs) := by
          rw [hpow_split, Nat.add_comm, pow_add, mul_comm]
        have q_eq : Int.tdiv (n * beta ^ l.natAbs) (beta ^ k.natAbs) = n * beta ^ (Nat.succ t) := by
          -- (n * (β^(t+1) * β^k)) / (β^k) = n * β^(t+1)
          rw [hpow_split']
          rw [← mul_assoc n]
          rw [Int.mul_tdiv_cancel _ (ne_of_gt hbK)]
        -- Since β ∣ β^(t+1), the resulting quotient is a multiple of β, hence remainder is 0
        have hb_ne0 : beta ≠ 0 := ne_of_gt hb
        have dvd_beta : beta ∣ (beta ^ (Nat.succ t)) := by
          -- β ∣ β^(t+1)
          refine ⟨beta ^ t, ?_⟩
          rw [pow_succ]
          ring
        have dvd_q : beta ∣ (n * beta ^ (Nat.succ t)) := dvd_mul_of_dvd_right dvd_beta n
        have : (n * beta ^ (Nat.succ t)) % beta = 0 := Int.emod_eq_zero_of_dvd dvd_q
        simp [q_eq, this]
        intro h_absurd
        exact absurd h_absurd hle
    · -- k < 0: both are zero since l ≥ 0 implies k - l < 0
      have hklt : k < 0 := lt_of_not_ge hk
      have hkl_neg : ¬ (k - l ≥ 0) := by
        push_neg
        have : k - l ≤ k := sub_le_self k hl
        exact lt_of_le_of_lt this hklt
      simp [show ¬ (k ≥ 0) from not_le.mpr hklt]
      intro h_absurd
      -- When k < 0 and l ≥ 0, we have k < l, so l ≤ k is false
      have : k < l := lt_of_lt_of_le hklt hl
      exact absurd h_absurd (not_le.mpr this)

/-- Digit of divided number

Coq theorem and proof:
```raw
Theorem Zdigit_div_pow :
  forall n k k', (0 <= k)%Z -> (0 <= k')%Z ->
  Zdigit (Z.quot n (Zpower beta k')) k = Zdigit n (k + k').
Proof.
intros n k k' Hk Hk'.
unfold Zdigit.
rewrite Zquot_Zquot.
rewrite Zplus_comm.
now rewrite Zpower_plus.
Qed.
```
-/
theorem Zdigit_div_pow (n k l : Int) (hβ : beta > 1 := h_beta):
    ⦃⌜0 ≤ l ∧ 0 ≤ k ∧ 0 < n⌝⦄
    (pure (Zdigit beta (n / beta ^ l.natAbs) k) : Id _)
    ⦃⇓result => ⌜∃ shifted, Zdigit beta n (k + l) = shifted ∧ result = shifted⌝⦄ := by
  intro ⟨hl, hk, hn_pos⟩
  -- The digit at position k+l directly
  use (if k + l ≥ 0 then (Int.tdiv n (beta ^ (k + l).natAbs)) % beta else 0)
  constructor
  · -- Right side is definitionally this value
    unfold Zdigit
    simp only []
  · -- Show left side equals the same by unfolding and simplifying
    unfold Zdigit
    simp [hk]
    -- Since k ≥ 0 and l ≥ 0, we have k + l ≥ 0
    have hkl_nonneg : 0 ≤ k + l := add_nonneg hk hl
    simp [hkl_nonneg]
    -- Need to show: (n / β^l).tdiv β^k = n.tdiv β^(k+l)
    -- Convert natAbs values
    have hk_as : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk
    have hl_as : (l.natAbs : Int) = l := Int.natAbs_of_nonneg hl
    have hkl_as : ((k + l).natAbs : Int) = k + l := Int.natAbs_of_nonneg hkl_nonneg
    -- Show natAbs addition
    have hsum_nat : k.natAbs + l.natAbs = (k + l).natAbs := by
      have : (k.natAbs : Int) + (l.natAbs : Int) = ((k + l).natAbs : Int) := by
        rw [hk_as, hl_as, hkl_as]
      exact Nat.cast_injective this
    -- Key: (n / β^l).tdiv β^k = n.tdiv β^(k+l)
    have hb : 0 < beta := beta_pos (beta := beta) hβ
    have hbK : 0 < beta ^ k.natAbs := pow_pos hb _
    have hbL : 0 < beta ^ l.natAbs := pow_pos hb _

    -- Since n > 0, we have n ≥ 0, so we can use ediv properties directly
    have hn_nonneg : 0 ≤ n := le_of_lt hn_pos

    have hdiv_eq : Int.tdiv (n / beta ^ l.natAbs) (beta ^ k.natAbs) =
                   Int.tdiv n (beta ^ (k + l).natAbs) := by
      rw [← hsum_nat]
      rw [pow_add]
      -- Since n ≥ 0, both ediv and tdiv equal regular division
      have hdiv_nonneg : 0 ≤ n / beta ^ l.natAbs := Int.ediv_nonneg hn_nonneg (Int.le_of_lt hbL)
      rw [Int.tdiv_eq_ediv_of_nonneg hdiv_nonneg]
      rw [Int.tdiv_eq_ediv_of_nonneg hn_nonneg]
      -- `(n / (β^l)) / (β^k) = n / (β^(l+k))` for nonnegative divisor `β^l`
      -- Use `Int.ediv_ediv_of_nonneg` with explicit parameters (requires `0 ≤ β^l`).
      -- `(n / (β^l)) / (β^k) = n / ((β^l) * (β^k))`
      have hassoc : (n / (beta ^ l.natAbs)) / (beta ^ k.natAbs)
          = n / ((beta ^ l.natAbs) * (beta ^ k.natAbs)) := by
        have hbL_nonneg : 0 ≤ beta ^ l.natAbs := Int.le_of_lt hbL
        -- Specialize `Int.ediv_ediv_of_nonneg` to our `a,b,c` via type annotation
        simpa using
          (Int.ediv_ediv_of_nonneg hbL_nonneg :
            (n / (beta ^ l.natAbs)) / (beta ^ k.natAbs)
              = n / ((beta ^ l.natAbs) * (beta ^ k.natAbs)))
      -- Normalize powers and commutativity of multiplication to match the goal
      simpa [pow_add, mul_comm] using hassoc
    rw [hdiv_eq]

/-- Digit modulo power

Coq theorem and proof:
```raw
Theorem Zdigit_mod_pow :
  forall n k k', (k < k')%Z ->
  Zdigit (Z.rem n (Zpower beta k')) k = Zdigit n k.
Proof.
intros n k k' Hk.
destruct (Zle_or_lt 0 k) as [H|H].
unfold Zdigit.
rewrite <- 2!ZOdiv_mod_mult.
apply (f_equal (fun x => Z.quot x (beta ^ k))).
replace k' with (k + 1 + (k' - (k + 1)))%Z by ring.
rewrite Zpower_exp by lia.
rewrite Zmult_comm.
rewrite Zpower_plus by easy.
change (Zpower beta 1) with (beta * 1)%Z.
rewrite Zmult_1_r.
apply ZOmod_mod_mult.
now rewrite 2!Zdigit_lt.
Qed.
```
-/
-- Helper lemma for Zdigit_mod_pow
private lemma tdiv_mod_pow_eq
    (n k l β : ℤ)
    (hn : 0 ≤ n) (hk0 : 0 ≤ k) (hklt : k < l) (hβ : 1 < β) :
    ((n % β ^ l.natAbs).tdiv (β ^ k.natAbs)) % β
      = (n.tdiv (β ^ k.natAbs)) % β := by
  -- Shorthands
  set Pk : ℤ := β ^ k.natAbs
  set Pl : ℤ := β ^ l.natAbs

  -- β, Pk, Pl are positive
  have hβpos  : 0 < β := lt_trans (show (0 : ℤ) < 1 from by decide) hβ
  have hPkpos : 0 < Pk := by
    have := pow_pos hβpos (k.natAbs)
    simpa [Pk] using this
  have hPlpos : 0 < Pl := by
    have := pow_pos hβpos (l.natAbs)
    simpa [Pl] using this

  -- Convert both tdiv's to Euclidean division (numerators ≥ 0; divisors > 0).
  have hr_nonneg : 0 ≤ n % Pl := Int.emod_nonneg _ (ne_of_gt hPlpos)
  have htdiv_r :
      (n % Pl).tdiv Pk = (n % Pl) / Pk := by
    simpa using Int.tdiv_eq_ediv_of_nonneg hr_nonneg
  have htdiv_n :
      n.tdiv Pk = n / Pk := by
    simpa using Int.tdiv_eq_ediv_of_nonneg hn

  -- Reduce goal to Euclidean division
  have : ((n % Pl) / Pk) % β = (n / Pk) % β := by
    -- Euclidean decomposition: n = (n / Pl) * Pl + (n % Pl)
    have hsplit0 : (n / Pl) * Pl + n % Pl = n := by
      rw [mul_comm]
      exact Int.mul_ediv_add_emod n Pl

    -- Show: n / Pk = (n / Pl) * (Pl / Pk) + (n % Pl) / Pk
    have hk_le_l : k.natAbs ≤ l.natAbs := by
      -- since 0 ≤ k < l, we also have 0 ≤ l
      have hl0 : 0 ≤ l := le_trans hk0 (le_of_lt hklt)
      -- k < l with nonnegative k and l implies k.natAbs < l.natAbs
      have hlt : k.natAbs < l.natAbs := Int.natAbs_lt_natAbs_of_nonneg_of_lt hk0 hklt
      exact le_of_lt hlt

    -- (Pl splits as Pk * β^(l-k))
    have hPl_split : Pl = Pk * (β ^ (l.natAbs - k.natAbs)) := by
      -- β^l = β^(k + (l-k)) = β^k * β^(l-k)
      have heq : k.natAbs + (l.natAbs - k.natAbs) = l.natAbs := Nat.add_sub_cancel' hk_le_l
      simp only [Pl, Pk]
      conv_lhs => rw [← heq]
      rw [pow_add]

    -- Pk divides Pl since k ≤ l
    have hPk_dvd_Pl : Pk ∣ Pl := by
      -- a^m ∣ a^n when m ≤ n
      simp [Pk, Pl]
      exact pow_dvd_pow β hk_le_l

    -- Because Pk ∣ (n/Pl)*Pl, we can split (a + b)/Pk = a/Pk + b/Pk
    have hPk_dvd_a : Pk ∣ (n / Pl) * Pl := by
      exact dvd_mul_of_dvd_right hPk_dvd_Pl (n / Pl)
    have hsplit_div :
        n / Pk = (n / Pl) * (Pl / Pk) + (n % Pl) / Pk := by
      -- (a + b) / c = a / c + b / c when c ∣ a
      -- here: a = (n/Pl)*Pl, b = n%Pl, c = Pk
      calc n / Pk = ((n / Pl) * Pl + n % Pl) / Pk := by rw [hsplit0]
        _ = (n / Pl) * Pl / Pk + (n % Pl) / Pk := Int.add_ediv_of_dvd_left hPk_dvd_a
        _ = (n / Pl) * (Pl / Pk) + (n % Pl) / Pk := by rw [Int.mul_ediv_assoc _ hPk_dvd_Pl]

    -- Show (Pl / Pk) = β^(l-k)
    have hPk_ne : Pk ≠ 0 := ne_of_gt hPkpos
    have hquot :
        Pl / Pk = β ^ (l.natAbs - k.natAbs) := by
      -- (Pk * t) / Pk = t
      rw [hPl_split]
      simp [Int.mul_ediv_cancel_left _ hPk_ne]

    -- Since k < l, (l.natAbs - k.natAbs) ≥ 1, hence β ∣ (Pl / Pk)
    have hbeta_dvd_quot : β ∣ Pl / Pk := by
      -- 1 ≤ lAbs - kAbs
      have hpos : 1 ≤ l.natAbs - k.natAbs := by
        -- k < l with 0 ≤ k,l ⇒ k.natAbs < l.natAbs
        have hl0 : 0 ≤ l := le_trans hk0 (le_of_lt hklt)
        have hlt_nat : k.natAbs < l.natAbs := Int.natAbs_lt_natAbs_of_nonneg_of_lt hk0 hklt
        -- Since k.natAbs < l.natAbs, we have 1 ≤ l.natAbs - k.natAbs
        exact Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hlt_nat)
      -- write β^(m) = β * β^(m-1) for m ≥ 1
      rcases Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos) with ⟨m, hm⟩
      refine ⟨β ^ m, ?_⟩
      simp only [hquot, hm, pow_succ, mul_comm]

    -- Reduce modulo β: the big term vanishes
    have hvanish :
        ((n / Pl) * (Pl / Pk)) % β = 0 := by
      have ⟨t, ht⟩ := hbeta_dvd_quot
      calc ((n / Pl) * (Pl / Pk)) % β
        = ((n / Pl) * (β * t)) % β := by rw [ht]
        _ = (β * ((n / Pl) * t)) % β := by ring_nf
        _ = 0 := by simp

    -- Wrap up: rewrite `n / Pk` by `hsplit_div` and use `Int.add_emod`
    show ((n % Pl) / Pk) % β = (n / Pk) % β
    rw [hsplit_div]
    rw [Int.add_emod]
    rw [hvanish]
    simp

  -- fold back tdivs
  simpa [htdiv_r, htdiv_n, Pk, Pl] using this

theorem Zdigit_mod_pow (n k l : Int) (hβ : beta > 1 := h_beta):
    ⦃⌜0 ≤ k ∧ k < l ∧ 0 < n⌝⦄
    (pure (Zdigit beta (n % beta ^ l.natAbs) k) : Id _)
    ⦃⇓result => ⌜∃ orig, Zdigit beta n k = orig ∧ result = orig⌝⦄ := by
  intro ⟨hk_nonneg, hk_lt, hn_pos⟩
  use (Int.tdiv n (beta ^ k.natAbs)) % beta
  constructor
  · unfold Zdigit
    simp [hk_nonneg]
  · unfold Zdigit
    simp [hk_nonneg]
    -- Apply the helper lemma
    have hn_nonneg : 0 ≤ n := le_of_lt hn_pos
    exact tdiv_mod_pow_eq n k l beta hn_nonneg hk_nonneg hk_lt hβ

/-- Digit modulo power outside range

Coq theorem and proof:
```raw
Theorem Zdigit_mod_pow_out :
  forall n k k', (0 <= k' <= k)%Z ->
  Zdigit (Z.rem n (Zpower beta k')) k = Z0.
Proof.
intros n k k' Hk.
unfold Zdigit.
rewrite ZOdiv_small_abs.
apply Zrem_0_l.
apply Z.lt_le_trans with (Zpower beta k').
rewrite <- (Z.abs_eq (beta ^ k')) at 2 by apply Zpower_ge_0.
apply Zrem_lt.
apply Zgt_not_eq.
now apply Zpower_gt_0.
now apply Zpower_le.
Qed.
```
-/
-- Helper lemma for power monotonicity
private lemma pow_mono_int {beta : Int} (hβ : 1 < beta) {m n : Nat} (hmn : m ≤ n) :
    beta ^ m ≤ beta ^ n := by
  induction n with
  | zero => simp at hmn; simp [hmn]
  | succ n ih =>
    cases Nat.eq_or_lt_of_le hmn with
    | inl h => rw [h]
    | inr h =>
      have : m ≤ n := Nat.le_of_succ_le_succ h
      calc beta ^ m ≤ beta ^ n := ih this
        _ ≤ beta ^ n * beta := by
          have hpos : 0 < beta := by linarith
          have hpow_pos : 0 < beta ^ n := pow_pos_int hpos n
          have h1 : 1 ≤ beta := by linarith
          -- beta^n ≤ beta^n * beta since 1 ≤ beta
          calc beta ^ n = beta ^ n * 1 := by ring
            _ ≤ beta ^ n * beta := Int.mul_le_mul_of_nonneg_left h1 (le_of_lt hpow_pos)
        _ = beta ^ (n + 1) := by rw [pow_succ]

private lemma pow_strict_mono_int {beta : Int} (hβ : 1 < beta) {m n : Nat} (hmn : m < n) :
    beta ^ m < beta ^ n := by
  have hle : m ≤ n := le_of_lt hmn
  have : m + 1 ≤ n := hmn
  induction n generalizing m with
  | zero => simp at hmn
  | succ n' ih =>
    cases Nat.eq_or_lt_of_le this with
    | inl h =>
      -- m + 1 = n'.succ, so m = n'
      have : m = n' := by grind
      rw [this, pow_succ]
      have hpos : 0 < beta := by linarith
      have hpow_pos : 0 < beta ^ n' := pow_pos_int hpos n'
      calc beta ^ n' = beta ^ n' * 1 := by ring
        _ < beta ^ n' * beta := by
          apply Int.mul_lt_mul_of_pos_left
          · exact hβ
          · exact hpow_pos
    | inr h =>
      -- m + 1 < n'.succ, so m < n'
      have hmn' : m < n' := by grind
      have hle : m ≤ n' := le_of_lt hmn'
      have hsuc : m + 1 ≤ n' := by grind
      calc beta ^ m < beta ^ n' := ih hmn' hle hsuc
        _ ≤ beta ^ n'.succ := by
          rw [pow_succ]
          have hpos : 0 < beta := by linarith
          have hpow_pos : 0 < beta ^ n' := pow_pos_int hpos n'
          have h1 : 1 ≤ beta := by linarith
          calc beta ^ n' = beta ^ n' * 1 := by ring
            _ ≤ beta ^ n' * beta := Int.mul_le_mul_of_nonneg_left h1 (le_of_lt hpow_pos)

theorem Zdigit_mod_pow_out (n k l : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜0 ≤ l ∧ l ≤ k⌝⦄
    (pure (Zdigit beta (n % beta ^ l.natAbs) k) : Id _)
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro ⟨hl_nonneg, hl_le_k⟩
  unfold Zdigit

  -- Since l ≤ k and 0 ≤ l, we have 0 ≤ k
  have hk_nonneg : 0 ≤ k := le_trans hl_nonneg hl_le_k
  simp [hk_nonneg]

  -- Key: show that (n % beta^l) / beta^k = 0
  have hdiv_zero : Int.tdiv (n % beta ^ l.natAbs) (beta ^ k.natAbs) = 0 := by
    apply Int.tdiv_eq_zero_of_lt
    · -- Show 0 ≤ n % beta^l (modulo is non-negative for positive modulus)
      apply Int.emod_nonneg
      intro hcontra
      have : beta ^ l.natAbs = 0 := hcontra
      have hβpos : 0 < beta := by linarith [hβ]
      have : 0 < beta ^ l.natAbs := pow_pos hβpos l.natAbs
      linarith
    · -- Show n % beta^l < beta^k (absolute value not needed since modulo is non-negative)
      -- First get the bound on modulo
      have hmod_bound : n % beta ^ l.natAbs < beta ^ l.natAbs := by
        have hβpos : 0 < beta := by linarith [hβ]
        have hpow_pos : 0 < beta ^ l.natAbs := pow_pos hβpos l.natAbs
        -- For positive divisor, n % m < m when m > 0
        exact Int.emod_lt_of_pos n hpow_pos

      -- Since l ≤ k, we have beta^l ≤ beta^k
      have hpow_le : beta ^ l.natAbs ≤ beta ^ k.natAbs := by
        -- Show l.natAbs ≤ k.natAbs
        have hnat_le : l.natAbs ≤ k.natAbs := by
          -- For non-negative integers l and k, if l ≤ k then l.natAbs ≤ k.natAbs
          have hl_eq : (l.natAbs : Int) = l := Int.natAbs_of_nonneg hl_nonneg
          have hk_eq : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk_nonneg
          -- Convert the inequality
          have : (l.natAbs : Int) ≤ (k.natAbs : Int) := by
            rw [hl_eq, hk_eq]
            exact hl_le_k
          -- Convert back to natural numbers
          exact Nat.cast_le.mp this
        -- Apply our helper lemma for power monotonicity
        exact pow_mono_int hβ hnat_le

      -- Absolute value of non-negative modulo is itself
      have habs_eq : |n % beta ^ l.natAbs| = n % beta ^ l.natAbs := by
        apply abs_of_nonneg
        apply Int.emod_nonneg
        intro hcontra
        have : beta ^ l.natAbs = 0 := hcontra
        have hβpos : 0 < beta := by linarith [hβ]
        have : 0 < beta ^ l.natAbs := pow_pos hβpos l.natAbs
        linarith

      -- Now we have n % beta^l < beta^l ≤ beta^k
      exact lt_of_lt_of_le hmod_bound hpow_le

  -- Therefore (n % beta^l) / beta^k % beta = 0 % beta = 0
  rw [hdiv_zero]
  simp

/-- Sum of digits representation -/
def Zsum_digit (f : Int → Int) : Nat → Int
  | 0 => 0
  | n + 1 =>
    let prev := Zsum_digit f n
    prev + f n * beta ^ n

theorem ZOmod_plus_pow_digit (n k : Int) (hn : 0 ≤ n) (hβ : beta > 1):
    ⦃⌜0 ≤ k⌝⦄
    (pure (Zdigit beta n k) : Id _)
    ⦃⇓d => ⌜n % beta ^ (k + 1).natAbs =
            n % beta ^ k.natAbs + d * beta ^ k.natAbs⌝⦄ := by
  intro hk
  -- expose the digit and rewrite `tdiv` to `/` using `hn`
  unfold Zdigit
  simp
  set b : Int := beta ^ k.natAbs with hb
  -- basic positivity
  have hβpos : 0 < beta := by
    have : (0 : Int) < 1 := by decide
    exact lt_trans this hβ
  have hbpos : 0 < b := by simpa [hb] using pow_pos hβpos k.natAbs
  have hbne  : b ≠ 0 := ne_of_gt hbpos

  -- replace `tdiv` with `ediv` since `n ≥ 0`
  have : (Int.tdiv n b) % beta = (n / b) % beta := by
    simp [Int.tdiv_eq_ediv_of_nonneg hn]
  simp [this]

  -- Candidate remainder at base `b*beta`
  set r : Int := n % b + (n / b % beta) * b with hr

  -- r ≥ 0
  have hr_nonneg : 0 ≤ r := by
    have h0 : 0 ≤ n % b := Int.emod_nonneg _ hbne
    have h1 : 0 ≤ (n / b % beta) := Int.emod_nonneg _ (ne_of_gt hβpos)
    exact add_nonneg h0 (mul_nonneg h1 (le_of_lt hbpos))

  -- r < b*beta
  have hr_lt : r < b * beta := by
    have hx : n % b < b := Int.emod_lt_of_pos _ hbpos
    have hy : (n / b % beta) < beta := Int.emod_lt_of_pos _ hβpos
    -- ( (n/b % β) + 1 ) * b ≤ β*b  ⇒  (n/b % β)*b + b ≤ β*b
    have hy' : (n / b % beta) * b + b ≤ beta * b := by
      have : (n / b % beta) + 1 ≤ beta := (Int.add_one_le_iff).mpr hy
      have := mul_le_mul_of_nonneg_right this (le_of_lt hbpos)
      calc (n / b % beta) * b + b
          = ((n / b % beta) + 1) * b := by ring
          _ ≤ beta * b := this
    -- (n % b + 1) + (n/b % β)*b ≤ b + (n/b % β)*b
    have hx' : n % b + 1 ≤ b := (Int.add_one_le_iff).mpr hx
    have : r + 1 ≤ b + (n / b % beta) * b := by
      have := add_le_add_right hx' ((n / b % beta) * b)
      simpa [hr, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm] using this
    -- chain and swap to `b*β`
    have : r + 1 ≤ beta * b := le_trans this (by simpa [mul_comm, add_comm] using hy')
    have : r + 1 ≤ b * beta := by simpa [mul_comm] using this
    exact (Int.add_one_le_iff.mp this)

  -- Algebraic decomposition: n = ((n/b)/β) * (b*β) + r
  have hsplit1 : n = (n / b) * b + n % b := by
    have := Int.mul_ediv_add_emod n b
    rw [mul_comm] at this
    exact this.symm
  have hsplit2 : (n / b) = (n / b / beta) * beta + (n / b % beta) := by
    have := Int.mul_ediv_add_emod (n / b) beta
    rw [mul_comm] at this
    exact this.symm
  have hdecomp : n = ((n / b) / beta) * (b * beta) + r := by
    calc
      n = (n / b) * b + n % b := hsplit1
      _ = ((n / b) / beta * beta + (n / b % beta)) * b + n % b := by
            rw [← hsplit2]
      _ = ((n / b) / beta) * (beta * b) + (n / b % beta) * b + n % b := by
            ring_nf
      _ = ((n / b) / beta) * (b * beta) + r := by
            simp [hr, mul_comm, add_comm, add_assoc]

  -- Uniqueness of remainder at modulus `b*β`
  have hmod_bb : n % (b * beta) = r := by
    -- Uniqueness of Euclidean division at modulus (b * beta)
    have hpos : 0 < (b * beta) := mul_pos hbpos hβpos
    -- Put the decomposition into the form `r + (b*beta)*q = n`
    have hdecomp' :
        r + (b * beta) * ((n / b) / beta) = n := by
      -- from: hdecomp : n = ((n / b) / beta) * (b * beta) + r
      -- commute + reorder terms
      simpa [add_comm, mul_comm, mul_left_comm] using hdecomp.symm
    -- Apply the uniqueness lemma to get the remainder
    have hpair :
        n / (b * beta) = (n / b) / beta ∧ n % (b * beta) = r :=
      (Int.ediv_emod_unique hpos).mpr ⟨hdecomp', hr_nonneg, hr_lt⟩
    exact hpair.2

  -- Convert `(k+1).natAbs` to `k.natAbs + 1` under `k ≥ 0`
  have hNat : (k + 1).natAbs = k.natAbs + 1 := by
    have hk1 : 0 ≤ k + 1 := add_nonneg hk (by decide)
    -- compare as Int and use injectivity of `Nat.cast`
    apply @Nat.cast_injective Int _ _
    calc
      ((k + 1).natAbs : Int) = k + 1 := Int.natAbs_of_nonneg hk1
      _ = (k.natAbs : Int) + 1 := by simp [Int.natAbs_of_nonneg hk]
  -- Finish: rewrite the modulus and unfold `r`
  calc
    n % beta ^ (k + 1).natAbs
        = n % beta ^ (k.natAbs + 1) := by simp [hNat]
    _ = n % (beta ^ k.natAbs * beta) := by simp [pow_succ, mul_comm]
    _ = r := by simpa [hb, mul_comm] using hmod_bb
    _ = n % beta ^ k.natAbs + ((n / b) % beta) * b := rfl
    _ = n % beta ^ k.natAbs + ((Int.tdiv n b) % beta) * b := by
          -- put `tdiv` back (it matches the returned value)
          simp [Int.tdiv_eq_ediv_of_nonneg hn]
    _ = n % beta ^ k.natAbs + ((Int.tdiv n b) % beta) * beta ^ k.natAbs := by
          simp [hb]
  -- Final clean finish: eliminate the IF and switch tdiv → ediv on both denominators.
  have hk' : 0 ≤ k := hk

  -- tdiv = ediv for nonnegative n, at both denominators we used
  have htdiv_pow :
      n.tdiv (beta ^ k.natAbs) % beta = n / beta ^ k.natAbs % beta := by
    simp [Int.tdiv_eq_ediv_of_nonneg hn]
  have htdiv_b :
      n.tdiv b % beta = n / b % beta := by
    simp [Int.tdiv_eq_ediv_of_nonneg hn]

  -- collapse the IF using hk'
  have hIf :
      (if 0 ≤ k then n / b % beta * b else 0) = n / b % beta * b := by
    simp [hk']

  -- now both sides match by rewriting b = beta ^ k.natAbs and the two facts above
  simp [hb, hk', htdiv_pow]

/-- Sum reconstructs from digits

Coq theorem and proof:
```raw
Theorem Zsum_digit_digit :
  forall n k,
  Zsum_digit (Zdigit n) k = Z.rem n (Zpower beta (Z_of_nat k)).
Proof.
intros n.
induction k.
apply sym_eq.
apply Z.rem_1_r.
simpl Zsum_digit.
rewrite IHk.
unfold Zdigit.
rewrite <- ZOdiv_mod_mult.
rewrite <- (ZOmod_mod_mult n beta).
rewrite Zmult_comm.
replace (beta ^ Z_of_nat k * beta)%Z with (Zpower beta (Z_of_nat (S k))).
rewrite Zplus_comm, Zmult_comm.
apply sym_eq.
apply Z.quot_rem'.
rewrite inj_S.
rewrite <- (Zmult_1_r beta) at 3.
apply Zpower_plus.
apply Zle_0_nat.
easy.
Qed.
```
-/
theorem Zsum_digit_digit (n : Int) (k : Nat) (hβ : beta > 1 := h_beta) :
    ⦃⌜0 < n⌝⦄
    (pure (Zsum_digit beta (fun i => Zdigit beta n i) k) : Id _)
    ⦃⇓result => ⌜result = n % beta ^ k⌝⦄ := by
  intro hn
  have hn_nonneg : 0 ≤ n := le_of_lt hn
  induction k with
  | zero =>
      simp [Zsum_digit]
  | succ k ih =>
      -- Use the modular decomposition for the (k : Int) digit.
      have hmod :
          n % beta ^ ((k : Int) + 1).natAbs =
            n % beta ^ (k : Int).natAbs + Zdigit beta n (k : Int) * beta ^ (k : Int).natAbs := by
        have h := (ZOmod_plus_pow_digit (beta := beta) (n := n) (k := (k : Int)) hn_nonneg hβ)
          (Int.natCast_nonneg k)
        simpa [wp, PostCond.noThrow, pure] using h
      -- Unfold the sum and rewrite using the inductive hypothesis.
      have ih' : Zsum_digit beta (fun i => Zdigit beta n i) k = n % beta ^ k := by
        simpa [wp, PostCond.noThrow, pure] using ih
      simp [wp, PostCond.noThrow, pure, Zsum_digit, ih']
      simpa using hmod.symm

theorem Zdigit_ext_nonneg (n m : Int) (hn : 0 ≤ n) (hm : 0 ≤ m) (hβ : beta > 1 := h_beta):
    ⦃⌜∀ k, 0 ≤ k → Zdigit beta n k = Zdigit beta m k⌝⦄
    (pure (Zdigit beta n 0) : Id _)
    ⦃⇓_ => ⌜n = m⌝⦄ := by
  intro hdigits
  by_cases hn0 : n = 0
  · have hm0 : m = 0 := by
      by_contra hm0
      have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
      obtain ⟨k, hk_nonneg, hk_ne⟩ := exists_nonzero_digit beta m hβ hmpos
      have hkm := hdigits k hk_nonneg
      have hzero : Zdigit beta n k = 0 := by simp [hn0, Zdigit]
      have hmzero : Zdigit beta m k = 0 := by simpa [hzero] using hkm.symm
      exact hk_ne hmzero
    simpa [hn0, hm0]
  · have hnpos : 0 < n := lt_of_le_of_ne hn (Ne.symm hn0)
    have hm0 : m ≠ 0 := by
      intro hm0
      obtain ⟨k, hk_nonneg, hk_ne⟩ := exists_nonzero_digit beta n hβ hnpos
      have hkm := hdigits k hk_nonneg
      have hzero : Zdigit beta m k = 0 := by simp [hm0, Zdigit]
      have hnzero : Zdigit beta n k = 0 := by simpa [hzero] using hkm
      exact hk_ne hnzero
    have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)

    -- Equal digit sums for all k.
    have hsum_eq :
        ∀ k : Nat,
          Zsum_digit beta (fun i => Zdigit beta n i) k =
          Zsum_digit beta (fun i => Zdigit beta m i) k := by
      intro k
      induction k with
      | zero => simp [Zsum_digit]
      | succ k ih =>
          have hk_nonneg : 0 ≤ (k : Int) := Int.natCast_nonneg k
          have hdig := hdigits (k : Int) hk_nonneg
          simp [Zsum_digit, ih, hdig]

    have hmod_eq : ∀ k : Nat, n % beta ^ k = m % beta ^ k := by
      intro k
      have hsum_n :
          Zsum_digit beta (fun i => Zdigit beta n i) k = n % beta ^ k := by
        have h := (Zsum_digit_digit (beta := beta) (n := n) (k := k) hβ) hnpos
        simpa [wp, PostCond.noThrow, pure] using h
      have hsum_m :
          Zsum_digit beta (fun i => Zdigit beta m i) k = m % beta ^ k := by
        have h := (Zsum_digit_digit (beta := beta) (n := m) (k := k) hβ) hmpos
        simpa [wp, PostCond.noThrow, pure] using h
      calc
        n % beta ^ k = Zsum_digit beta (fun i => Zdigit beta n i) k := by
          simpa using hsum_n.symm
        _ = Zsum_digit beta (fun i => Zdigit beta m i) k := hsum_eq k
        _ = m % beta ^ k := hsum_m

    -- Choose a large enough exponent so both are below the modulus.
    let kN : Nat := 1 + n.natAbs
    let kM : Nat := 1 + m.natAbs
    let K  : Nat := kN + kM
    have hb1 : 1 ≤ beta := le_of_lt hβ
    have hbpos : 0 < beta := beta_pos hβ

    have pow_succ_ge_local : ∀ t : Nat, (beta : Int) ^ t ≤ beta ^ (t + 1) := by
      intro t
      have hnonneg : 0 ≤ (beta : Int) ^ t := by
        have hb_nonneg : 0 ≤ (beta : Int) := le_trans (by decide) hb1
        exact pow_nonneg hb_nonneg _
      have := mul_le_mul_of_nonneg_left hb1 hnonneg
      simpa [pow_succ, mul_comm] using this

    have pow_le_pow_add : ∀ a b : Nat, (beta : Int) ^ a ≤ beta ^ (a + b) := by
      intro a b
      induction b with
      | zero => simp
      | succ b ih =>
          have hstep : (beta : Int) ^ (a + b) ≤ beta ^ (a + (b + 1)) := by
            simpa [Nat.add_assoc] using (pow_succ_ge_local (a + b))
          exact le_trans ih hstep

    have hNlt : n < beta ^ kN := by
      have h := abs_lt_beta_pow_succ_natAbs (beta := beta) (n := n) hβ hn0
      simpa [kN, abs_of_nonneg hn] using h
    have hMlt : m < beta ^ kM := by
      have h := abs_lt_beta_pow_succ_natAbs (beta := beta) (n := m) hβ hm0
      simpa [kM, abs_of_nonneg hm] using h
    have hNltK : n < beta ^ K := lt_of_lt_of_le hNlt (pow_le_pow_add kN kM)
    have hMltK : m < beta ^ K := by
      have h := pow_le_pow_add kM kN
      exact lt_of_lt_of_le hMlt (by simpa [K, Nat.add_comm] using h)

    have hmod_n : n % beta ^ K = n := by
      exact Int.emod_eq_of_lt hn hNltK
    have hmod_m : m % beta ^ K = m := by
      exact Int.emod_eq_of_lt hm hMltK
    have hmodK := hmod_eq K
    calc
      n = n % beta ^ K := by symm; exact hmod_n
      _ = m % beta ^ K := hmodK
      _ = m := hmod_m
theorem ZOdiv_plus_pow_digit
    (n k : Int) (hn : 0 ≤ n) (hβ : beta > 1 := h_beta) :
    ⦃⌜0 ≤ k⌝⦄
    (pure (Zdigit beta n k) : Id _)
    ⦃⇓d => ⌜n / beta ^ k.natAbs =
            d + (n / beta ^ (k + 1).natAbs) * beta⌝⦄ := by
  intro hk
  -- open the digit at position k
  unfold Zdigit; simp        -- exposes `d = if 0 ≤ k then … else 0`

  -- Notation: b = β^(|k|)
  set b : Int := beta ^ k.natAbs with hb

  -- β > 0
  have hβpos : 0 < beta := lt_trans (by decide : (0 : Int) < 1) hβ

  -- b > 0 since β > 0 and exponent is a Nat
  have hb_pos : 0 < b := by
    simpa [hb] using pow_pos hβpos (k.natAbs)

  -- (n / b) / β = n / (b * β)
  have ediv_assoc : (n / b) / beta = n / (b * beta) := by
    -- Use `Int.ediv_ediv_of_nonneg` with `0 ≤ b`
    have hb_nonneg : 0 ≤ b := le_of_lt hb_pos
    simpa using (Int.ediv_ediv_of_nonneg hb_nonneg)

  -- n / b = (n / (b*β)) * β + (n / b) % β
  have step : n / b = (n / (b * beta)) * beta + (n / b % beta) := by
    -- `mul_ediv_add_emod` gives `(n/b) = ((n/b)/β) * β + (n/b)%β`; rewrite the middle with `ediv_assoc`
    simpa [ediv_assoc, mul_comm] using (Int.mul_ediv_add_emod (n / b) beta).symm

  -- Switch the `% β` term to use `tdiv` (since n ≥ 0 and b > 0)
  have htdiv : (Int.tdiv n b) % beta = (n / b) % beta := by
    have : Int.tdiv n b = n / b := by
      rw [Int.tdiv_eq_ediv]
      simp [hn]
    simp [this]
  have step' : n / b = (n / (b * beta)) * beta + (Int.tdiv n b % beta) := by
    simpa [htdiv] using step

  -- (k+1).natAbs = k.natAbs + 1  (because k ≥ 0)
  have hNat : (k + 1).natAbs = k.natAbs + 1 := by
    have hk1 : 0 ≤ k + 1 := add_nonneg hk (by decide)
    -- cast-to-ℤ trick to use `Int.natAbs_of_nonneg` on both sides
    apply (Nat.cast_injective : Function.Injective (fun n : Nat => (n : Int)))
    calc
      ((k + 1).natAbs : Int) = k + 1 := Int.natAbs_of_nonneg hk1
      _ = (k.natAbs : Int) + 1 := by simp [Int.natAbs_of_nonneg hk]

  -- rewrite `β^(|(k+1)|)` as `b * β`
  have pow_succ' : beta ^ (k + 1).natAbs = b * beta := by
    -- `pow_succ` turns `β^(t+1)` into `β^t * β`; `hNat` replaces `|(k+1)|` with `|k|+1`
    simp [hb, hNat, pow_succ, mul_comm]

  -- finish: also collapse the `if 0 ≤ k then … else 0` via `[hk]`
  simp only [pow_succ']
  have : 0 ≤ k := hk
  simp only [this, if_true]
  rw [add_comm] at step'
  exact step'

/-- Digit of a sum at position k (Euclidean %): valid for 0 ≤ n, m. -/
theorem Zdigit_plus_nonneg
    (n m k : Int) (hn : 0 ≤ n) (hm : 0 ≤ m) (hβ : beta > 1 := h_beta) :
    ⦃⌜0 ≤ k⌝⦄
    (pure (Zdigit beta (n + m) k) : Id _)
    ⦃⇓result => ⌜∃ dn dm carry,
                  Zdigit beta n k = dn ∧
                  Zdigit beta m k = dm ∧
                  carry ∈ ({0, 1} : Set Int) ∧
                  result = (dn + dm + carry) % beta⌝⦄ := by
  intro hk
  classical
  -- base and digit abbreviations (no `ite`!)
  let b : Int := beta ^ k.natAbs
  have hβpos : 0 < beta := by
    have : (0 : Int) < 1 := by decide
    exact lt_trans this hβ
  have hbpos : 0 < b := by simpa using pow_pos hβpos k.natAbs
  have hbne  : b ≠ 0 := ne_of_gt hbpos

  let dn : Int := (Int.tdiv n b) % beta
  let dm : Int := (Int.tdiv m b) % beta

  -- these are the two digit equalities we will return
  have dndef : Zdigit beta n k = dn := by
    unfold Zdigit
    have : 0 ≤ k := hk
    simp [this, b, dn]
  have dmdef : Zdigit beta m k = dm := by
    unfold Zdigit
    have : 0 ≤ k := hk
    simp [this, b, dm]

  -- define carry
  let carry : Int := (n % b + m % b) / b

  -- carry ∈ {0,1}
  have carry01 : carry ∈ ({0, 1} : Set Int) := by
    -- 0 ≤ remainders < b
    have h0n : 0 ≤ n % b := Int.emod_nonneg _ hbne
    have h0m : 0 ≤ m % b := Int.emod_nonneg _ hbne
    have hnlt : n % b < b := Int.emod_lt_of_pos _ hbpos
    have hmlt : m % b < b := Int.emod_lt_of_pos _ hbpos
    have hsum_lt : n % b + m % b < 2 * b := by
      have := add_lt_add hnlt hmlt
      simpa [two_mul] using this
    have hsum_nonneg : 0 ≤ n % b + m % b := add_nonneg h0n h0m

    by_cases hx : n % b + m % b < b
    · -- quotient = 0
      have hq : (n % b + m % b) / b = 0 :=
        Int.ediv_eq_zero_of_lt hsum_nonneg hx
      simp [carry, hq, Set.mem_insert_iff, Set.mem_singleton_iff]
    · -- quotient = 1
      have hge : b ≤ n % b + m % b := le_of_not_gt hx
      -- set y = sum - b with 0 ≤ y < b
      set y : Int := n % b + m % b - b
      have y_nonneg : 0 ≤ y := sub_nonneg.mpr hge
      have y_add : y + b = n % b + m % b := by
        dsimp [y]; exact sub_add_cancel _ _
      have y_lt : y < b := by
        have : y + b < b + b := by
          simpa [y_add, two_mul, add_comm, add_left_comm, add_assoc] using hsum_lt
        rw [add_comm y b] at this
        exact (Int.add_lt_add_iff_left b).1 this
      have y_div_zero : y / b = 0 :=
        Int.ediv_eq_zero_of_lt y_nonneg y_lt
      -- (y + b)/b = y/b + b/b = 0 + 1 = 1
      have hdiv_add :
          (y + b) / b = y / b + b / b := by
        have := Int.add_ediv_of_dvd_left
                  (a := b) (b := y) (c := b)
                  (by exact ⟨1, by ring⟩)
        simpa [add_comm] using this
      have hb_self : b / b = 1 := by simpa [hbne] using Int.ediv_self b
      have hq : (n % b + m % b) / b = 1 := by
        simp [← y_add, hdiv_add, y_div_zero, hb_self]
      simp [carry, hq, Set.mem_insert_iff, Set.mem_singleton_iff]

  -- quotient decomposition at base b
  have hnq : b * (n / b) + n % b = n := (Int.mul_ediv_add_emod n b)
  have hmq : b * (m / b) + m % b = m := (Int.mul_ediv_add_emod m b)

  -- derive: (n + m)/b = n/b + m/b + carry
  have hdiv :
      (n + m) / b = n / b + m / b + carry := by
    -- n + m = ((n/b + m/b) * b) + (n%b + m%b)
    have expand :
        n + m = ((n / b + m / b) * b) + (n % b + m % b) := by
      calc
        n + m
            = (b * (n / b) + n % b) + (b * (m / b) + m % b) := by
                simp [hnq, hmq]
        _ = (b * (n / b) + b * (m / b)) + (n % b + m % b) := by ring_nf
        _ = ((n / b + m / b) * b) + (n % b + m % b) := by ring
    -- divide both sides by b, splitting twice with `add_ediv_of_dvd_left`
    have hb_dvd₁ : b ∣ (n / b) * b := ⟨n / b, by ring⟩
    have hb_dvd₂ : b ∣ (m / b) * b := ⟨m / b, by ring⟩
    calc
      (n + m) / b
          = (((n / b) * b) + ((m / b) * b + (n % b + m % b))) / b := by
                simp only [expand]
                ring_nf
      _ = ((n / b) * b) / b + ((m / b) * b + (n % b + m % b)) / b := by
                simpa using
                  Int.add_ediv_of_dvd_left
                    (a := (n / b) * b) (b := ((m / b) * b + (n % b + m % b))) (c := b) hb_dvd₁
      _ = (n / b) + (((m / b) * b + (n % b + m % b)) / b) := by
                simpa [hbne] using
                  congrArg (fun t => t + ((m / b) * b + (n % b + m % b)) / b)
                    (Int.mul_ediv_cancel_left (a := n / b) (b := b) hbne)
      _ = (n / b) + ((m / b) + (n % b + m % b) / b) := by
                have h := Int.add_ediv_of_dvd_left
                    (a := (m / b) * b) (b := (n % b + m % b)) (c := b) hb_dvd₂
                rw [h]
                congr 1
                -- split the /b across the sum
                have hsplit :
                  ((m / b) * b + (n % b + m % b)) / b
                    = (m / b) * b / b + (n % b + m % b) / b := by
                  simpa using
                    Int.add_ediv_of_dvd_left
                      (a := (m / b) * b) (b := (n % b + m % b)) (c := b) ⟨m / b, by ring⟩

                -- cancel the (m/b)*b / b
                have hcancel : (m / b) * b / b = m / b := by
                  rw [mul_comm]
                  exact Int.mul_ediv_cancel_left (m / b) hbne

                -- use both facts at once
                simp [hcancel]
      _ = n / b + m / b + (n % b + m % b) / b := by ring

  -- convert dn, dm to Euclidean remainders (since n,m ≥ 0)
  have dn_ediv : dn = (n / b) % beta := by
    simp [dn, Int.tdiv_eq_ediv_of_nonneg hn]
  have dm_ediv : dm = (m / b) % beta := by
    simp [dm, Int.tdiv_eq_ediv_of_nonneg hm]

  -- final assembly
  refine ⟨dn, dm, carry, dndef, dmdef, carry01, ?_⟩

  -- Zdigit (n+m) k = ((n+m)/b) % β (since k ≥ 0)
  have hnm_nonneg : 0 ≤ n + m := add_nonneg hn hm
  have lhs :
      Zdigit beta (n + m) k = ((n + m) / b) % beta := by
    unfold Zdigit
    have : 0 ≤ k := hk
    simp [this, b, Int.tdiv_eq_ediv_of_nonneg hnm_nonneg]

  -- push `% beta` through additions
  calc
    Zdigit beta (n + m) k
        = ((n + m) / b) % beta := lhs
    _ = (n / b + m / b + carry) % beta := by simp [hdiv]
    _ = ((n / b + m / b) % beta + carry % beta) % beta := by
          rw [Int.add_emod]
    _ = (((n / b) % beta + (m / b) % beta) % beta + carry % beta) % beta := by
          congr 1
          rw [Int.add_emod]
    _ = ((dn + dm) % beta + carry % beta) % beta := by
          simp only [dn_ediv, dm_ediv]
    _ = (dn + dm + carry) % beta := by
          -- squash the duplicate mods and fold via `add_emod` backwards
          have hb_ne : beta ≠ 0 := ne_of_gt hβpos

          -- (x % β) % β = x % β
          have idem₁ :
              ((dn + dm) % beta) % beta = (dn + dm) % beta :=
            Int.emod_eq_of_lt
              (Int.emod_nonneg _ hb_ne) (Int.emod_lt_of_pos _ hβpos)
          have idem₂ :
              (carry % beta) % beta = carry % beta :=
            Int.emod_eq_of_lt
              (Int.emod_nonneg _ hb_ne) (Int.emod_lt_of_pos _ hβpos)

          -- ((a % β) + (b % β)) % β = (a + b) % β  (use `add_emod` backwards)
          have fold :
              ((dn + dm) % beta + carry % beta) % beta
                = (dn + dm + carry) % beta := by
            simp [Int.add_emod, add_comm]

          -- finish
          simp


/-- Scale a number by a power of beta -/
def Zscale (n k : Int) : Int :=
  (if 0 ≤ k then n * beta ^ k.natAbs else n / beta ^ (-k).natAbs)

/-- Monotonicity of {name}`wp` for {name}`Id` with a pure ({name full := PostCond.noThrow}`noThrow`) post. -/
private lemma wp_mono_pure
  {α : Type u} {prog : Id α}
  {Q Q' : α → Assertion PostShape.pure}
  (h    : (wp⟦prog⟧ (PostCond.noThrow Q)).down)
  (himp : ∀ r, (Q r).down → (Q' r).down) :
  (wp⟦prog⟧ (PostCond.noThrow Q')).down := by
  -- For `Id`, `wp⟦prog⟧ (noThrow Q)` definally reduces to `Q (Id.run prog)`.
  change (Q  (Id.run prog)).down at h
  change (Q' (Id.run prog)).down
  exact himp _ h

/-- Digit of scaled number

Coq theorem and proof:
```raw
Theorem Zdigit_scale :
  forall n k k', (0 <= k')%Z ->
  Zdigit (Zscale n k) k' = Zdigit n (k' - k).
Proof.
intros n k k' Hk'.
unfold Zscale.
case Zle_bool_spec ; intros Hk.
now apply Zdigit_mul_pow.
apply Zdigit_div_pow with (1 := Hk').
lia.
Qed.
```
-/
theorem Zdigit_scale_point
    (n k k' : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜0 ≤ k' ∧ (0 ≤ k ∨ 0 ≤ n)⌝⦄
    (pure (Zdigit beta (Zscale beta n k) k') : Id _)
    ⦃⇓result => ⌜Zdigit beta n (k' - k) = result⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hk', hk_or⟩
  by_cases hk : 0 ≤ k
  · -- k ≥ 0: use Zdigit_mul_pow
    have h := (Zdigit_mul_pow (beta := beta) (n := n) (k := k') (l := k) hβ) hk
    have h' :
        ∃ shifted,
          Zdigit beta n (k' - k) = shifted ∧
          Zdigit beta (n * beta ^ k.natAbs) k' = shifted := by
      simpa [wp, PostCond.noThrow, pure] using h
    rcases h' with ⟨shifted, hshifted, hres⟩
    simpa [Zscale, hk, hshifted, hres]
  · -- k < 0: use Zdigit_div_pow (need n ≥ 0)
    have hklt : k < 0 := lt_of_not_ge hk
    have hn_nonneg : 0 ≤ n := by
      cases hk_or with
      | inl hk_ge => exact (False.elim (hk hk_ge))
      | inr hn => exact hn
    by_cases hn0 : n = 0
    · simp [Zscale, hk, hn0, Zdigit]
    · have hnpos : 0 < n := lt_of_le_of_ne hn_nonneg (Ne.symm hn0)
      have hl : 0 ≤ -k := neg_nonneg.mpr (le_of_lt hklt)
      have h :=
        (Zdigit_div_pow (beta := beta) (n := n) (k := k') (l := -k) hβ) ⟨hl, hk', hnpos⟩
      have h' :
          ∃ shifted,
            Zdigit beta n (k' + -k) = shifted ∧
            Zdigit beta (n / beta ^ (-k).natAbs) k' = shifted := by
        simpa [wp, PostCond.noThrow, pure] using h
      rcases h' with ⟨shifted, hshifted, hres⟩
      have hres' : Zdigit beta (n / beta ^ k.natAbs) k' = shifted := by
        simpa using hres
      simpa [Zscale, hk, sub_eq_add_neg, hshifted, hres']
theorem Zscale_0 (k : Int) :
    ⦃⌜True⌝⦄
    (pure (Zscale beta 0 k) : Id _)
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro _
  unfold Zscale
  split <;> simp

/-- Scaling preserves sign (Euclidean division version). -/
theorem Zsame_sign_scale
    (n k : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜True⌝⦄
    (pure (Zscale beta n k) : Id _)
    ⦃⇓result =>
       ⌜
         ((0 < n → 0 ≤ result) ∧ (n < 0 → result ≤ 0))                                    -- (i)
         ∧ (0 ≤ k → ((0 < n → 0 < result) ∧ (n < 0 → result < 0)))                       -- (ii)
         ∧ (k < 0 → (result = 0 ↔ (0 ≤ n ∧ |n| < beta ^ (-k).natAbs)))                   -- (iii)
       ⌝⦄ := by
  intro _
  unfold Zscale
  by_cases hk : 0 ≤ k
  · --------------------------------------------------------------------  k ≥ 0: multiply
    have hβpos : 0 < beta := lt_trans (show (0:ℤ) < 1 by decide) hβ
    have hbpos  : 0 < beta ^ k.natAbs := pow_pos hβpos _
    have hbnn   : 0 ≤ beta ^ k.natAbs := le_of_lt hbpos
    simp [hk]   -- result = n * beta ^ k.natAbs
    -- After simp when k ≥ 0, goal becomes: ((0 < n → 0 ≤ result) ∧ (n < 0 → result ≤ 0)) ∧ (0 < n → 0 < result) ∧ (n < 0 → result < 0)
    -- Part (iii) is vacuous and disappears, part (ii)'s implication is simplified away
    refine And.intro ?i (And.intro ?ii_pos ?ii_neg)
    -- (i): Sign preservation (weak)
    · exact And.intro
        (fun hn => mul_nonneg (le_of_lt hn) hbnn)
        (fun hn => mul_nonpos_of_nonpos_of_nonneg (le_of_lt hn) hbnn)
    -- (ii) positive case: 0 < n → 0 < result
    · exact fun hn => mul_pos hn hbpos
    -- (ii) negative case: n < 0 → result < 0
    · exact fun hn => mul_neg_of_neg_of_pos hn hbpos
  · --------------------------------------------------------------------  k < 0: divide
    have hklt : k < 0 := lt_of_not_ge hk
    have hβpos : 0 < beta := lt_trans (show (0:ℤ) < 1 by decide) hβ
    have hbposK : 0 < beta ^ k.natAbs := pow_pos hβpos _
    simp [hk]   -- result = n / (beta ^ k.natAbs)
    -- After simp when k < 0, goal becomes: ((0 < n → 0 ≤ result) ∧ (n < 0 → result ≤ 0)) ∧ (k < 0 → (result = 0 ↔ ...))
    -- Part (ii) is vacuous and disappears
    constructor
    -- (i): Sign preservation
    · exact And.intro
        (fun hn => Int.ediv_nonneg (le_of_lt hn) (le_of_lt hbposK))
        (fun hn => (Int.ediv_neg_of_neg_of_pos hn hbposK).le)
    -- (iii): zero ↔ (0 ≤ n ∧ |n| < β^{(-k).natAbs})
    · intro _  -- we already have hklt
      -- Prove the version with k.natAbs, then rewrite exponent once at the end.
      have hkabs : (-k).natAbs = k.natAbs := by simpa using Int.natAbs_neg k
      constructor
      · -- → : result = 0 ⇒ 0 ≤ n ∧ |n| < β^{(-k).natAbs}
        intro hzero
        set d := beta ^ k.natAbs with hd
        have hdeq : n % d + d * (n / d) = n := by simpa [hd] using Int.emod_add_mul_ediv n d
        have hz : n / d = 0 := hzero
        have hmod_eq : n % d = n := by simpa [hz, mul_zero, add_zero] using hdeq
        have hmod_nonneg : 0 ≤ n % d := Int.emod_nonneg n (ne_of_gt hbposK)
        have hn0 : 0 ≤ n := by simpa [hmod_eq] using hmod_nonneg
        have hmod_lt : n % d < d := Int.emod_lt_of_pos n hbposK
        have habs_eq : |n| = n % d := by
          have h1 : |n| = |n % d| := by simp [hmod_eq]
          have h2 : |n % d| = n % d := abs_of_nonneg hmod_nonneg
          simpa [h2] using h1
        have hlt : |n| < d := by simpa [habs_eq] using hmod_lt
        -- rewrite `d` exponent from `k.natAbs` to `(-k).natAbs` only here
        simpa [hd, hkabs] using And.intro hn0 hlt
      · -- ← : (0 ≤ n ∧ |n| < β^{(-k).natAbs}) ⇒ result = 0
        intro hconj
        rcases hconj with ⟨hn0, hlt_abs⟩
        -- turn |n| < β^{(-k).natAbs} into n < β^{k.natAbs}
        have hlt_abs' : |n| < beta ^ k.natAbs := by simpa [hkabs] using hlt_abs
        have hn_lt : n < beta ^ k.natAbs := by
          have : |n| = n := abs_of_nonneg hn0
          simpa [this] using hlt_abs'
        exact Int.ediv_eq_zero_of_lt hn0 hn_lt

/-- Scaling and multiplication -/
theorem Zscale_mul_pow (n k l : Int) (hβ : beta > 1 := h_beta):
    ⦃⌜0 ≤ l⌝⦄
    (pure (Zscale beta (n * beta ^ l.natAbs) k) : Id _)
    ⦃⇓result => ⌜∃ scaled, Zscale beta n (k + l) = scaled ∧ result = scaled⌝⦄ := by
  intro hl
  unfold Zscale
  have hβpos : 0 < beta := by
    have : (0 : Int) < 1 := by decide
    exact lt_trans this hβ
  have hpowLpos : 0 < beta ^ l.natAbs := by simpa using pow_pos hβpos l.natAbs
  have hlabs : (l.natAbs : Int) = l := Int.natAbs_of_nonneg hl
  by_cases hk : 0 ≤ k
  · -- k ≥ 0, so k+l ≥ 0
    have hkl : 0 ≤ k + l := add_nonneg hk hl
    have hkabs : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk
    have hklabs : ((k + l).natAbs : Int) = k + l := Int.natAbs_of_nonneg hkl
    -- LHS: (n * β^l) * β^k = n * β^(k+l)
    simp only [hk, if_true]
    use n * beta ^ (k + l).natAbs
    constructor
    -- RHS: scale_{k+l} n = n * β^(k+l)
    · simp only [hkl, if_true]
    · calc (n * beta ^ l.natAbs) * beta ^ k.natAbs
        = n * (beta ^ l.natAbs * beta ^ k.natAbs) := by ring
        _ = n * beta ^ (l.natAbs + k.natAbs) := by rw [← pow_add]
        _ = n * beta ^ (k + l).natAbs := by
          congr 1
          have : l.natAbs + k.natAbs = (k + l).natAbs := by
            have eq_as_int : (l.natAbs : Int) + (k.natAbs : Int) = ((k + l).natAbs : Int) := by
              simp [hlabs, hkabs, hklabs, add_comm]
            exact Nat.cast_injective eq_as_int
          rw [this]
  · -- k < 0; write p := -k ≥ 0. Split on sign of (k + l).
    have hkneg : k < 0 := lt_of_not_ge hk
    have hp : 0 ≤ -k := neg_nonneg.mpr (le_of_lt hkneg)
    have hpabs : ((-k).natAbs : Int) = -k := Int.natAbs_of_nonneg hp
    -- LHS = (n * β^l) / β^(-k)
    simp only [hk, if_false]
    by_cases hsum : 0 ≤ k + l
    · -- k + l ≥ 0 ⇒ -k ≤ l, exact cancellation to multiplication
      have : -k ≤ l := by linarith
      -- β^{-k} ∣ β^l, so (n*β^l)/β^{-k} = n * β^{l - (-k)} = n * β^{k+l}
      have hsplit : beta ^ l.natAbs = beta ^ (-k).natAbs * beta ^ ((k + l).natAbs) := by
        -- use natAbs equalities: lAbs = l, (-k)Abs = -k, (k+l)Abs = k+l
        have hklabs : ((k + l).natAbs : Int) = k + l := Int.natAbs_of_nonneg hsum
        have : l.natAbs = (-k).natAbs + (k + l).natAbs := by
          -- Show equality at the Nat level using Int equality
          have eq_as_int : (l.natAbs : Int) = ((-k).natAbs : Int) + ((k + l).natAbs : Int) := by
            calc (l.natAbs : Int)
              = l := hlabs
              _ = -k + (k + l) := by ring
              _ = ((-k).natAbs : Int) + ((k + l).natAbs : Int) := by
                rw [hpabs, hklabs]
          exact Nat.cast_injective eq_as_int
        -- Now use pow_add
        rw [this, pow_add]
      -- use (a*c)/(a) = c style cancellation
      have hpos : 0 < beta ^ (-k).natAbs := by
        simpa using pow_pos hβpos (-k).natAbs
      have hne : beta ^ (-k).natAbs ≠ 0 := ne_of_gt hpos
      have : (n * beta ^ l.natAbs) / (beta ^ (-k).natAbs)
               = n * (beta ^ ((k + l).natAbs)) := by
        -- (n * (a*b)) / a = n*b
        -- rewrite β^l as a*b
        rw [hsplit]
        rw [← mul_assoc]
        rw [mul_comm n]
        rw [mul_assoc]
        rw [Int.mul_ediv_cancel_left _ hne]
      simp only [this]
      -- RHS: since k+l ≥ 0, Zscale beta n (k+l) = n * β^(k+l)
      use n * beta ^ (k + l).natAbs
      constructor
      · have hklabs : ((k + l).natAbs : Int) = k + l := Int.natAbs_of_nonneg hsum
        simp only [hsum, if_true]
      · rfl
    · -- k + l < 0 ⇒ write q := -(k + l) > 0, and show division-by-composed-power
      have hq : 0 ≤ -(k + l) := by exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge hsum))
      have hqlt : k + l < 0 := lt_of_not_ge hsum
      have hklabs : ((k + l).natAbs : Int) = -(k + l) := by
        have : k + l ≤ 0 := le_of_lt hqlt
        exact Int.ofNat_natAbs_of_nonpos this
      -- identity: (n*β^l) / β^{-k} = n / β^{-(k+l)}
      -- since β^{-k} = β^l * β^{-(k+l)} (as Int exponents)
      have hsplit : beta ^ (-k).natAbs = beta ^ l.natAbs * beta ^ (-(k + l)).natAbs := by
        -- -k = l + (-(k+l))
        have : (-k) = l + (-(k + l)) := by ring
        -- rewrite in natAbs form
        have hpabs' : ((-k).natAbs : Int) = -k := Int.natAbs_of_nonneg (neg_nonneg.mpr (le_of_lt hkneg))
        have hlabs' : (l.natAbs : Int) = l := Int.natAbs_of_nonneg hl
        have hqabs' : ((-(k + l)).natAbs : Int) = -(k + l) := Int.natAbs_of_nonneg hq
        -- now pow_add on Nat side corresponds to multiplication
        -- we just need the multiplicative identity afterwards
        -- so:
        have : (-k).natAbs = l.natAbs + (-(k + l)).natAbs := by
          -- Show equality at the Nat level using Int equality
          have eq_as_int : ((-k).natAbs : Int) = (l.natAbs : Int) + ((-(k + l)).natAbs : Int) := by
            calc ((-k).natAbs : Int)
              = -k := hpabs'
              _ = l + (-(k + l)) := this
              _ = (l.natAbs : Int) + ((-(k + l)).natAbs : Int) := by
                rw [hlabs']
                have : ((-(k + l)).natAbs : Int) = -(k + l) :=
                  Int.natAbs_of_nonneg hq
                rw [this]
          exact Nat.cast_injective eq_as_int
        rw [this, pow_add]
      have hposc : 0 < beta ^ l.natAbs := hpowLpos
      have hpos_kl : 0 < beta ^ (-(k + l)).natAbs := pow_pos hβpos _
      have : (n * beta ^ l.natAbs) / (beta ^ (-k).natAbs)
               = n / (beta ^ (-(k + l)).natAbs) := by
        -- (a*c)/(b*c) = a/b with c>0
        rw [hsplit]
        -- Now we have (n * beta^l.natAbs) / (beta^l.natAbs * beta^(-(k+l)).natAbs)
        -- We'll use the fact that (a * b) / (b * c) = a / c when b > 0
        rw [mul_comm (beta ^ l.natAbs) (beta ^ (-(k + l)).natAbs)]
        -- Now: (n * beta^l.natAbs) / (beta^(-(k+l)).natAbs * beta^l.natAbs)
        -- Apply Int.mul_ediv_mul_of_pos_left
        exact Int.mul_ediv_mul_of_pos_left _ _ hposc
      simp only [this]
      -- RHS: since k+l < 0, Zscale n (k+l) divides by β^{-(k+l)}
      use n / beta ^ (-(k + l)).natAbs
      constructor
      · simp only [not_le.mpr hqlt, if_false]
      · rfl

/-- Helper lemma: For Zscale composition to work correctly, we need divisibility
    This captures the requirement that values in floating-point systems are
    properly normalized (i.e., mantissas are multiples of appropriate base powers) -/
private lemma zscale_div_exact (n d : Int) (_hd : d > 0) (hdiv : d ∣ n) :
    (n / d) * d = n := by
  exact Int.ediv_mul_cancel hdiv

/-- Composition of scaling
    Note: This theorem assumes proper divisibility conditions for the scaling operations
    to compose correctly. These are typically satisfied in floating-point systems with
    normalized mantissas. -/
theorem Zscale_scale (n k l : Int) (hβ : beta > 1 := h_beta)
    (hdiv_k : k < 0 → beta ^ (-k).natAbs ∣ n)
    (_hdiv_compose : k < 0 → l ≥ 0 → k + l < 0 → beta ^ l.natAbs ∣ n) :
    ⦃⌜True⌝⦄
    (pure (Zscale beta (Zscale beta n k) l) : Id _)
    ⦃⇓result => ⌜∃ scaled, Zscale beta n (k + l) = scaled ∧ result = scaled⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure]
  by_cases hk : 0 ≤ k
  · -- k ≥ 0: reduce to Zscale_mul_pow
    have h :=
      (Zscale_mul_pow (beta := beta) (n := n) (k := l) (l := k) hβ) hk
    have h' :
        ∃ scaled,
          Zscale beta n (l + k) = scaled ∧
          Zscale beta (n * beta ^ k.natAbs) l = scaled := by
      simpa [wp, PostCond.noThrow, pure] using h
    rcases h' with ⟨scaled, hscaled, hres⟩
    calc
      Zscale beta (Zscale beta n k) l
          = Zscale beta (n * beta ^ k.natAbs) l := by simp [Zscale, hk]
      _ = scaled := hres
      _ = Zscale beta n (l + k) := by symm; exact hscaled
      _ = Zscale beta n (k + l) := by simp [add_comm]
  · -- k < 0
    have hklt : k < 0 := lt_of_not_ge hk
    have hβpos : 0 < beta := lt_trans (by decide : (0 : Int) < 1) hβ
    have hk_nonneg : 0 ≤ -k := neg_nonneg.mpr (le_of_lt hklt)
    have hkabs : ((-k).natAbs : Int) = -k := Int.natAbs_of_nonneg hk_nonneg
    have hdpos : 0 < beta ^ (-k).natAbs := pow_pos hβpos _
    have hdiv_d : beta ^ (-k).natAbs ∣ n := hdiv_k hklt
    by_cases hl : 0 ≤ l
    · -- l ≥ 0
      have hlabs : (l.natAbs : Int) = l := Int.natAbs_of_nonneg hl
      by_cases hsum : 0 ≤ k + l
      · -- k + l ≥ 0
        have hklabs : ((k + l).natAbs : Int) = k + l := Int.natAbs_of_nonneg hsum
        have hdiv_exact :
              (n / beta ^ (-k).natAbs) * beta ^ (-k).natAbs = n := by
            exact zscale_div_exact n (beta ^ (-k).natAbs) hdpos hdiv_d
        have hnat :
            l.natAbs = (-k).natAbs + (k + l).natAbs := by
          have eq_as_int :
              (l.natAbs : Int) =
                ((-k).natAbs : Int) + ((k + l).natAbs : Int) := by
            calc (l.natAbs : Int)
                = l := hlabs
            _ = -k + (k + l) := by ring
            _ = ((-k).natAbs : Int) + ((k + l).natAbs : Int) := by
                rw [hkabs, hklabs]
          exact Nat.cast_injective eq_as_int
        have hpow :
            beta ^ l.natAbs =
              beta ^ (-k).natAbs * beta ^ (k + l).natAbs := by
          rw [hnat, pow_add]
        calc
          Zscale beta (Zscale beta n k) l
              = (n / beta ^ (-k).natAbs) * beta ^ l.natAbs := by
                simp [Zscale, hk, hl]
          _ =
              (n / beta ^ (-k).natAbs) *
                (beta ^ (-k).natAbs * beta ^ (k + l).natAbs) := by
                simp [hpow]
          _ =
              ((n / beta ^ (-k).natAbs) * beta ^ (-k).natAbs) *
                beta ^ (k + l).natAbs := by
                ac_rfl
          _ = n * beta ^ (k + l).natAbs := by
                rw [hdiv_exact]
          _ = Zscale beta n (k + l) := by
                simp [Zscale, hsum]
      · -- k + l < 0
        have hqlt : k + l < 0 := lt_of_not_ge hsum
        have hq_nonneg : 0 ≤ -(k + l) := neg_nonneg.mpr (le_of_lt hqlt)
        have hqabs : ((-(k + l)).natAbs : Int) = -(k + l) :=
          Int.natAbs_of_nonneg hq_nonneg
        have hnat :
              (-k).natAbs = l.natAbs + (-(k + l)).natAbs := by
            have eq_as_int :
                ((-k).natAbs : Int) =
                  (l.natAbs : Int) + ((-(k + l)).natAbs : Int) := by
              calc ((-k).natAbs : Int)
                  = -k := hkabs
              _ = l + (-(k + l)) := by ring
              _ = (l.natAbs : Int) + ((-(k + l)).natAbs : Int) := by
                  rw [hlabs, hqabs]
            exact Nat.cast_injective eq_as_int
        have hpow :
            beta ^ (-k).natAbs =
              beta ^ l.natAbs * beta ^ (-(k + l)).natAbs := by
          rw [hnat, pow_add]
        have hdiv_de :
            beta ^ (-(k + l)).natAbs ∣ beta ^ (-k).natAbs := by
          refine ⟨beta ^ l.natAbs, ?_⟩
          rw [hpow]
          simp [mul_comm]
        have hdiv_exact :
            (n / beta ^ (-k).natAbs) * beta ^ (-k).natAbs = n := by
          exact zscale_div_exact n (beta ^ (-k).natAbs) hdpos hdiv_d
        have hmul_assoc :
            ((n / beta ^ (-k).natAbs) * beta ^ (-k).natAbs) /
                beta ^ (-(k + l)).natAbs
              = (n / beta ^ (-k).natAbs) *
                  (beta ^ (-k).natAbs / beta ^ (-(k + l)).natAbs) := by
          simpa using
            (Int.mul_ediv_assoc (n / beta ^ (-k).natAbs) hdiv_de)
        have hratio :
            beta ^ (-k).natAbs / beta ^ (-(k + l)).natAbs =
              beta ^ l.natAbs := by
          have hne : beta ^ (-(k + l)).natAbs ≠ 0 :=
            ne_of_gt (pow_pos hβpos _)
          calc
            beta ^ (-k).natAbs / beta ^ (-(k + l)).natAbs
                = (beta ^ l.natAbs * beta ^ (-(k + l)).natAbs) /
                    beta ^ (-(k + l)).natAbs := by
                      rw [hpow]
            _ = (beta ^ (-(k + l)).natAbs * beta ^ l.natAbs) /
                    beta ^ (-(k + l)).natAbs := by
                      simp [mul_comm]
            _ = beta ^ l.natAbs := by
                      simpa using
                        (Int.mul_ediv_cancel_left
                          (a := beta ^ (-(k + l)).natAbs)
                          (b := beta ^ l.natAbs)
                          hne)
        have hmain :
            n / beta ^ (-(k + l)).natAbs =
              (n / beta ^ (-k).natAbs) * beta ^ l.natAbs := by
          calc
            n / beta ^ (-(k + l)).natAbs
                = ((n / beta ^ (-k).natAbs) * beta ^ (-k).natAbs) /
                    beta ^ (-(k + l)).natAbs := by
                      rw [hdiv_exact]
            _ = (n / beta ^ (-k).natAbs) *
                  (beta ^ (-k).natAbs / beta ^ (-(k + l)).natAbs) := hmul_assoc
            _ = (n / beta ^ (-k).natAbs) * beta ^ l.natAbs := by
                      rw [hratio]
        calc
          Zscale beta (Zscale beta n k) l
              = (n / beta ^ (-k).natAbs) * beta ^ l.natAbs := by
                simp [Zscale, hk, hl]
          _ = n / beta ^ (-(k + l)).natAbs := by
                symm; exact hmain
          _ = Zscale beta n (k + l) := by
                simp [Zscale, hsum]
    · -- l < 0
      have hl_neg : l < 0 := lt_of_not_ge hl
      have hsum : k + l < 0 := by linarith
      have hsum_nonneg : 0 ≤ -(k + l) := neg_nonneg.mpr (le_of_lt hsum)
      have hkabs' : ((-k).natAbs : Int) = -k := hkabs
      have hlabs : ((-l).natAbs : Int) = -l :=
        Int.natAbs_of_nonneg (neg_nonneg.mpr (le_of_lt hl_neg))
      have hsumabs : ((-(k + l)).natAbs : Int) = -(k + l) :=
        Int.natAbs_of_nonneg hsum_nonneg
      have hnat :
            (-k).natAbs + (-l).natAbs = (-(k + l)).natAbs := by
        have eq_as_int :
            ((-k).natAbs : Int) + ((-l).natAbs : Int)
              = ((-(k + l)).natAbs : Int) := by
          calc ((-k).natAbs : Int) + ((-l).natAbs : Int)
              = -k + -l := by rw [hkabs', hlabs]
          _ = -(k + l) := by ring
          _ = ((-(k + l)).natAbs : Int) := by
              rw [hsumabs]
        exact Nat.cast_injective eq_as_int
      have hpow :
          beta ^ (-k).natAbs * beta ^ (-l).natAbs =
            beta ^ (-(k + l)).natAbs := by
        -- rearrange pow_add
        have := congrArg (fun t => beta ^ t) hnat
        simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using this
      have hdiv_assoc :
          (n / beta ^ (-k).natAbs) / beta ^ (-l).natAbs
            = n / (beta ^ (-k).natAbs * beta ^ (-l).natAbs) := by
        have hb_nonneg : 0 ≤ beta ^ (-k).natAbs := le_of_lt hdpos
        simpa using (Int.ediv_ediv_of_nonneg hb_nonneg)
      calc
        Zscale beta (Zscale beta n k) l
            = (n / beta ^ (-k).natAbs) / beta ^ (-l).natAbs := by
              simp [Zscale, hk, hl]
        _ = n / (beta ^ (-k).natAbs * beta ^ (-l).natAbs) := hdiv_assoc
        _ = n / beta ^ (-(k + l)).natAbs := by
              rw [hpow]
        _ = Zscale beta n (k + l) := by
              simp [Zscale, hsum]
/-- Slice digits: scale by {name}`Zscale` with exponent -k1, then take the
remainder modulo beta^k2 when 0 ≤ k2 (otherwise 0). -/
def Zslice (n k1 k2 : Int) : Int :=
  let scaled := Zscale beta n (-k1)
  if 0 ≤ k2 then scaled % beta ^ k2.natAbs else 0

/-- Digit of slice

Coq theorem and proof:
```raw
Theorem Zdigit_slice :
  forall n k l m, (0 <= m)%Z ->
  Zdigit (Zslice n k l) m =
  if Zlt_bool m l then Zdigit n (k + m) else Z0.
Proof.
intros n k l m Hm.
unfold Zslice.
case Zle_bool_spec ; intros Hl.
rewrite Zdigit_mod_pow.
case Zlt_bool.
apply Zdigit_scale.
exact Hm.
exact Hm.
case Zlt_bool_spec ; intros Hl'.
exact Hm.
lia.
rewrite Zdigit_0.
case Zlt_bool.
apply refl_equal.
apply refl_equal.
Qed.
```
-/
theorem Zdigit_slice (n k l m : Int) (h_beta : beta > 1) :
    ⦃⌜0 ≤ m ∧ 0 ≤ n⌝⦄
    (pure (Zdigit beta ((Zslice beta n k l)) m) : Id _)
    ⦃⇓result =>
        ⌜if m < l then
            ∃ orig, Zdigit beta n (k + m) = orig ∧ result = orig
          else result = 0⌝⦄ := by
  sorry
/-- Digit of slice outside range

Coq theorem and proof:
```raw
Theorem Zdigit_slice_out :
  forall n k l m, (l <= m)%Z ->
  Zdigit (Zslice n k l) m = Z0.
Proof.
intros n k l m Hm.
case (Zle_or_lt 0 m) ; intros Hm'.
rewrite Zdigit_slice.
rewrite Zlt_bool_false.
apply refl_equal.
exact Hm.
exact Hm'.
apply Zdigit_lt.
exact Hm'.
Qed.
```
-/
theorem Zdigit_slice_out (n k l m : Int) (h_beta : beta > 1):
    ⦃⌜l ≤ m⌝⦄
    (pure (Zdigit beta ((Zslice beta n k l)) m) : Id _)
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  sorry
/-- Zslice of zero is always zero

Coq theorem and proof:
```raw
Theorem Zslice_0 :
  forall k k',
  Zslice 0 k k' = Z0.
Proof.
intros k k'.
unfold Zslice.
case Zle_bool.
rewrite Zscale_0.
apply Zrem_0_l.
apply refl_equal.
Qed.
```
-/
theorem Zslice_0 (k k' : Int) :
    ⦃⌜True⌝⦄
    (pure (Zslice beta 0 k k') : Id _)
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro _
  unfold Zslice Zscale
  simp

/-- Slicing preserves sign conditions

Coq theorem and proof:
```raw
Theorem Zsame_sign_slice :
  forall n k l,
  (0 <= n)%Z -> (0 <= k)%Z -> (0 <= l)%Z ->
  (0 <= Zslice n k l)%Z.
Proof.
intros n k l Hn Hk Hl.
unfold Zslice.
case Zle_bool.
apply Zrem_ge_0.
apply Zpower_ge_0.
apply Zsame_sign_scale.
lia.
apply Zsame_sign_scale.
exact Hn.
Qed.
```
-/
theorem Zsame_sign_slice (n k l : Int) (h_beta : beta > 1):
    ⦃⌜0 ≤ n ∧ 0 ≤ k ∧ 0 ≤ l⌝⦄
    (pure (Zslice beta n k l) : Id _)
    ⦃⇓result => ⌜0 ≤ result⌝⦄ := by
  intro h
  rcases h with ⟨_hn, _hk, hl⟩
  -- Open the definition and use the `0 ≤ l` branch.
  unfold Zslice
  -- After rewriting the `if`, the wp reduces to a predicate on the result of `Zscale`.
  -- `simp [hl]` both selects the `then` branch and simplifies the wp for `Id`.
  simp [hl]
  -- Goal now is: 0 ≤ (Zscale beta n (-k)) % (beta ^ l.natAbs)
  have hβpos : 0 < beta :=
    lt_trans (show (0 : Int) < 1 by decide) h_beta
  have hpowpos : 0 < beta ^ l.natAbs := pow_pos hβpos _
  -- Remainder modulo a positive number is nonnegative.
  exact Int.emod_nonneg _ (ne_of_gt hpowpos)

/-- Composition of Zslice operations

Coq theorem and proof:
```raw
Theorem Zslice_slice :
  forall n k1 k2 k1' k2',
  (0 <= k1')%Z -> (k1' <= k2)%Z ->
  Zslice (Zslice n k1 k2) k1' k2' = Zslice n (k1 + k1') (Z.min (k2 - k1') k2').
Proof.
intros n k1 k2 k1' k2' Hk1' Hk2.
destruct (Zle_or_lt 0 k2') as [Hk2'|Hk2'].
2: now rewrite 2!Zslice_0.
apply Zdigit_ext.
intros k Hk.
rewrite Zdigit_slice.
case Zlt_bool_spec ; intros H.
rewrite Zdigit_slice.
rewrite Zdigit_slice.
case Zlt_bool_spec ; intros H0.
case Zlt_bool_spec ; intros H1.
apply f_equal.
ring.
now rewrite Zdigit_slice_out.
now rewrite Zdigit_slice_out with (1 := H0).
exact Hk1'.
now apply Zplus_le_0_compat.
exact Hk.
rewrite (Zdigit_slice_out n (k1 + k1')) with (2 := H).
apply Zdigit_slice_out.
lia.
exact Hk.
Qed.
```
-/
theorem Zslice_slice (n k1 k2 k1' k2' : Int) (h_beta : beta > 1) :
    ⦃⌜0 < n ∧ 0 ≤ k1' ∧ k1' ≤ k2⌝⦄
    (pure (Zslice beta ((Zslice beta n k1 k2)) k1' k2') : Id _)
    ⦃⇓result =>
       ⌜∃ inner_slice,
          Zslice beta n (k1 + k1') (min (k2 - k1') k2') = inner_slice ∧
          result = inner_slice⌝⦄ := by
  sorry
/-- Zslice and multiplication by power of beta

Coq theorem and proof:
```raw
Theorem Zslice_mul_pow :
  forall n k k1 k2,
  (0 <= k)%Z ->
  Zslice (n * Zpower beta k) k1 k2 = Zslice n (k1 - k) k2.
Proof.
intros n k k1 k2 Hk.
unfold Zslice.
rewrite Zscale_mul_pow with (1 := Hk).
ring_simplify (k1 - k + k)%Z.
apply refl_equal.
Qed.
```
-/
theorem Zslice_mul_pow (n k k1 k2 : Int) (h_beta : beta > 1):
    ⦃⌜0 ≤ k⌝⦄
    (pure (Zslice beta (n * beta ^ k.natAbs) k1 k2) : Id _)
    ⦃⇓result => ⌜∃ slice_shifted, Zslice beta n (k1 - k) k2 = slice_shifted ∧
                  result = slice_shifted⌝⦄ := by
  sorry
/-- Zslice and division by power of beta

Coq theorem and proof:
```raw
Theorem Zslice_div_pow :
  forall n k k1 k2,
  (0 <= k)%Z -> (0 <= k1)%Z ->
  Zslice (Z.quot n (Zpower beta k)) k1 k2 = Zslice n (k1 + k) k2.
Proof.
intros n k k1 k2 Hk Hk1.
unfold Zslice.
rewrite Zdigit_div_pow with (1 := Hk1) (2 := Hk).
ring_simplify (- (k1 + k) + (k1 + k))%Z.
case Zle_bool.
apply f_equal.
rewrite Zscale_0.
apply Zdigit_0.
apply refl_equal.
Qed.
```
-/
theorem Zslice_div_pow (n k k1 k2 : Int) (h_beta : beta > 1):
    ⦃⌜0 ≤ k ∧ 0 ≤ k1⌝⦄
    (pure (Zslice beta (n / beta ^ k.natAbs) k1 k2) : Id _)
    ⦃⇓result => ⌜∃ slice_shifted, Zslice beta n (k1 + k) k2 = slice_shifted ∧
                  result = slice_shifted⌝⦄ := by
  sorry
/-- Zslice and scaling

Coq theorem and proof:
```raw
Theorem Zslice_scale :
  forall n k k1 k2,
  (0 <= k1)%Z ->
  Zslice (Zscale n k) k1 k2 = Zslice n (k1 - k) k2.
Proof.
intros n k k1 k2 Hk1.
unfold Zslice.
rewrite Zscale_scale.
ring_simplify (- k1 + (k1 - k))%Z.
apply refl_equal.
Qed.
```
-/
theorem Zslice_scale (n k k1 k2 : Int) (h_beta : beta > 1)
    (hdiv_k : k < 0 → beta ^ (-k).natAbs ∣ n):
    ⦃⌜0 ≤ k1⌝⦄
    (pure (Zslice beta (Zscale beta n k) k1 k2) : Id _)
    ⦃⇓result => ⌜∃ slice_unscaled, Zslice beta n (k1 - k) k2 = slice_unscaled ∧
                  result = slice_unscaled⌝⦄ := by
  sorry
private lemma div_mul_pow_eq_div_sub
    (n a b : Int) (beta : Int) (h_beta : beta > 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b ≤ a)
    (hdiv : beta ^ a.natAbs ∣ n) :
    (n / beta ^ a.natAbs) * beta ^ b.natAbs
      = n / beta ^ (a - b).natAbs := by
  -- Split the divisibility
  rcases hdiv with ⟨t, ht⟩   -- n = (β^a) * t
  have hβpos : 0 < beta := lt_trans (show (0 : Int) < 1 by decide) h_beta
  have hpow_a_pos : 0 < beta ^ a.natAbs := pow_pos hβpos _
  have hpow_ab_pos : 0 < beta ^ (a - b).natAbs := pow_pos hβpos _
  have hpow_a_ne : beta ^ a.natAbs ≠ 0 := ne_of_gt hpow_a_pos
  have hpow_ab_ne : beta ^ (a - b).natAbs ≠ 0 := ne_of_gt hpow_ab_pos

  -- a, b nonneg & b ≤ a ⇒ a = b + (a-b) at the NatAbs level
  have hab_nonneg : 0 ≤ a - b := sub_nonneg_of_le hab
  have hnatsumZ :
      (a.natAbs : ℤ)
        = (b.natAbs : ℤ) + ((a - b).natAbs : ℤ) := by
    -- With nonnegativity, natAbs casts back to the integer itself
    have haZ  : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha
    have hbZ  : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg hb
    have habZ : ((a - b).natAbs : ℤ) = a - b :=
      Int.natAbs_of_nonneg hab_nonneg
    simpa [haZ, hbZ, habZ]
  have hnatsum :
      a.natAbs = b.natAbs + (a - b).natAbs :=
    (Nat.cast_injective hnatsumZ)

  -- β^a = β^b * β^(a-b)
  have power_split :
      beta ^ a.natAbs = beta ^ b.natAbs * beta ^ (a - b).natAbs := by
    simpa [hnatsum, pow_add]

  -- Rewrite both sides to the same canonical form: t * β^b
  -- Left side
  have lhs_eq :
      (n / beta ^ a.natAbs) * beta ^ b.natAbs
        = t * beta ^ b.natAbs := by
    -- n = (β^a) * t
    -- so (n / β^a) = t, because division is exact
    have : n / beta ^ a.natAbs = t := by
      -- ((β^a) * t) / (β^a) = t
      -- use cancel-on-the-left for integer division
      -- this is a standard simp fact
      simpa [ht, mul_comm, mul_left_comm, mul_assoc] using
        Int.mul_ediv_cancel_left t hpow_a_ne
    simpa [this]

  -- Right side (rewrite, then cancel the left factor)
  have rhs_eq :
      n / beta ^ (a - b).natAbs
        = t * beta ^ b.natAbs := by
    -- rewrite n as  (β^(a-b)) * (β^b * t)
    have hn :
      n = (beta ^ (a - b).natAbs) * (beta ^ b.natAbs * t) := by
        calc
          n = beta ^ a.natAbs * t := ht
          _ = (beta ^ b.natAbs * beta ^ (a - b).natAbs) * t := by
                simpa [power_split, mul_comm, mul_left_comm, mul_assoc]
          _ = beta ^ (a - b).natAbs * (beta ^ b.natAbs * t) := by
                ring
    -- cancel β^(a-b) on the left
    have := Int.mul_ediv_cancel_left (beta ^ b.natAbs * t) hpow_ab_ne
    simpa [hn, mul_comm, mul_left_comm, mul_assoc] using this

  have rhs_eq_comm :
    beta ^ b.natAbs * t = n / beta ^ (a - b).natAbs := by
      -- rhs_eq : n / ... = t * beta ^ b.natAbs
      -- so beta^b * t = n / ... after commuting and symmetry
      simpa [mul_comm] using rhs_eq.symm

  -- Finish: commutativity aligns both sides
  calc
    (n / beta ^ a.natAbs) * beta ^ b.natAbs
        = t * beta ^ b.natAbs := lhs_eq
    _   = beta ^ b.natAbs * t := by simpa [mul_comm]
    _   = n / beta ^ (a - b).natAbs := rhs_eq_comm


/-- Combined division and scaling for Zslice

Coq theorem and proof:
```raw
Theorem Zslice_div_pow_scale :
  forall n k k' k1 k2,
  (0 <= k)%Z ->
  Zslice (Z.quot n (Zpower beta k) * Zpower beta k') k1 k2 = Zslice n (k1 + k - k') k2.
Proof.
intros n k k' k1 k2 Hk.
case (Zle_or_lt 0 k') ; intros Hk'.
rewrite Zslice_mul_pow with (1 := Hk').
rewrite Zslice_div_pow with (1 := Hk).
ring.
apply Zle_minus_le_0.
exact Hk'.
replace k' with (- (- k'))%Z by ring.
rewrite <- Zpower_Zopp.
rewrite <- Zquot_Zquot.
2: apply Zgt_not_eq, Zpower_gt_0 ; lia.
2: apply Zgt_not_eq, Zpower_gt_0 ; lia.
rewrite Zslice_div_pow.
ring.
now apply Zlt_le_weak.
lia.
Qed.
```
-/
theorem Zslice_div_pow_scale_nonnegKp
    (n k k' k1 k2 : Int) (h_beta : beta > 1)
    : ⦃⌜0 ≤ k ∧ 0 ≤ k1 ∧ 0 ≤ k' ∧ k1 ≥ k'⌝⦄
      (pure (Zslice beta ((n / beta ^ k.natAbs) * beta ^ k'.natAbs) k1 k2) : Id _)
      ⦃⇓result =>
         ⌜∃ slice_combined,
            Zslice beta n (k1 + k - k') k2 = slice_combined ∧
            result = slice_combined⌝⦄ := by
  intro ⟨hk, hk1, hk', hk1_ge_k'⟩

  -- Step 1: multiply by β^k' shifts index by -k'
  have hmul := Zslice_mul_pow beta (n / beta ^ k.natAbs) k' k1 k2 h_beta
  have hmul_spec := hmul hk'
  -- hmul_spec :
  --   (wp⟦Zslice β ((n/β^k) * β^k') k1 k2⟧
  --      (PostCond.noThrow fun s1 =>
  --         ⌜Zslice β (n/β^k) (k1 - k') k2 = s1⌝)).down
  unfold wp PostCond.noThrow at hmul_spec
  simp only [Id.instWP, PredTrans.pure] at hmul_spec
  obtain ⟨slice1, h_eq1, h_eq2⟩ := hmul_spec
  -- h_eq1 : Zslice β (n/β^k) (k1 - k') k2 = slice1
  -- h_eq2 : Zslice β ((n/β^k) * β^k') k1 k2 = slice1

  -- Step 2: divide by β^k shifts index by +k
  have hk1_k' : 0 ≤ k1 - k' := by
    -- We have k1 ≥ k' from the precondition
    linarith
  have hdiv := Zslice_div_pow beta n k (k1 - k') k2 h_beta
  have hdiv_spec := hdiv ⟨hk, hk1_k'⟩
  -- hdiv_spec :
  --   (wp⟦Zslice β (n/β^k) (k1 - k') k2⟧
  --      (PostCond.noThrow fun s2 =>
  --         ⌜Zslice β n ((k1 - k') + k) k2 = s2⌝)).down
  unfold wp PostCond.noThrow at hdiv_spec
  simp only [Id.instWP, PredTrans.pure] at hdiv_spec
  obtain ⟨slice2, h_eq3, h_eq4⟩ := hdiv_spec
  -- h_eq3 : Zslice β n ((k1 - k') + k) k2 = slice2
  -- h_eq4 : Zslice β (n/β^k) (k1 - k') k2 = slice2

  -- Step 3: tie slices together
  -- From h_eq1 and h_eq4, both are evaluations of the same LHS:
  --   Zslice β (n/β^k) (k1 - k') k2 = slice1  and = slice2
  have run_eq_slice1 : (Zslice beta (n / beta ^ k.natAbs) (k1 - k') k2) = slice1 := by
    simpa using h_eq1
  have : slice1 = slice2 := by
    -- combine the two equalities by transitivity
    have h_eq_slice2 : (Zslice beta (n / beta ^ k.natAbs) (k1 - k') k2) = slice2 := by
      simpa using h_eq4
    -- We have run_eq_slice1: Zslice ... = slice1
    -- And h_eq_slice2: Zslice ... = slice2
    -- Therefore slice1 = slice2
    exact run_eq_slice1.symm.trans h_eq_slice2
  -- Now produce the required witness and finish
  use slice2
  constructor
  · -- rewrite ((k1 - k') + k) = (k1 + k - k')
    have : (k1 - k') + k = k1 + k - k' := by ring
    simpa [this]
      using h_eq3
  · -- LHS result equals slice2
    -- h_eq2 : run (Zslice β ((n/β^k) * β^k') k1 k2) = slice1
    -- so it equals slice2 by the equality just proved
    simp only [h_eq2]
    exact this

/-- Addition and Zslice interaction

Coq theorem and proof:
```raw
Theorem Zplus_slice :
  forall n m k l,
  (0 <= k)%Z -> (0 <= l)%Z ->
  (Zslice (n + m) k l = Zslice n k l + Zslice m k l \/
   Zslice (n + m) k l = (Zslice n k l + Zslice m k l + 1) %% Zpower beta l)%Z.
Proof.
intros n m k l Hk Hl.
unfold Zslice.
case Zle_bool_spec ; intros H.
2: left ; now rewrite 3!Zrem_0_r.
apply Zplus_slice_aux.
exact Hl.
Qed.
```
-/
theorem Zplus_slice (n m k l : Int) (h_beta : beta > 1) :
    ⦃⌜0 ≤ k ∧ 0 ≤ l⌝⦄
    (pure (Zslice beta (n + m) k l) : Id _)
    ⦃⇓result => ⌜∃ n_slice m_slice,
                  Zslice beta n k l = n_slice ∧
                  Zslice beta m k l = m_slice ∧
                  (result = (n_slice + m_slice) % beta ^ l.natAbs ∨
                   result = (n_slice + m_slice + 1) % beta ^ l.natAbs)⌝⦄ := by
  sorry
/-- Fuel-bounded digit counter helper for Zdigits. -/
def Zdigits_aux (n d pow : Int) : Nat → Int
  | 0        => d
  | fuel+1   => if Int.natAbs n < pow then d
                else Zdigits_aux n (d + 1) (beta * pow) fuel

/-- Number of digits of an integer. -/
def Zdigits (n : Int) : Int :=
  if _h : n = 0 then 0
  else
    -- start at d = 1 with pow = beta^1 = beta
    let fuel := (Int.natAbs n).succ
    Zdigits_aux beta n 1 beta fuel

/- Correctness of digit count bounds

Coq theorem and proof:
```raw
Theorem Zdigits_correct :
  forall n,
  (Zpower beta (Zdigits n - 1) <= Z.abs n < Zpower beta (Zdigits n))%Z.
Proof.
cut (forall p, Zpower beta (Zdigits (Zpos p) - 1) <= Zpos p < Zpower beta (Zdigits (Zpos p)))%Z.
intros H [|n|n] ; try exact (H n).
now split.
intros n.
simpl.
(* Uses auxiliary induction on positive numbers with radix representation *)
assert (U: (Zpos n < Zpower beta (Z_of_nat (S (digits2_Pnat n))))%Z).
apply Z.lt_le_trans with (1 := proj2 (digits2_Pnat_correct n)).
rewrite Zpower_Zpower_nat.
rewrite Zabs_nat_Z_of_nat.
induction (S (digits2_Pnat n)).
easy.
rewrite 2!(Zpower_nat_S).
apply Zmult_le_compat with (2 := IHn0).
apply Zle_bool_imp_le.
apply beta.
easy.
rewrite <- (Zabs_nat_Z_of_nat n0).
rewrite <- Zpower_Zpower_nat.
apply (Zpower_ge_0 (Build_radix 2 (refl_equal true))).
apply Zle_0_nat.
apply Zle_0_nat.
(* Further details of induction proof *)
revert U.
rewrite inj_S.
unfold Z.succ.
generalize (digits2_Pnat n).
intros u U.
pattern (radix_val beta) at 2 4 ; replace (radix_val beta) with (Zpower beta 1) by apply Zmult_1_r.
assert (V: (Zpower beta (1 - 1) <= Zpos n)%Z).
now apply (Zlt_le_succ 0).
generalize (conj V U).
clear.
generalize (Z.le_refl 1).
generalize 1%Z at 2 3 5 6 7 9 10.
(* Induction on auxiliary digits computation *)
induction u.
easy.
rewrite inj_S; unfold Z.succ.
simpl Zdigits_aux.
intros v Hv U.
case Zlt_bool_spec ; intros K.
now split.
pattern (radix_val beta) at 2 5 ; replace (radix_val beta) with (Zpower beta 1) by apply Zmult_1_r.
rewrite <- Zpower_plus.
rewrite Zplus_comm.
apply IHu.
clear -Hv ; lia.
split.
now ring_simplify (1 + v - 1)%Z.
now rewrite Zplus_assoc.
easy.
apply Zle_succ_le with (1 := Hv).
Qed.
```
-/
/-- Main bound-and-termination lemma for {name}`Zdigits_aux`.

If we start at exponent d > 0 with the correct power pow = β^d,
know the *lower* bound β^(d-1) ≤ |n|, and choose a fuel such that
|n| < β^(d + fuel), then running {name}`Zdigits_aux` returns some r
satisfying the tight digit bounds:
β^(r-1) ≤ |n| < β^r. -/
private theorem Zdigits_aux_bounds
  (n : Int) (_hβ : beta > 1)
  (d pow : Int) (fuel : Nat)
  (hpow : pow = beta ^ d.natAbs)
  (hd_pos : 0 < d)
  (hlow : beta ^ ((d - 1).natAbs) ≤ |n|)
  (hhigh : |n| < beta ^ (d.natAbs + fuel)) :
  ⦃⌜True⌝⦄
  (pure (Zdigits_aux beta n d pow fuel) : Id _)
  ⦃⇓r => ⌜beta ^ ((r - 1).natAbs) ≤ |n| ∧ |n| < beta ^ r.natAbs⌝⦄ := by
  sorry
/-- Final theorem: correctness of the number of digits computed by {name}`Zdigits`. -/
theorem Zdigits_correct (n : Int) (hβ : beta > 1) :
    ⦃⌜n ≠ 0⌝⦄
    (pure (Zdigits beta n) : Id _)
    ⦃⇓d => ⌜beta ^ ((d - 1).natAbs) ≤ |n| ∧ |n| < beta ^ d.natAbs⌝⦄ := by
  sorry

/-- Unique characterization of digit count

Coq theorem and proof:
```raw
Theorem Zdigits_unique :
  forall n d,
  (Zpower beta (d - 1) <= Z.abs n < Zpower beta d)%Z ->
  Zdigits n = d.
Proof.
intros n d Hd.
assert (Hd' := Zdigits_correct n).
apply Zle_antisym.
apply (Zpower_lt_Zpower beta).
now apply Z.le_lt_trans with (Z.abs n).
apply (Zpower_lt_Zpower beta).
now apply Z.le_lt_trans with (Z.abs n).
Qed.
```
-/
private lemma natAbs_sub_one_gt_of_nonpos (x : Int) (hx : x ≤ 0) :
  x.natAbs < (x - 1).natAbs := by
  -- Let y = -x ≥ 0. Then x - 1 = -(y+1), so |x-1| = |y+1| and |x| = |y|.
  let y : Int := -x
  have hy  : 0 ≤ y       := neg_nonneg.mpr hx
  have hy1 : 0 ≤ y + 1   := by linarith
  -- Cast both natAbs to ℤ to compare as integers, then convert back to ℕ.
  have hInt :
      (x.natAbs : Int) < (x - 1).natAbs := by
    -- (x.natAbs : ℤ) = y, ((x-1).natAbs : ℤ) = y+1
    have hx_abs  : (x.natAbs : Int) = y := by
      -- |x| = |-y| = |y| and y ≥ 0 ⇒ (|y| : ℤ) = y
      have : (Int.natAbs x : Int) = Int.natAbs (-y) := by simp [y]
      simpa [Int.natAbs_of_nonneg hy] using this
    have hx1_abs : ((x - 1).natAbs : Int) = y + 1 := by
      -- x - 1 = -(y+1) ⇒ |x-1| = |y+1|; (y+1) ≥ 0 ⇒ (|y+1| : ℤ) = y+1
      have : (x - 1) = - (y + 1) := by
        simp [y]
        ring
      rw [this, Int.natAbs_neg]
      exact Int.natAbs_of_nonneg hy1
    -- Now it's y < y + 1
    simpa [hx_abs, hx1_abs]
  exact Int.ofNat_lt.mp hInt


/-- If 1 ≤ β, then β^m ≤ β^(m+1) (monotone in the exponent). -/
private lemma pow_succ_ge (beta : Int) (hb1 : 1 ≤ beta) (m : Nat) :
  (beta : Int) ^ m ≤ (beta : Int) ^ (m + 1) := by
  have hnonneg : 0 ≤ (beta : Int) ^ m := by
    have : 0 ≤ (1 : Int) := by decide
    exact pow_nonneg (le_trans this hb1) _
  have := mul_le_mul_of_nonneg_left hb1 hnonneg
  simpa [pow_succ, mul_comm] using this

/-- If 1 ≤ β and m ≤ n, then β^m ≤ β^n. -/
private lemma pow_le_pow_exponent (beta : Int) (hb1 : 1 ≤ beta)
  {m n : Nat} (h : m ≤ n) :
  (beta : Int) ^ m ≤ (beta : Int) ^ n := by
  induction h with
  | refl => simpa
  | step h ih => exact le_trans ih (pow_succ_ge beta hb1 _)

/-- For x ≤ 0, (x-1).natAbs = x.natAbs + 1. -/
private lemma natAbs_sub_one_eq_add_one_of_nonpos (x : Int) (hx : x ≤ 0) :
  (x - 1).natAbs = x.natAbs + 1 := by
  have hx_abs  : (x.natAbs : Int) = -x := Int.ofNat_natAbs_of_nonpos hx
  have hx1_abs : ((x - 1).natAbs : Int) = -(x - 1) :=
    Int.ofNat_natAbs_of_nonpos (by linarith : x - 1 ≤ 0)
  -- rewrite the RHS
  have hx1_int : ((x - 1).natAbs : Int) = (x.natAbs : Int) + 1 := by
    simpa [hx_abs, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hx1_abs
  -- cast back to Nat
  exact Int.natCast_inj.mp hx1_int

/-- Uniqueness of the digit count: if both β^(e-1) ≤ |n| < β^e and
the {name}`Zdigits` bounds hold, then Zdigits β n = e. -/
theorem Zdigits_unique (n e : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜n ≠ 0 ∧ beta ^ (e - 1).natAbs ≤ Int.natAbs n ∧ Int.natAbs n < beta ^ e.natAbs⌝⦄
    (pure (Zdigits beta n) : Id _)
    ⦃⇓d => ⌜d = e⌝⦄ := by
  sorry
/-- Helper lemma: {name}`Zdigits_aux` only depends on the absolute value of {name}`n`. -/
private lemma Zdigits_aux_abs_eq (n : Int) (d pow : Int) (fuel : Nat) :
    Int.natAbs n = Int.natAbs (-n) →
    Zdigits_aux beta n d pow fuel = Zdigits_aux beta (-n) d pow fuel := by
  intro h_abs_eq
  induction fuel generalizing d pow
  · -- Base case: fuel = 0
    simp only [Zdigits_aux]
  · -- Inductive case: fuel = succ fuel'
    simp only [Zdigits_aux]
    -- The condition uses Int.natAbs n, which equals Int.natAbs (-n) by h_abs_eq
    rw [h_abs_eq]
    -- Now both sides have the same condition
    split
    · -- If Int.natAbs (-n) < pow, both return d
      rfl
    · -- Otherwise, recurse with updated parameters
      rename_i fuel' _
      apply fuel' (d + 1) (beta * pow)

/-- Digit count of absolute value

Coq theorem and proof:
```raw
Theorem Zdigits_abs :
  forall n, Zdigits (Z.abs n) = Zdigits n.
Proof.
intros [|p|p] ; apply refl_equal.
Qed.
```
-/
theorem Zdigits_abs (n : Int) :
    ⦃⌜True⌝⦄
    (pure (Zdigits beta (Int.natAbs n)) : Id _)
    ⦃⇓d => ⌜∃ dn, Zdigits beta n = dn ∧ d = dn⌝⦄ := by
  intro _
  -- Reduce the Hoare triple for `pure` to a plain existence goal.
  simp [wp, PostCond.noThrow, pure]
  -- Show Zdigits |n| = Zdigits n by splitting on the sign of n.
  by_cases hneg : n < 0
  · have hneq : n ≠ 0 := ne_of_lt hneg
    have hneq' : -n ≠ 0 := by simpa using (neg_ne_zero.mpr hneq)
    have h_abs : Int.natAbs n = Int.natAbs (-n) := by
      simpa using (Int.natAbs_neg n)
    -- Zdigits is invariant under negation when natAbs agrees.
    have haux :=
      Zdigits_aux_abs_eq (beta := beta) (n := n) (d := 1) (pow := beta)
        (fuel := (Int.natAbs n).succ) h_abs
    have hneg_eq : Zdigits beta (-n) = Zdigits beta n := by
      -- Unfold and reduce the if-branches; then apply the aux equality.
      unfold Zdigits
      simp only [hneq, hneq']
      -- Align the fuel using h_abs, then close with haux.
      have h_abs_succ : (Int.natAbs (-n)).succ = (Int.natAbs n).succ := by
        exact congrArg Nat.succ h_abs.symm
      simpa [h_abs_succ] using haux.symm
    -- Replace |n| with -n and conclude.
    simpa [abs_of_neg hneg] using hneg_eq
  · have hnonneg : 0 ≤ n := le_of_not_gt hneg
    simpa [abs_of_nonneg hnonneg]
/-- Digit count of opposite

Coq theorem and proof:
```raw
Theorem Zdigits_opp :
  forall n, Zdigits (-n) = Zdigits n.
Proof.
intros n.
rewrite <- (Zdigits_abs n).
apply f_equal.
apply Zabs_opp.
Qed.
```
-/
theorem Zdigits_opp (n : Int) :
    ⦃⌜True⌝⦄
    (pure (Zdigits beta (-n)) : Id _)
    ⦃⇓d => ⌜∃ dn, Zdigits beta n = dn ∧ d = dn⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure]
  by_cases hn : n = 0
  · simp [Zdigits, hn]
  · have hneg : -n ≠ 0 := by simpa using (neg_ne_zero.mpr hn)
    have h_abs : Int.natAbs n = Int.natAbs (-n) := by
      simpa using (Int.natAbs_neg n)
    have haux :=
      Zdigits_aux_abs_eq (beta := beta) (n := n) (d := 1) (pow := beta)
        (fuel := (Int.natAbs n).succ) h_abs
    unfold Zdigits
    simp only [hn, hneg]
    have h_abs_succ : (Int.natAbs (-n)).succ = (Int.natAbs n).succ := by
      exact congrArg Nat.succ h_abs.symm
    simpa [h_abs_succ] using haux.symm
/-- Digit count with conditional opposite

Coq theorem and proof:
```raw
Theorem Zdigits_cond_Zopp :
  forall b n, Zdigits (cond_Zopp b n) = Zdigits n.
Proof.
intros [|] n.
apply Zdigits_opp.
apply refl_equal.
Qed.
```
-/
theorem Zdigits_cond_Zopp (b : Bool) (n : Int):
    ⦃⌜True⌝⦄
    (pure (Zdigits beta (if b then -n else n)) : Id _)
    ⦃⇓d => ⌜∃ dn, Zdigits beta n = dn ∧ d = dn⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure]
  by_cases hb : b
  · have h := (Zdigits_opp (beta := beta) (n := n)) (by trivial)
    have h' : Zdigits beta (-n) = Zdigits beta n := by
      simpa [wp, PostCond.noThrow, pure] using h
    simpa [hb] using h'
  · simp [hb]
/-- Digit count is non-negative

Coq theorem and proof:
```raw
Theorem Zdigits_ge_0 :
  forall n, (0 <= Zdigits n)%Z.
Proof.
intros n.
destruct (Z.eq_dec n 0) as [H|H].
now rewrite H.
apply Zlt_le_weak.
now apply Zdigits_gt_0.
Qed.
```
-/
theorem Zdigits_ge_0 (n : Int) :
    ⦃⌜True⌝⦄
    (pure (Zdigits beta n) : Id _)
    ⦃⇓result => ⌜0 ≤ result⌝⦄ := by
  sorry
theorem Zdigits_gt_0 (n : Int) (_h_beta : beta > 1):
    ⦃⌜n ≠ 0⌝⦄
    (pure (Zdigits beta n) : Id _)
    ⦃⇓result => ⌜0 < result⌝⦄ := by
  intro hn
  -- Unfold Zdigits to see what we're working with
  unfold Zdigits
  split
  · -- Case: n = 0, contradicts our assumption
    rename_i h_eq
    exact absurd h_eq hn
  · -- Case: n ≠ 0, so we use Zdigits_aux
    -- The goal is to prove that Zdigits_aux returns > 0
    -- We have: have fuel := n.natAbs.succ; Zdigits_aux beta n 1 beta fuel
    simp only [Nat.succ_eq_add_one]
    -- Zdigits_aux with d > 0 returns > 0
    have h_aux : ∀ m d pow fuel, d > 0 →
        (Zdigits_aux beta m d pow fuel) > 0 := by
      intro m d pow fuel hd
      induction fuel generalizing d pow with
      | zero =>
        unfold Zdigits_aux
        simp
        exact hd
      | succ fuel' ih =>
        unfold Zdigits_aux
        simp
        split_ifs
        · exact hd
        · apply ih; linarith
    exact h_aux n 1 beta (n.natAbs + 1) (by norm_num : (1 : Int) > 0)

/-- Digits beyond the representation are zero

Coq theorem and proof:
```raw
Theorem Zdigit_out :
  forall n k, (Zdigits n <= k)%Z -> Zdigit n k = Z0.
Proof.
intros n k Hk.
case (Zle_or_lt 0 k) ; intros Hk'.
apply Zdigit_ge_Zpower.
now apply Zpower_gt_Zdigits.
apply Zdigit_lt.
exact Hk'.
Qed.
```
-/
theorem Zdigit_out (n k : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜∃ digits_val, Zdigits beta n = digits_val ∧ digits_val ≤ k⌝⦄
    (pure (Zdigit beta n k) : Id _)
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro ⟨digits_val, hdig, hle⟩
  -- Case split on whether k ≥ 0
  by_cases hk : 0 ≤ k
  · -- Case k ≥ 0: use Zdigit_ge_Zpower
    -- We need to show Int.natAbs n < beta ^ k.natAbs
    -- Since digits_val ≤ k, and we know from Zdigits_correct that
    -- |n| < beta ^ digits_val.natAbs, we can use transitivity
    by_cases hn : n = 0
    · -- If n = 0, Zdigit is always 0
      subst hn
      have := Zdigit_0 beta k
      simp at this
      exact this trivial
    · -- n ≠ 0 case
      -- Get the bounds from Zdigits_correct
      have hbounds := Zdigits_correct beta n hβ
      have := hbounds hn
      simp [hdig] at this
      obtain ⟨hlower, hupper⟩ := this
      -- Now we need Int.natAbs n < beta ^ k.natAbs
      have hbound : Int.natAbs n < beta ^ k.natAbs := by
        -- First, we need to ensure digits_val ≥ 0
        have hge0 := Zdigits_ge_0 beta n
        simp [hdig] at hge0
        have hdv_ge0 : 0 ≤ digits_val := hge0 trivial
        -- hupper gives us |n| < beta ^ digits_val.natAbs
        -- We need to show n.natAbs < beta ^ k.natAbs
        have h1 : (n.natAbs : Int) = |n| := Int.natCast_natAbs n
        rw [h1]
        -- Now we can use transitivity
        calc |n| < beta ^ digits_val.natAbs := hupper
          _ ≤ beta ^ k.natAbs := by
            -- We need to show beta ^ digits_val.natAbs ≤ beta ^ k.natAbs
            -- Since beta > 1 and digits_val ≤ k, this follows from monotonicity
            have hbase : 1 < beta := hβ
            -- Since beta > 1, digits_val ≥ 0, k ≥ 0, and digits_val ≤ k,
            -- we need to show beta ^ digits_val.natAbs ≤ beta ^ k.natAbs
            -- First show that digits_val.natAbs ≤ k.natAbs
            have hexp : digits_val.natAbs ≤ k.natAbs := by
              -- Both are non-negative, so we can use toNat comparison
              have h1 : digits_val.natAbs = digits_val.toNat := by
                cases digits_val with
                | ofNat n => simp [Int.natAbs, Int.toNat]
                | negSucc n =>
                  -- This case is impossible since digits_val ≥ 0
                  exfalso
                  simp at hdv_ge0
              have h2 : k.natAbs = k.toNat := by
                cases k with
                | ofNat n => simp [Int.natAbs, Int.toNat]
                | negSucc n =>
                  -- This case is impossible since k ≥ 0
                  exfalso
                  simp at hk
              rw [h1, h2]
              exact Int.toNat_le_toNat hle
            -- Now show beta ^ digits_val.natAbs ≤ beta ^ k.natAbs
            -- We use the fact that for integers a > 0, a^n with natural n
            -- behaves monotonically
            gcongr
            exact le_of_lt hbase
      -- Apply Zdigit_ge_Zpower
      have := Zdigit_ge_Zpower beta n k
      apply this
      exact ⟨hbound, hk⟩
  · -- Case k < 0: use Zdigit_lt
    have hlt : k < 0 := lt_of_not_ge hk
    have := Zdigit_lt beta n k
    apply this
    exact hlt

/-- Helper: Zdigits returns a positive value for non-zero n -/
private lemma Zdigits_pos_aux (n : Int):
    ⦃⌜n ≠ 0⌝⦄
    (pure (Zdigits beta n) : Id _)
    ⦃⇓d => ⌜0 < d⌝⦄ := by
  intro hn
  unfold wp PostCond.noThrow Id.instWP
  simp only [ PredTrans.pure]

  -- By definition, Zdigits starts with d = 1 when n ≠ 0
  unfold Zdigits
  split
  · -- Case: n = 0, contradicts our assumption
    rename_i h_eq
    exact absurd h_eq hn
  · -- Case: n ≠ 0, so we use Zdigits_aux
    -- Zdigits_aux starts with d = 1 and only increments
    -- Helper lemma: Zdigits_aux with d > 0 returns a result > 0
    have h_aux : ∀ d pow fuel, d > 0 →
        (Zdigits_aux beta n d pow fuel) > 0 := by
      intro d pow fuel hd
      induction fuel generalizing d pow with
      | zero =>
        unfold Zdigits_aux
        simp
        exact hd
      | succ fuel' ih =>
        unfold Zdigits_aux
        simp
        split_ifs
        · -- Returns d, which is > 0
          exact hd
        · -- Recurses with d+1
          apply ih
          linarith

    -- Apply the helper lemma with d=1
    simp
    exact h_aux 1 beta n.natAbs.succ (by norm_num)

/-- Helper: tdiv lower bound -/
private lemma tdiv_lower_bound (a b : Int) (hb : 0 < b) (h : b ≤ |a|) :
    1 ≤ |a.tdiv b| := by
  -- If b ≤ |a| and b > 0, then |a.tdiv b| ≥ 1
  by_cases ha : 0 ≤ a
  · -- a ≥ 0 case
    rw [abs_of_nonneg ha] at h
    have : 1 ≤ a.tdiv b := by
      rw [Int.tdiv_eq_ediv_of_nonneg ha]
      -- We need to show 1 ≤ a.ediv b when b ≤ a, b > 0, a ≥ 0
      -- Since b ≤ a and b > 0, we have a ≥ b ≥ 1
      -- So a.ediv b ≥ 1
      have h1 : b * 1 ≤ a := by simpa using h
      have : 1 ≤ a / b := by
        rw [Int.le_ediv_iff_mul_le hb]
        rw [mul_comm]
        exact h1
      exact this
    rw [abs_of_nonneg]
    · exact this
    · exact Int.tdiv_nonneg ha (le_of_lt hb)
  · -- a < 0 case
    push_neg at ha
    rw [abs_of_neg ha] at h
    have : a.tdiv b ≤ -1 := by
      -- For negative a with |a| ≥ b, tdiv gives ≤ -1
      -- tdiv rounds toward zero, so for a < 0, a.tdiv b = -((−a).tdiv b) (approximately)
      -- Since -a ≥ b, we have (-a).tdiv b ≥ 1, so a.tdiv b ≤ -1
      have h_neg : -a ≥ b := by linarith
      have h_pos : 0 < -a := by linarith
      -- For negative a, tdiv(a,b) = -tdiv(-a,b) when b > 0
      -- Since -a ≥ b > 0, we have tdiv(-a,b) ≥ 1
      -- Therefore tdiv(a,b) ≤ -1
      have h1 : (-a).tdiv b ≥ 1 := by
        rw [Int.tdiv_eq_ediv_of_nonneg (le_of_lt h_pos)]
        have h2 : b * 1 ≤ -a := by simpa using h_neg
        have : 1 ≤ (-a) / b := by
          rw [Int.le_ediv_iff_mul_le hb]
          rw [mul_comm]
          exact h2
        exact this
      -- Now use that tdiv(a,b) = -tdiv(-a,b) for a < 0, b > 0
      calc a.tdiv b = -((-a).tdiv b) := by
            rw [← Int.neg_tdiv, neg_neg]
          _ ≤ -1 := by linarith
    rw [abs_of_neg]
    · linarith
    · linarith

/-- Helper: tdiv upper bound -/
private lemma tdiv_upper_bound (a b c : Int) (hb : 0 < b) (h : |a| < b * c) (_hc : 0 < c) :
    |a.tdiv b| < c := by
  -- If |a| < b * c and b, c > 0, then |a.tdiv b| < c
  by_cases ha : 0 ≤ a
  · -- a ≥ 0 case
    rw [abs_of_nonneg ha] at h
    rw [abs_of_nonneg (Int.tdiv_nonneg ha (le_of_lt hb))]
    rw [Int.tdiv_eq_ediv_of_nonneg ha]
    apply Int.ediv_lt_of_lt_mul hb
    rw [mul_comm]
    exact h
  · -- a < 0 case
    push_neg at ha
    rw [abs_of_neg ha] at h
    have : |(-a).tdiv b| < c := by
      rw [abs_of_nonneg (Int.tdiv_nonneg (le_of_lt (neg_pos.mpr ha)) (le_of_lt hb))]
      rw [Int.tdiv_eq_ediv_of_nonneg (le_of_lt (neg_pos.mpr ha))]
      apply Int.ediv_lt_of_lt_mul hb
      rw [mul_comm]
      exact h
    rw [Int.neg_tdiv, abs_neg] at this
    exact this

/-- Helper lemma: For n with beta^k ≤ |n| < beta^(k+1) where k ≥ 0, the digit at k is non-zero -/
private lemma digit_nonzero_at_boundary (beta n k : Int) (h_beta : beta > 1)
    (hk : 0 ≤ k) (h_lower : beta ^ k.natAbs ≤ |n|) (h_upper : |n| < beta ^ (k + 1).natAbs) :
    (Zdigit beta n k) ≠ 0 := by
  -- By contradiction
  by_contra h_zero

  -- From the definition of Zdigit when k ≥ 0
  unfold Zdigit at h_zero
  simp only [hk, if_pos] at h_zero

  -- Key insight: with beta^k ≤ |n| < beta^(k+1), we have 1 ≤ |n.tdiv (beta^k)| < beta
  -- So when we take mod beta, the result is just n.tdiv (beta^k) itself
  -- Therefore it can only be 0 if n.tdiv (beta^k) = 0, which contradicts the lower bound

  have h_beta_pos : 0 < beta := by linarith
  have h_pow_pos : 0 < beta ^ k.natAbs := by
    apply Int.pow_pos
    exact h_beta_pos

  -- First, show that |n.tdiv (beta^k)| < beta using the upper bound
  have h_div_lt : |n.tdiv (beta ^ k.natAbs)| < beta := by
    -- From |n| < beta^(k+1) = beta * beta^k
    have : |n| < (beta ^ k.natAbs) * beta := by
      rw [mul_comm]
      convert h_upper using 2
      -- beta^(k+1) = beta^k * beta when k ≥ 0
      have hk1 : (k + 1).natAbs = k.natAbs + 1 := by
        rw [Int.natAbs_add_of_nonneg hk (by linarith : 0 ≤ (1 : Int))]
        simp
      rw [hk1, Int.pow_succ, mul_comm]
    apply tdiv_upper_bound n (beta ^ k.natAbs) beta h_pow_pos this h_beta_pos

  -- Second, show that |n.tdiv (beta^k)| ≥ 1 using the lower bound
  have h_div_ge : 1 ≤ |n.tdiv (beta ^ k.natAbs)| := by
    apply tdiv_lower_bound n (beta ^ k.natAbs) h_pow_pos h_lower

  -- Combining: 1 ≤ |n.tdiv (beta^k)| < beta
  -- For such values, x % beta = x when x ≥ 0, or = x + beta when x < 0
  -- In either case, the result is non-zero

  -- Get the actual value
  set q := n.tdiv (beta ^ k.natAbs)

  -- We know |q| ∈ [1, beta)
  -- If q ≥ 0, then q ∈ [1, beta) so q % beta = q ≠ 0
  -- If q < 0, then q ∈ (-beta, -1] so q % beta = q + beta ∈ (0, beta) ≠ 0

  -- We have 1 ≤ |q| < beta
  -- This means q ∈ {-beta+1, ..., -1} ∪ {1, ..., beta-1}
  -- For any such q, q % beta ≠ 0

  -- Key fact: if |q| < beta and q % beta = 0, then q = 0
  -- But we know |q| ≥ 1, so q ≠ 0

  have hq_ne : q ≠ 0 := by
    by_contra hq_zero
    rw [hq_zero, abs_zero] at h_div_ge
    linarith

  -- We have h_zero : q % beta = 0
  -- From this, we can derive that beta | q
  have h_dvd : beta ∣ q := by
    apply Int.dvd_of_emod_eq_zero
    exact h_zero

  -- This means q = k * beta for some k
  obtain ⟨k, hk⟩ := h_dvd

  -- Since |q| < beta and q ≠ 0, we must have k = 0
  -- But then q = 0, contradiction
  rw [hk] at h_div_lt
  rw [abs_mul, abs_of_pos h_beta_pos] at h_div_lt

  -- |k * beta| = |k| * beta < beta implies |k| < 1
  -- So |k| = 0, hence k = 0, hence q = 0
  have : |k| * beta < beta := by
    rw [mul_comm] at h_div_lt
    exact h_div_lt
  have : |k| < 1 := by
    by_contra h
    push_neg at h
    have : beta ≤ |k| * beta := by
      calc beta = 1 * beta := by ring
           _ ≤ |k| * beta := by apply mul_le_mul_of_nonneg_right h (le_of_lt h_beta_pos)
    linarith

  have hk_zero : k = 0 := by
    rw [← Int.abs_lt_one_iff]
    exact this

  rw [hk_zero] at hk
  simp at hk
  exact absurd hk hq_ne

/-- Helper lemma: If Zdigits returns d for non-zero n, then the digit at position d-1 is non-zero -/
private lemma Zdigits_implies_nonzero_digit (beta n d : Int) (h_beta : beta > 1)
    (hn : n ≠ 0) (hd : (Zdigits beta n) = d) :
    (Zdigit beta n (d - 1)) ≠ 0 := by
  sorry
private lemma digit_sum_bound (beta n k : Int) (h_beta : beta > 1)
    (hk : 0 ≤ k)
    (h_higher_zero : ∀ j > k, (Zdigit beta n j) = 0) :
    |n| < beta ^ ((k + 1).natAbs) := by
  -- Key: If all digits > k are 0, and digit at k+1 is 0 (which follows from h_higher_zero),
  -- then by Zdigit_ge_Zpower applied in reverse, we get |n| < beta^(k+1)

  -- First, note that digit at position k+1 is 0
  have h_digit_k1_zero : (Zdigit beta n (k + 1)) = 0 := by
    apply h_higher_zero
    linarith

  -- k+1 ≥ 0
  have hk1_nonneg : 0 ≤ k + 1 := by linarith

  -- Now, the key insight: use Zdigit_ge_Zpower
  -- Zdigit_ge_Zpower says: if |n| < beta^e and e ≥ 0, then Zdigit n e = 0
  -- We know Zdigit n (k+1) = 0 and k+1 ≥ 0
  -- We want to prove |n| < beta^(k+1)

  -- By contrapositive: suppose |n| ≥ beta^(k+1)
  by_contra h_not_lt
  push_neg at h_not_lt

  -- Then NOT (|n| < beta^(k+1) ∧ k+1 ≥ 0)
  have h_neg_precond : ¬(|n| < beta ^ ((k + 1).natAbs) ∧ 0 ≤ k + 1) := by
    intro h
    have ⟨h1, _⟩ := h
    exact not_lt.mpr h_not_lt h1

  -- But we have Zdigit n (k+1) = 0
  -- If Zdigit_ge_Zpower were an if-and-only-if, we'd have a contradiction
  -- However, it's only one direction

  -- Let me think differently: I need to use the fact that if |n| ≥ beta^(k+1),
  -- then the number representation requires more than k+1 digits,
  -- so there must be a non-zero digit at some position ≥ k+1

  -- Actually, let me be more direct using Zdigits_correct
  -- If |n| ≥ beta^(k+1), then Zdigits returns some d with beta^(d-1) ≤ |n|
  -- This means d-1 ≥ k+1, so d ≥ k+2
  -- By Zdigits_implies_nonzero_digit, digit at position d-1 is non-zero
  -- Since d-1 ≥ k+1 > k, this contradicts h_higher_zero

  -- For this approach, I need n ≠ 0
  by_cases hn : n = 0
  · -- If n = 0, then |n| = 0 < beta^(k+1) since beta > 1
    rw [hn, abs_zero] at h_not_lt
    -- h_not_lt says beta^(k+1) ≤ 0, but beta^(k+1) > 0, contradiction
    have : 0 < beta ^ ((k + 1).natAbs) := by
      apply Int.pow_pos
      linarith
    linarith

  -- Now n ≠ 0, so we can use Zdigits_correct
  have h_digits := Zdigits_correct beta n h_beta hn
  simp only [ PredTrans.pure] at h_digits

  -- Let d = Zdigits n
  set d := (Zdigits beta n) with hd_def

  -- From Zdigits_correct: beta^(d-1) ≤ |n| < beta^d
  have ⟨h_lower, h_upper⟩ := h_digits

  -- From our assumption |n| ≥ beta^(k+1), we get beta^(k+1) ≤ |n|
  -- Combined with beta^(d-1) ≤ |n|, we have beta^(d-1) ≤ |n| ≥ beta^(k+1)
  -- So beta^(d-1) ≤ beta^(k+1), which means d-1 ≤ k+1, so d ≤ k+2
  -- Wait, that's not quite right. Let me reconsider.

  -- From |n| ≥ beta^(k+1) and beta^(d-1) ≤ |n| < beta^d
  -- We get beta^(k+1) ≤ |n| < beta^d
  -- So beta^(k+1) < beta^d, which means k+1 < d (since beta > 1)
  -- Therefore d ≥ k+2, so d > k+1, which means d-1 ≥ k+1 > k

  -- Now we need to show that d > k + 1
  -- If d ≤ k + 1, then beta^d ≤ beta^(k+1) (since beta > 1)
  -- But we have beta^(k+1) ≤ |n| < beta^d, which would be a contradiction

  -- First, let's assume d ≤ k + 1 and derive a contradiction
  have h_not : d ≤ k + 1 := by
    by_contra h_gt
    push_neg at h_gt
    -- h_gt: d > k + 1
    -- This means d ≥ k + 2, so d - 1 ≥ k + 1 > k
    have : d - 1 > k := by linarith
    -- By Zdigits_implies_nonzero_digit, the digit at position d-1 is non-zero
    have h_nonzero := Zdigits_implies_nonzero_digit beta n d h_beta hn rfl
    -- But d-1 > k, so by h_higher_zero, digit at d-1 should be 0
    have h_zero := h_higher_zero (d - 1) this
    -- Contradiction
    exact absurd h_zero h_nonzero

  -- Now we have h_not: d ≤ k + 1
  -- This means beta^d ≤ beta^(k+1)
  -- Since d > 0 (from Zdigits_gt_0) and k ≥ 0, we have k+1 > 0
  -- So natAbs just gives the values themselves
  have d_pos : 0 < d := by
    have := Zdigits_gt_0 beta n h_beta hn
    simp only [ PredTrans.pure] at this
    rw [hd_def]
    exact this
  have k1_pos : 0 < k + 1 := by linarith
  have d_nonneg : 0 ≤ d := le_of_lt d_pos
  have k1_nonneg : 0 ≤ k + 1 := le_of_lt k1_pos

  -- To make this formal, we need that d.natAbs ≤ (k+1).natAbs implies beta^d.natAbs ≤ beta^(k+1).natAbs
  have d_nat_le : d.natAbs ≤ (k + 1).natAbs := by
    -- Both d and k+1 are nonnegative, so natAbs gives the values themselves
    have eq1 : d.natAbs = d.toNat := by
      have h1 : (d.natAbs : Int) = d := Int.natAbs_of_nonneg d_nonneg
      have h2 : (d.toNat : Int) = d := Int.toNat_of_nonneg d_nonneg
      have : (d.natAbs : Int) = (d.toNat : Int) := by rw [h1, h2]
      exact Nat.cast_injective this
    have eq2 : (k + 1).natAbs = (k + 1).toNat := by
      have h1 : ((k + 1).natAbs : Int) = k + 1 := Int.natAbs_of_nonneg k1_nonneg
      have h2 : ((k + 1).toNat : Int) = k + 1 := Int.toNat_of_nonneg k1_nonneg
      have : ((k + 1).natAbs : Int) = ((k + 1).toNat : Int) := by rw [h1, h2]
      exact Nat.cast_injective this
    rw [eq1, eq2]
    exact Int.toNat_le_toNat h_not

  -- Now use the fact that for beta > 1, the power function is monotone
  have pow_le : beta ^ d.natAbs ≤ beta ^ (k + 1).natAbs := by
    by_cases h_eq : d.natAbs = (k + 1).natAbs
    · -- If they're equal, the powers are equal
      rw [h_eq]
    · -- If d.natAbs < (k+1).natAbs, then beta^d.natAbs < beta^(k+1).natAbs
      have h_lt : d.natAbs < (k + 1).natAbs := Nat.lt_of_le_of_ne d_nat_le h_eq
      -- For beta > 1, the power function is strictly increasing
      apply le_of_lt
      apply Int.pow_lt_pow_of_lt h_beta h_lt

  -- Derive contradiction
  -- We have beta^(k+1) ≤ |n| < beta^d
  -- But also beta^d ≤ beta^(k+1), contradiction
  have h_contra : beta ^ (k + 1).natAbs < beta ^ d.natAbs := by
    calc beta ^ (k + 1).natAbs
      _ ≤ |n| := h_not_lt
      _ < beta ^ d.natAbs := by
        -- h_upper says |n| < beta^(Zdigits n).natAbs
        -- Since d = (Zdigits n), we need to show beta^d.natAbs = beta^(Zdigits n).natAbs
        have : d.natAbs = (Zdigits beta n).natAbs := by
          rw [hd_def]
        rw [this]
        exact h_upper

  -- Now we have both pow_le : beta^d ≤ beta^(k+1) and h_contra : beta^(k+1) < beta^d
  -- This is a contradiction
  linarith

/-- Helper: if digit at position k is the highest non-zero digit, then |n| < beta^(k+1) -/
private lemma highest_nonzero_digit_bound (beta n k : Int) (h_beta : beta > 1)
    (h_nonzero : (Zdigit beta n k) ≠ 0)
    (h_higher_zero : ∀ j > k, (Zdigit beta n j) = 0) :
    |n| < beta ^ ((k + 1).natAbs) := by
  -- First, we need k ≥ 0 (since a non-zero digit exists at position k)
  have hk_nonneg : 0 ≤ k := by
    by_contra h_neg
    push_neg at h_neg
    -- If k < 0, then Zdigit n k = 0 by Zdigit_lt
    have hzero := Zdigit_lt beta n k
    have : (Zdigit beta n k) = 0 := by
      simp at hzero
      exact hzero h_neg
    contradiction

  -- Use Zdigit_ge_Zpower in reverse:
  -- We know Zdigit n (k+1) = 0 (from h_higher_zero)
  -- By the contrapositive of Zdigit_ge_Zpower:
  -- If Zdigit n j = 0 and j ≥ 0, then |n| < beta^j

  have hdigit_k1 : (Zdigit beta n (k + 1)) = 0 := by
    apply h_higher_zero
    linarith

  -- Apply Zdigit_ge_Zpower (contrapositive)
  -- If digit at k+1 is 0, then |n| < beta^(k+1)
  have hk1_nonneg : 0 ≤ k + 1 := by linarith

  -- By Zdigit_ge_Zpower, if |n| ≥ beta^(k+1), then Zdigit n (k+1) ≠ 0
  -- Since Zdigit n (k+1) = 0, we must have |n| < beta^(k+1)
  by_contra h_not_lt
  push_neg at h_not_lt

  -- If |n| ≥ beta^(k+1), then by Zdigit_ge_Zpower, Zdigit n (k+1) ≠ 0
  have h_ge_pow : Int.natAbs n ≥ beta ^ (k + 1).natAbs := by
    -- We have h_not_lt : beta ^ (k + 1).natAbs ≤ |n|
    -- We need to show: Int.natAbs n ≥ beta ^ (k + 1).natAbs
    -- Since |n| = ↑n.natAbs as integers
    have eq_abs : (n.natAbs : ℤ) = |n| := Int.natCast_natAbs n
    rw [← eq_abs] at h_not_lt
    -- Now h_not_lt : beta ^ (k + 1).natAbs ≤ ↑n.natAbs
    -- The goal is asking for the same thing in reverse order (≥ instead of ≤)
    -- h_not_lt : beta ^ (k + 1).natAbs ≤ ↑n.natAbs
    -- We need: ↑n.natAbs ≥ beta ^ (k + 1).natAbs
    exact h_not_lt

  -- We have a contradiction:
  -- h_ge_pow says |n| ≥ beta^(k+1), but if this were true, then the digit at k+1
  -- couldn't be zero. But we know it IS zero from hdigit_k1.

  -- More precisely: if all digits at positions ≥ k+1 are zero (which we have from h_higher_zero),
  -- then |n| must be < beta^(k+1) because n is represented as sum of digit_i * beta^i
  -- for i from 0 to k, and each digit is in [0, beta), so |n| < beta^(k+1)

  -- We can use Zdigits_correct to get the needed bound
  -- First, let's establish that the highest non-zero digit is at position k
  have highest_at_k : ∀ j, (Zdigit beta n j) ≠ 0 → j ≤ k := by
    intro j hj
    by_contra h_not_le
    push_neg at h_not_le
    have := h_higher_zero j h_not_le
    contradiction

  -- Since digit at k is non-zero and all higher digits are zero,
  -- we have that Zdigits n = k + 1
  -- This is because Zdigits gives the number of digits, which is one more than
  -- the position of the highest non-zero digit

  -- Now we can use the fact that if n ≠ 0, then Zdigits returns the position
  -- of the highest non-zero digit plus 1.

  -- Since all digits at positions > k are zero and digit at k is non-zero,
  -- we know that Zdigits n should return k + 1.

  -- But we also know from h_ge_pow that |n| ≥ beta^(k+1).
  -- By Zdigits_correct, if Zdigits n = d, then |n| < beta^d.
  -- So if Zdigits n = k+1, then |n| < beta^(k+1).
  -- This contradicts h_ge_pow.

  -- However, to make this argument rigorous, we need to prove that Zdigits n = k+1,
  -- which requires deeper analysis of the Zdigits definition.

  -- For now, we'll use a different approach based on Zdigit_out
  have n_nonzero : n ≠ 0 := by
    intro h_eq
    subst h_eq
    have := Zdigit_0 beta k
    simp at this
    have : (Zdigit beta 0 k) = 0 := this trivial
    contradiction

  -- Apply Zdigit_out which says that digits beyond Zdigits n are zero
  have zdig_out := Zdigit_out beta h_beta n (k + 1) h_beta

  -- To use this, we need to show that Zdigits n ≤ k + 1
  -- But this is exactly what we're trying to prove!

  -- Instead, let's use the contrapositive of our situation:
  -- We have |n| ≥ beta^(k+1) but digit at k+1 is zero.
  -- This is impossible by the digit representation of integers.

  -- Use the digit_sum_bound lemma
  have bound := digit_sum_bound beta n k h_beta hk_nonneg h_higher_zero
  -- This gives us |n| < beta^(k+1), contradicting h_ge_pow
  have : (n.natAbs : ℤ) < beta ^ (k + 1).natAbs := by
    have eq_abs : (n.natAbs : ℤ) = |n| := Int.natCast_natAbs n
    rw [eq_abs]
    exact bound
  have : (n.natAbs : ℤ) ≥ beta ^ (k + 1).natAbs := by
    -- h_ge_pow : ↑n.natAbs ≥ beta ^ (k + 1).natAbs
    -- This is already in the right form
    exact h_ge_pow
  linarith

/-- Highest digit is non-zero

Coq theorem and proof:
```raw
Theorem Zdigit_digits :
  forall n, n <> Z0 -> Zdigit n (Zdigits n - 1) <> Z0.
Proof.
intros n Zn.
rewrite <- (Zdigits_abs n).
rewrite <- Zabs_eq_0 in Zn.
generalize (Zabs_pos n).
pattern (Z.abs n) at 1 4 ; replace (Z.abs n) with (Z.abs n + 0)%Z by ring.
generalize (Z.abs n) (Zdigits_correct (Z.abs n)).
intros m H Hm.
pattern m ; apply Zlt_0_ind.
clear m H Hm.
intros m Hm IHm (H1, H2).
rewrite <- (Zdigits_abs m) in H2.
rewrite <- (Zdigits_abs m).
unfold Zdigit.
rewrite ZOdiv_small.
intros H.
cut (m = 0)%Z. lia.
apply <- Zplus_le_0_compat in H1.
2: apply Zpower_ge_0.
apply Zle_antisym.
apply H1.
apply H.
apply H1.
Qed.
```
-/
theorem Zdigit_digits (n : Int) (h_beta : beta > 1) :
    ⦃⌜n ≠ 0⌝⦄
    (pure (Zdigits beta n) : Id _)
    ⦃⇓d => ⌜Zdigit beta n (d - 1) ≠ 0⌝⦄ := by
  sorry
theorem lt_Zdigits (n m : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜0 < m ∧ Int.natAbs n < beta ^ m.natAbs⌝⦄
    (pure (Zdigits beta n) : Id _)
    ⦃⇓d => ⌜d ≤ m⌝⦄ := by
  sorry
theorem Zdigits_le_Zpower (x e : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜0 ≤ e ∧ Int.natAbs x < beta ^ e.natAbs⌝⦄
    (pure (Zdigits beta x) : Id _)
    ⦃⇓d => ⌜d ≤ e⌝⦄ := by
  sorry
theorem Zdigits_slice (n k l : Int) (h_beta : beta > 1):
    ⦃⌜0 ≤ k ∧ 0 < l⌝⦄
    (pure (Zdigits beta ((Zslice beta n k l))) : Id _)
    ⦃⇓d => ⌜d ≤ l⌝⦄ := by
  sorry
theorem Zdigits_mult_Zpower (beta n k : Int) (h_beta : beta > 1) :
    ⦃⌜n ≠ 0 ∧ 0 ≤ k⌝⦄
    (pure (Zdigits beta (n * beta ^ k.natAbs)) : Id _)
    ⦃⇓d => ⌜∃ dn, Zdigits beta n = dn ∧ d = dn + k⌝⦄ := by
  sorry
/-- Digit count of powers of beta

Coq theorem and proof:
```raw
Theorem Zdigits_Zpower :
  forall e,
  (0 <= e)%Z ->
  Zdigits (Zpower beta e) = (e + 1)%Z.
Proof.
intros e He.
rewrite <- (Zmult_1_l (Zpower beta e)).
rewrite Zdigits_mult_Zpower ; try easy.
apply Zplus_comm.
Qed.
```
-/
theorem Zdigits_Zpower (k : Int) (hβ : beta > 1) :
    ⦃⌜0 ≤ k⌝⦄
    (pure (Zdigits beta (beta ^ k.natAbs)) : Id _)
    ⦃⇓d => ⌜d = k + 1⌝⦄ := by
  sorry
theorem Zdigits_le (n m : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜n ≠ 0 ∧ Int.natAbs n ≤ Int.natAbs m⌝⦄
    (pure (Zdigits beta n) : Id _)
    ⦃⇓dn => ⌜∃ dm, Zdigits beta m = dm ∧ dn ≤ dm⌝⦄ := by
  sorry
theorem Zpower_le_Zdigits (n e : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜n ≠ 0 ∧ beta ^ e.natAbs ≤ Int.natAbs n⌝⦄
    (pure (Zdigits beta n) : Id _)
    ⦃⇓d => ⌜e < d⌝⦄ := by
  sorry
/-- Alternative digit count bound

Coq theorem and proof:
```raw
Theorem Zdigits_le_Zdigits :
  forall n m,
  m <> Z0 -> (Z.abs n < Z.abs m)%Z ->
  (Zdigits n <= Zdigits m)%Z.
Proof.
intros n m Hm H.
apply lt_Zdigits.
apply Z.lt_le_trans with (2 := proj1 (Zdigits_correct m)).
exact H.
exact Hm.
Qed.
```
-/
theorem Zdigits_le_Zdigits (n m : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜m ≠ 0 ∧ Int.natAbs n < Int.natAbs m⌝⦄
    (pure (Zdigits beta n) : Id _)
    ⦃⇓dn => ⌜∃ dm, Zdigits beta m = dm ∧ dn ≤ dm⌝⦄ := by
  sorry
private lemma Zdigits_nonneg (x : Int) :
    ⦃⌜True⌝⦄
    (pure (Zdigits beta x) : Id _)
    ⦃⇓d => ⌜0 ≤ d⌝⦄ := by
  sorry
/-- Power greater than digit count

Coq theorem and proof:
```raw
Theorem Zpower_gt_Zdigits :
  forall e x,
  (Zdigits x <= e)%Z ->
  (Z.abs x < Zpower beta e)%Z.
Proof.
intros e x Hex.
destruct (Zdigits_correct x) as [H1 H2].
apply Z.lt_le_trans with (1 := H2).
now apply Zpower_le.
Qed.
```
-/
theorem Zpower_gt_Zdigits (e x : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜True⌝⦄
    (pure (Zdigits beta x) : Id _)
    ⦃⇓d => ⌜d ≤ e → Int.natAbs x < beta ^ e.natAbs⌝⦄ := by
  intro _
  -- By cases on whether x = 0
  by_cases hx : x = 0
  · -- If x = 0, then Zdigits returns 0
    simp only [Zdigits, hx, PredTrans.pure]
    intro hde
    -- Need to show: Int.natAbs 0 < beta ^ e.natAbs
    simp only [Int.natAbs_zero]
    -- Need: 0 < beta ^ e.natAbs
    apply pow_pos
    linarith [hβ]

  · -- If x ≠ 0, use Zdigits_correct
    have h_correct := Zdigits_correct beta x hβ hx
    simp only [ PredTrans.pure] at h_correct ⊢
    obtain ⟨h_lower, h_upper⟩ := h_correct
    intro hde

    -- From Zdigits_correct: |x| < beta ^ d.natAbs
    -- From hde: d ≤ e
    -- Need to show: |x| < beta ^ e.natAbs

    -- First handle the case where e < 0
    by_cases he : 0 ≤ e
    · -- e ≥ 0
      -- Since d ≤ e and both are integers, d.natAbs ≤ e.natAbs
      have d_nonneg : 0 ≤ (Zdigits beta x) := by
        have := Zdigits_nonneg beta x trivial
        simp only [ PredTrans.pure] at this
        exact this

      have h_natAbs_le : ((Zdigits beta x)).natAbs ≤ e.natAbs := by
        -- Since d ≤ e and 0 ≤ d and 0 ≤ e, we have d.natAbs ≤ e.natAbs
        have d_eq : ↑((Zdigits beta x)).natAbs = (Zdigits beta x) := by
          exact Int.natAbs_of_nonneg d_nonneg
        have e_eq : ↑e.natAbs = e := by
          exact Int.natAbs_of_nonneg he
        -- Convert the inequality from Int to Nat
        have : (Zdigits beta x) ≤ e := hde
        rw [← d_eq, ← e_eq] at this
        exact Nat.cast_le.mp this

      -- Now we need: |x| < beta ^ e.natAbs
      -- We have: |x| < beta ^ d.natAbs
      -- And: d.natAbs ≤ e.natAbs
      -- So we need monotonicity of exponentiation

      -- First let's clarify types
      have h_x_bound : ↑(Int.natAbs x) < beta ^ ((Zdigits beta x)).natAbs := by
        convert h_upper using 2
        simp only [Int.natCast_natAbs]

      -- Use transitivity: |x| < beta^d.natAbs ≤ beta^e.natAbs
      have h_pow_mono : beta ^ ((Zdigits beta x)).natAbs ≤ beta ^ e.natAbs :=
        pow_mono_int (beta := beta) hβ h_natAbs_le

      calc ↑(Int.natAbs x)
        < beta ^ ((Zdigits beta x)).natAbs := h_x_bound
        _ ≤ beta ^ e.natAbs := h_pow_mono

    · -- e < 0
      -- If e < 0, then d ≤ e and 0 ≤ d (from Zdigits_nonneg) contradict.
      exfalso
      have d_nonneg : 0 ≤ (Zdigits beta x) := by
        have := Zdigits_nonneg beta x trivial
        simp only [ PredTrans.pure] at this
        exact this
      -- hde says Zdigits beta x ≤ e
      -- Combined with e < 0 and d_nonneg : 0 ≤ Zdigits beta x, we have a contradiction
      have hde_int : (Zdigits beta x) ≤ e := hde
      have e_neg : e < 0 := lt_of_not_ge he
      linarith [d_nonneg, hde_int, e_neg]

/-- Digit count greater than power

Coq theorem and proof:
```raw
Theorem Zdigits_gt_Zpower :
  forall e x,
  (Zpower beta e <= Z.abs x)%Z ->
  (e < Zdigits x)%Z.
Proof.
intros e x Hex.
generalize (Zpower_gt_Zdigits e x).
lia.
Qed.
```
-/
theorem Zdigits_gt_Zpower (e x : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜beta ^ e.natAbs ≤ Int.natAbs x⌝⦄
    (pure (Zdigits beta x) : Id _)
    ⦃⇓d => ⌜e < d⌝⦄ := by
  intro h_precond
  -- Use Zpower_gt_Zdigits to derive a contradiction if d ≤ e
  have h_zpower := @Zpower_gt_Zdigits beta h_beta e x hβ
  simp only [ PredTrans.pure] at h_zpower ⊢
  have h_spec := h_zpower trivial

  -- By contradiction: assume ¬(e < d), i.e., d ≤ e
  by_contra h_neg
  -- h_neg : ¬(e < (Zdigits beta x))
  -- Convert this to: (Zdigits beta x) ≤ e
  have h_le : (Zdigits beta x) ≤ e := by
    exact le_of_not_gt h_neg

  -- h_spec tells us: d ≤ e → |x| < beta^e.natAbs
  -- Since h_le gives us d ≤ e, we get |x| < beta^e.natAbs
  have h_bound : ↑(Int.natAbs x) < beta ^ e.natAbs := h_spec h_le

  -- But we have beta^e.natAbs ≤ |x| from precondition
  -- This is a contradiction: beta^e.natAbs ≤ |x| < beta^e.natAbs
  have h_precond' : beta ^ e.natAbs ≤ ↑(Int.natAbs x) := h_precond
  linarith [h_precond', h_bound]

/-- Helper lemma: Product upper bound for non-negative integers
For non-negative integers x and y, x + y + x*y < (x+1)*(y+1) -/
private lemma product_upper_bound (x y : Int) (_ : 0 ≤ x) (_ : 0 ≤ y) :
    x + y + x * y < (x + 1) * (y + 1) := by
  ring_nf
  linarith

/-- Helper lemma: Powers split for addition -/
private lemma pow_add_split (beta : Int) (dx dy : Int) (_ : beta > 1)
    (hdx : 0 ≤ dx) (hdy : 0 ≤ dy) :
    beta ^ (dx + dy).natAbs = beta ^ dx.natAbs * beta ^ dy.natAbs := by
  -- Since dx ≥ 0 and dy ≥ 0, we have dx + dy ≥ 0
  have h_sum_nonneg : 0 ≤ dx + dy := Int.add_nonneg hdx hdy
  -- Apply the lemma for natAbs of sum of non-negative integers
  rw [Int.natAbs_add_of_nonneg hdx hdy]
  -- Now we have beta ^ (dx.natAbs + dy.natAbs) = beta ^ dx.natAbs * beta ^ dy.natAbs
  -- This follows from the power addition law
  exact pow_add beta dx.natAbs dy.natAbs

/-- Helper lemma: For monadic Zdigits computation -/
private lemma Zdigits_run_eq (n : Int) :
    (Zdigits beta n) = (Zdigits beta n) := rfl

/-- Helper lemma: Digit count bound for sum with product.
    For non-negative {lean}`x` and {lean}`y`,
    {lean}`Zdigits beta (x + y + x * y) ≤ Zdigits beta x + Zdigits beta y`. -/
private lemma Zdigits_sum_product_bound (beta : Int) (x y : Int)
    (hbeta : beta > 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (Zdigits beta (x + y + x * y)) ≤
    (Zdigits beta x) + (Zdigits beta y) := by
  sorry
theorem Zdigits_mult_strong (x y : Int) (hbeta : beta > 1 := h_beta) :
    ⦃⌜0 ≤ x ∧ 0 ≤ y⌝⦄
    (pure (Zdigits beta (x + y + x * y)) : Id _)
    ⦃⇓d => ⌜∃ dx dy, Zdigits beta x = dx ∧ Zdigits beta y = dy ∧ d ≤ dx + dy⌝⦄ := by
  sorry
theorem Zdigits_mult (x y : Int) (hβ : beta > 1 := h_beta):
    ⦃⌜True⌝⦄
    (pure (Zdigits beta (x * y)) : Id _)
    ⦃⇓d => ⌜∃ dx dy, Zdigits beta x = dx ∧ Zdigits beta y = dy ∧ d ≤ dx + dy⌝⦄ := by
  sorry
theorem Zdigits_mult_ge (x y : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜x ≠ 0 ∧ y ≠ 0⌝⦄
    (pure (Zdigits beta (x * y)) : Id _)
    ⦃⇓d => ⌜∃ dx dy, Zdigits beta x = dx ∧ Zdigits beta y = dy ∧ dx + dy - 1 ≤ d⌝⦄ := by
  sorry
theorem Zdigits_div_Zpower (m e : Int) (h_beta : beta > 1) :
    ⦃⌜0 ≤ m ∧ 0 ≤ e ∧ ∃ dm, Zdigits beta m = dm ∧ e ≤ dm⌝⦄
    (pure (Zdigits beta (m / beta ^ e.natAbs)) : Id _)
    ⦃⇓d => ⌜∃ dm, Zdigits beta m = dm ∧ d = dm - e⌝⦄ := by
  sorry
theorem Zdigits_succ_le (x : Int) (h_beta : beta > 1):
    ⦃⌜0 ≤ x⌝⦄
    (pure (Zdigits beta (x + 1)) : Id _)
    ⦃⇓d => ⌜∃ dx, Zdigits beta x = dx ∧ d ≤ dx + 1⌝⦄ := by
  sorry
end DigitOperations

section Zdigits2

variable (beta : Int) (h_beta : beta > 1)

/-- Relationship between natural and integer digit count

Coq theorem and proof:
```raw
Theorem Z_of_nat_S_digits2_Pnat :
  forall m : positive,
  Z_of_nat (S (digits2_Pnat m)) = Zdigits radix2 (Zpos m).
Proof.
intros m.
apply eq_sym, Zdigits_unique.
rewrite <- Zpower_nat_Z.
rewrite Nat2Z.inj_succ.
change (_ - 1)%Z with (Z.pred (Z.succ (Z.of_nat (digits2_Pnat m)))).
rewrite <- Zpred_succ.
rewrite <- Zpower_nat_Z.
apply digits2_Pnat_correct.
Qed.
```
-/
theorem Z_of_nat_S_digits2_Pnat (m : Nat) :
    ⦃⌜m > 0⌝⦄
    (pure (Zdigits 2 m) : Id _)
    ⦃⇓d => ⌜d = (digits2_Pnat m)⌝⦄ := by
  intro hm_pos
  -- Let d be the (Nat) result of the binary digit counter.
  set dNat : Nat := (digits2_Pnat m)
  -- From correctness, we have: dNat > 0 and 2^(dNat-1) ≤ m < 2^dNat.
  have hbits := digits2_Pnat_correct (n := m) hm_pos
  -- Extract bounds and positivity.
  have dNat_pos : 0 < dNat := by
    -- unpack the wp result
    simpa [dNat, Id.instWP, PredTrans.pure] using (And.left hbits)
  have hlow_nat : 2 ^ (dNat - 1) ≤ m := by
    have := (And.left (And.right hbits))
    simpa [dNat, Id.instWP, PredTrans.pure] using this
  have hup_nat : m < 2 ^ dNat := by
    have := (And.right (And.right hbits))
    simpa [dNat, Id.instWP, PredTrans.pure] using this

  -- We will sandwich Zdigits 2 m between dNat and itself using general lemmas.
  -- Upper bound: Zdigits 2 m ≤ dNat from m < 2^dNat.
  have zd_le_dNat :=
    (Zdigits_le_Zpower (beta:=2) (hβ:=by decide) (x:= (m : Int)) (e := (dNat : Int)))
  -- Discharge the preconditions for Zdigits_le_Zpower.
  have pre_up : 0 ≤ (dNat : Int) ∧ Int.natAbs (m : Int) < (2 : Int) ^ (dNat : Int).natAbs := by
    constructor
    · exact (Int.natCast_nonneg dNat)
    · -- |m| = m and (dNat : Int).natAbs = dNat
      have hm_abs : (Int.natAbs (m : Int) : Int) = (m : Int) := by
        -- m is a natural, hence nonnegative as an integer
        simpa using (Int.natAbs_of_nonneg (show (0 : Int) ≤ (m : Int) from Int.natCast_nonneg m))
      have hd_abs : ((dNat : Int).natAbs : Int) = (dNat : Int) := by
        simpa using (Int.natAbs_of_nonneg (Int.natCast_nonneg dNat))
      -- cast the Nat inequality hup_nat to Int
      have : (m : Int) < (2 : Int) ^ dNat := by
        simpa using (Int.ofNat_lt.mpr hup_nat)
      simpa [hm_abs, hd_abs]
  have zd_le_dNat_run : (Zdigits 2 (m : Int)) ≤ (dNat : Int) := by
    have := zd_le_dNat (by decide) pre_up
    simpa [ Id.instWP, PredTrans.pure] using this

  -- Lower bound: dNat ≤ Zdigits 2 m from 2^(dNat-1) ≤ m.
  have dNat_le_zd :=
    (Zpower_le_Zdigits (beta:=2) (hβ:=by decide) (n := (m : Int)) (e := (dNat : Int) - 1))
  -- Preconditions for the strict lower-bound lemma.
  have pre_low : (m : Int) ≠ 0 ∧ (2 : Int) ^ (((dNat : Int) - 1).natAbs) ≤ Int.natAbs (m : Int) := by
    constructor
    · -- m > 0 ⇒ (m : Int) ≠ 0
      exact by
        intro h
        have h0 : Int.toNat (m : Int) = 0 := by simpa using congrArg Int.toNat h
        have : m = 0 := by simpa using h0
        exact (Nat.ne_of_gt hm_pos) this
    · -- rewrite both sides and cast the Nat inequality hlow_nat
      have hm_abs : (Int.natAbs (m : Int) : Int) = (m : Int) := by
        simpa using (Int.natAbs_of_nonneg (show (0 : Int) ≤ (m : Int) from Int.natCast_nonneg m))
      -- ((dNat : Int) - 1).natAbs = dNat - 1 since dNat ≥ 1
      have dNat_ge1 : (1 : Int) ≤ (dNat : Int) := Int.ofNat_le.mpr (Nat.succ_le_of_lt dNat_pos)
      have h_nonneg : 0 ≤ (dNat : Int) - 1 := sub_nonneg.mpr dNat_ge1
      -- establish Nat-level equality of exponents
      have hd_natAbs_eq : ((dNat : Int) - 1).natAbs = dNat - 1 := by
        apply (Nat.cast_injective : Function.Injective (fun k : Nat => (k : Int)))
        have : (((dNat : Int) - 1).natAbs : Int) = (dNat : Int) - 1 :=
          Int.natAbs_of_nonneg h_nonneg
        simpa [Int.ofNat_sub (Nat.succ_le_of_lt dNat_pos)] using this
      -- cast the lower-bound inequality from Nat to Int and rewrite exponents
      have : (2 : Int) ^ (dNat - 1) ≤ (m : Int) := by
        simpa using (Int.ofNat_le.mpr hlow_nat)
      simpa [hm_abs, hd_natAbs_eq] using this
  have dNat_le_zd_run : (dNat : Int) ≤ (Zdigits 2 (m : Int)) := by
    -- from (dNat - 1) < (Zdigits 2 m), add 1 on the left
    have hlt : (dNat : Int) - 1 < (Zdigits 2 (m : Int)) := by
      simpa [ Id.instWP, PredTrans.pure]
        using (dNat_le_zd (by decide) pre_low)
    have hle : (dNat : Int) - 1 + 1 ≤ (Zdigits 2 (m : Int)) :=
      Int.add_one_le_iff.mpr hlt
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hle

  -- Conclude equality by antisymmetry of ≤.
  have deq : (Zdigits 2 (m : Int)) = (dNat : Int) :=
    le_antisymm zd_le_dNat_run dNat_le_zd_run
  -- Wrap back into the wp shape
  simpa [ Id.instWP, PredTrans.pure] using deq

/-- Positive digit count for binary

Coq theorem and proof:
```raw
Theorem Zpos_digits2_pos :
  forall m : positive,
  Zpos (digits2_pos m) = Zdigits radix2 (Zpos m).
Proof.
intros m.
rewrite <- Z_of_nat_S_digits2_Pnat.
unfold Z.of_nat.
apply f_equal.
induction m ; simpl ; try easy ;
  apply f_equal, IHm.
Qed.
```
-/
theorem Zpos_digits2_pos (m : Nat) :
    ⦃⌜m > 0⌝⦄
    (pure (Zdigits 2 m) : Id _)
    ⦃⇓d => ⌜d = (digits2_Pnat m)⌝⦄ := by
  -- Directly reuse the previous theorem (same statement in this Lean port).
  exact Z_of_nat_S_digits2_Pnat m

/-- Equivalence of binary digit count functions

Coq theorem and proof:
```raw
Lemma Zdigits2_Zdigits :
  forall n, Zdigits2 n = Zdigits radix2 n.
Proof.
intros [|p|p] ; try easy ;
  apply Zpos_digits2_pos.
Qed.
```
-/
theorem Zdigits2_Zdigits (n : Int) :
    ⦃⌜True⌝⦄
    (pure (Zdigits 2 n) : Id _)
    ⦃⇓d => ⌜d = (Zdigits 2 n)⌝⦄ := by
  intro _
  -- Trivial reflexivity: running the same computation yields itself.
  rfl

end Zdigits2

end FloatSpec.Core.Digits
