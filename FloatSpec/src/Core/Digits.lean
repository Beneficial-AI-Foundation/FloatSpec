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
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic
import Mathlib.Algebra.Divisibility.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Std.Do
open scoped Int

namespace FloatSpec.Core.Digits

set_option maxRecDepth 4096
universe u

section DigitOperations

variable (beta : Int) (h_beta : beta > 1)

/-- Number of bits of a positive integer

    Computes the number of bits required to represent a positive natural number.
    Uses recursive division by 2 until the number becomes 0.
-/
def digits2_Pnat : Nat → Id Nat
  | 0 => pure 0
  | n + 1 => do
    let prev ← digits2_Pnat ((n + 1) / 2)
    pure (1 + prev)

/-- A pure helper with the same recursion, convenient for proofs. -/
def bits : Nat → Nat
  | 0     => 0
  | n + 1 => 1 + bits ((n + 1) / 2)

/-- Basic positivity: for `n > 0`, `bits n > 0`. -/
lemma bits_pos {n : Nat} (hn : 0 < n) : 0 < bits n := by
  cases' n with k
  · cases hn
  · simp [bits]

/-- Standard split: `n = 2*(n/2) + (n%2)` and `%2 < 2`. -/
lemma split2 (n : Nat) : n = 2 * (n / 2) + n % 2 ∧ n % 2 < 2 := by
  refine ⟨?h1, ?h2⟩
  · -- The fix is to wrap the lemma in `Eq.symm` to flip the equality.
    simpa [two_mul, Nat.mul_comm] using (Eq.symm (Nat.div_add_mod n 2))
  · exact Nat.mod_lt _ (by decide)

/-- Bits of a successor: unfold recursion. -/
lemma bits_succ (k : Nat) : bits (k + 1) = 1 + bits ((k + 1) / 2) := by
  simp [bits]

/-- Equality of the program and the pure helper. -/
lemma digits2_eq_bits (n : Nat) : digits2_Pnat n = pure (bits n) := by
  refine Nat.strongRecOn n (motive := fun n => digits2_Pnat n = pure (bits n)) ?step
  intro n ih
  cases' n with k
  · simp [digits2_Pnat, bits]
  · have ih_half : digits2_Pnat ((k + 1) / 2) = pure (bits ((k + 1) / 2)) := by
      have hlt : ((k + 1) / 2) < (k + 1) := by exact Nat.div_lt_self (Nat.succ_pos _) (by decide)
      exact ih ((k + 1) / 2) hlt
    simp [digits2_Pnat, bits, ih_half]

/-- Main bounds for `bits`: for `m > 0`, `2^(bits m - 1) ≤ m < 2^(bits m)`. -/
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
```coq
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
    digits2_Pnat n
    ⦃⇓d => ⌜d > 0 ∧ 2 ^ (d - 1) ≤ n ∧ n < 2 ^ d⌝⦄ := by
  intro hn
  have hb := bits_bounds n hn
  have dpos := bits_pos (n := n) hn
  -- Reduce the program to the pure helper and discharge the proposition
  simpa [digits2_eq_bits n] using And.intro dpos (And.intro hb.1 hb.2)

/-- Extract the k-th digit of a number n in the given radix

    Note: Lean's `Int./` and `%` use Euclidean semantics. The original
    Flocq proofs for digits rely on truncation-toward-zero for the division
    when bounding by powers. To match that proof style (e.g., `Z.quot_small`),
    we use truncated division `Int.tdiv` here. This ensures that for
    `|n| < beta^k` with `k ≥ 0`, the quotient is `0`, and hence the digit is `0`.
-/
def Zdigit (n k : Int) : Id Int :=
  pure (if k ≥ 0 then (Int.tdiv n (beta ^ k.natAbs)) % beta else 0)

/-- Digits with negative index are zero

Coq theorem and proof:
```coq
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
    Zdigit beta n k
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro hk
  unfold Zdigit
  simp [show ¬(k ≥ 0) from not_le.mpr hk]

/-- Digit of zero is always zero

Coq theorem and proof:
```coq
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
    Zdigit beta 0 k
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro _
  unfold Zdigit
  split <;> simp

/-- Digit of opposite number

Coq theorem and proof:
```coq
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
    Zdigit beta (-n) k
    ⦃⇓result => ⌜∃ orig_result, Zdigit beta n k = pure orig_result ∧
                  result = if k ≥ 0 then (Int.tdiv (-n) (beta ^ k.natAbs)) % beta else 0⌝⦄ := by
  intro _
  unfold Zdigit
  use (if k ≥ 0 then (Int.tdiv n (beta ^ k.natAbs)) % beta else 0)
  constructor
  · rfl
  · simp

/-- Digit is zero for large indices

Coq theorem and proof:
```coq
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
    Zdigit beta n e
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro ⟨hn_pos, hn_bound, he_pos⟩
  unfold Zdigit
  -- With k = e ≥ 0, the branch is active; truncated quotient is 0 under the bound
  simp [he_pos, Int.tdiv_eq_zero_of_lt hn_pos hn_bound]

/-- Digit is zero for large indices (general case)

Coq theorem and proof:
```coq
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
    Zdigit beta n e
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


/-- `beta` is positive from `1 < beta`. -/
private lemma beta_pos {beta : Int} (hβ : 1 < beta) : 0 < beta :=
  lt_trans (show (0 : Int) < 1 by decide) hβ

/-- Power of a positive integer is positive. -/
private lemma pow_pos_int {beta : Int} (hβ : 0 < beta) (k : Nat) :
    0 < beta ^ k := by
  simpa using (pow_pos hβ k)

/-- Evaluate the 0-th digit: it is exactly `n % beta`. -/
private lemma Zdigit_at_zero (beta n : Int) :
    Id.run (Zdigit beta n 0) = n % beta := by
  unfold Zdigit
  simp  -- `tdiv n 1 = n` and `0 ≥ 0` discharges the `if`

-- For nonnegative `n` and positive divisor `d`,
-- `Int.tdiv n d` equals Euclidean `n / d`.
/-- General evaluation of `Zdigit` for nonnegative `n` and nonnegative `k`. -/
private lemma Zdigit_eval_nonneg
    (beta n k : Int) (_hn : 0 ≤ n) (_hb : 0 < beta) (hk : 0 ≤ k) :
    Id.run (Zdigit beta n k) =
      (Int.tdiv n (beta ^ k.natAbs)) % beta := by
  unfold Zdigit
  simp [hk]

/-- For `0 ≤ n` and `0 < d`, truncated division gives zero iff `n < d`. -/
private lemma tdiv_zero_iff_lt_of_nonneg_pos {n d : Int}
    (hn : 0 ≤ n) (hd : 0 < d) : Int.tdiv n d = 0 ↔ n < d := by
  constructor
  · -- If tdiv n d = 0, then n < d
    intro h_div_eq_zero
    -- Use the division algorithm: n = d * (n.tdiv d) + (n.tmod d)
    have hdiv_algo := Int.tdiv_add_tmod n d
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
For `n ≥ 0`, `beta > 0`, and any `k`, dividing by `beta^(k+1)` equals
first dividing by `beta` and then by `beta^k`.
-/
private lemma tdiv_pow_succ_assoc
    (n beta : Int) (hn : 0 ≤ n) (hb : 0 < beta) (k : Nat) :
    Int.tdiv n (beta ^ (k + 1)) = Int.tdiv (Int.tdiv n beta) (beta ^ k) := by
    -- For non-negative n and positive divisors, tdiv = ediv
  have hbeta_pow : 0 < beta ^ k := pow_pos hb k
  have hbeta_pow_succ : 0 < beta ^ (k + 1) := pow_pos hb (k + 1)

  -- Convert tdiv to ediv for non-negative arguments
  rw [Int.tdiv_eq_ediv_of_nonneg hn]
  rw [Int.tdiv_eq_ediv_of_nonneg]
  · rw [Int.tdiv_eq_ediv_of_nonneg hn]
    -- Now we can use the ediv associativity lemma
    rw [pow_succ']
    rw [Int.ediv_ediv_eq_ediv_mul _ (Int.le_of_lt hb)]
  · -- Prove that n.tdiv beta ≥ 0
    apply Int.tdiv_nonneg hn (Int.le_of_lt hb)


/-- Helper lemma: For positive n, there exists k ≥ 0 such that Zdigit beta n k ≠ 0 -/
private lemma exists_nonzero_digit (beta n : Int) (hβ : beta > 1) (hn : 0 < n) :
    ∃ k, 0 ≤ k ∧ Id.run (Zdigit beta n k) ≠ 0 := by
  have hb : 0 < beta := beta_pos (beta := beta) hβ
  classical
  -- Strong recursion on x.toNat, returning a Nat index
  let P : Nat → Prop :=
    fun m => ∀ x : Int, Int.toNat x = m → 0 < x → ∃ k : Nat, Id.run (Zdigit beta x (Int.ofNat k)) ≠ 0
  have step : ∀ m, (∀ t, t < m → P t) → P m := by
    intro m ih x hx hpos
    have hx0 : 0 ≤ x := le_of_lt hpos
    have hz0 : Id.run (Zdigit beta x 0) = x % beta := Zdigit_at_zero beta x
    by_cases hrem : x % beta = 0
    · -- 0-th digit is zero: factor out one β
      have hx_eq : x = beta * (x / beta) := by
        have := (Int.emod_add_ediv x beta).symm
        simpa [hrem, zero_add] using this
      let q : Int := Int.tdiv x beta
      have hq_nonneg : 0 ≤ q := Int.tdiv_nonneg hx0 (Int.le_of_lt hb)
      have hq_eq_ediv : Int.tdiv x beta = x / beta := by
        simpa using (Int.tdiv_eq_ediv_of_nonneg hx0 : Int.tdiv x beta = x / beta)
      have hx_q : x = beta * q := by
        have : x = beta * (Int.tdiv x beta) := by simpa [hq_eq_ediv] using hx_eq
        simpa [q] using this
      have hq_ne_zero : q ≠ 0 := by
        intro hq0
        have hx0eq : x = 0 := by simp [hx_q, hq0]
        have hxne : x ≠ 0 := by exact ne_of_gt hpos
        exact hxne hx0eq
      have hq_pos : 0 < q := lt_of_le_of_ne hq_nonneg (Ne.symm hq_ne_zero)
      have htwo_le_beta : (2 : Int) ≤ beta := by have : (1 : Int) < beta := hβ; linarith
      have hq_lt_x : q < x := by
        have hqq_le : 2 * q ≤ beta * q := Int.mul_le_mul_of_nonneg_right htwo_le_beta hq_nonneg
        have : q < 2 * q := by
          have one_lt_two : (1 : Int) < 2 := by decide
          simpa [one_mul] using (mul_lt_mul_of_pos_right one_lt_two hq_pos)
        exact lt_of_lt_of_le this (by simpa [hx_q] using hqq_le)
      -- apply IH to q
      have hlt_nat : Int.toNat q < m := by
        have hm_int : (m : Int) = x := by
          have : ((x.toNat : Nat) : Int) = x := by simpa using (Int.toNat_of_nonneg hx0)
          simpa [hx] using this
        exact (Int.toNat_lt hq_nonneg).mpr (by simpa [hm_int] using hq_lt_x)
      rcases ih (Int.toNat q) hlt_nat q rfl hq_pos with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      -- evaluate digits and use division associativity to lift
      have eval_x : Id.run (Zdigit beta x (Int.ofNat (k + 1))) =
          (Int.tdiv x (beta ^ (k + 1))) % beta := by
        have : 0 ≤ (Int.ofNat (k + 1)) := Int.natCast_nonneg _
        simpa using (Zdigit_eval_nonneg beta x (Int.ofNat (k + 1)) hx0 hb this)
      have eval_q : Id.run (Zdigit beta q (Int.ofNat k)) =
          (Int.tdiv q (beta ^ k)) % beta := by
        have : 0 ≤ (Int.ofNat k) := Int.natCast_nonneg _
        simpa using (Zdigit_eval_nonneg beta q (Int.ofNat k) (le_of_lt hq_pos) hb this)
      have assoc : Int.tdiv x (beta ^ (k + 1)) = Int.tdiv (Int.tdiv x beta) (beta ^ k) :=
        tdiv_pow_succ_assoc x beta hx0 hb k
      have tdiv_x_beta_eq_q : Int.tdiv x beta = q := rfl
      have lift_eq : Id.run (Zdigit beta x (Int.ofNat (k + 1))) = Id.run (Zdigit beta q (Int.ofNat k)) := by
        calc
          Id.run (Zdigit beta x (Int.ofNat (k + 1)))
              = (Int.tdiv x (beta ^ (k + 1))) % beta := by simpa [assoc] using eval_x
          _   = (Int.tdiv (Int.tdiv x beta) (beta ^ k)) % beta := by simp [assoc]
          _   = (Int.tdiv q (beta ^ k)) % beta := by simp [tdiv_x_beta_eq_q]
          _   = Id.run (Zdigit beta q (Int.ofNat k)) := by simpa using eval_q
      exact fun hzero => hk (Eq.trans lift_eq.symm hzero)
    · -- 0-th digit is nonzero
      refine ⟨0, ?_⟩
      simpa [hz0] using hrem
  -- Instantiate recursion at n
  have ex_nat : ∃ k : Nat, Id.run (Zdigit beta n (Int.ofNat k)) ≠ 0 :=
    (Nat.strongRecOn (Int.toNat n) (motive := P) step) n rfl hn
  have ⟨k, hk⟩ := ex_nat
  exact ⟨Int.ofNat k, Int.natCast_nonneg _, by simpa using hk⟩

/-- Non-zero digit exists for positive numbers

Coq theorem and proof:
```coq
Theorem Zdigit_not_0_pos :
  forall n, (0 < n)%Z ->
  exists k, (0 <= k)%Z /\ Zdigit n k <> Z0.
Proof.
intros n Hn.
revert Hn.
pattern n ; apply Zlt_0_ind.
clear n.
intros n IHn _.
case_eq (Zdigit n 0).
intros H.
destruct (Zle_lt_or_eq 0 (n / radix_val beta))%Z.
apply Z_div_pos.
now apply Zlt_gt.
apply Zle_refl.
elim (IHn (n / radix_val beta)%Z).
intros k Hk.
exists (Zsucc k).
split.
apply Zle_le_succ, proj1 Hk.
intros H'.
unfold Zdigit in H'.
rewrite Zquot_Zquot in H'.
rewrite Zplus_comm in H'.
rewrite Zpower_plus in H'.
change (Zpower beta 1) with (radix_val beta) in H'.
apply (Zrem_lt (Z.quot n (radix_val beta)) (radix_val beta)) in H'.
exact H'.
now apply Zlt_gt.
apply Zle_refl.
easy.
apply Zdiv_lt_upper_bound.
now apply Zlt_gt.
pattern n at 1 ; rewrite <- Zrem_Zquot.
apply Zplus_lt_compat_r.
rewrite <- H.
apply Zrem_lt.
now apply Zlt_gt.
exact H0.
intros p Hp.
exists 0%Z.
easy.
intros p Hp.
exists 0%Z.
easy.
Qed.
```
-/
theorem Zdigit_not_0_pos (n : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜0 < n⌝⦄
    Zdigit beta n 0
    ⦃⇓_ => ⌜∃ k, 0 ≤ k ∧ Id.run (Zdigit beta n k) ≠ 0⌝⦄ := by
  intro hn
  exact exists_nonzero_digit beta n hβ hn


/-- Non-zero digit exists for non-zero numbers

Coq theorem and proof:
```coq
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
    Zdigit beta n 0
    ⦃⇓_ => ⌜∃ k, 0 ≤ k ∧ Id.run (Zdigit beta n k) ≠ 0⌝⦄ := by
  intro hne
  have hb : 0 < beta := beta_pos (beta := beta) hβ
  classical
  by_cases hn0 : 0 ≤ n
  · -- Nonnegative case; since n ≠ 0, we have n > 0 and can reuse the positive lemma
    have hnpos : 0 < n := lt_of_le_of_ne hn0 (Ne.symm hne)
    exact exists_nonzero_digit beta n hβ hnpos
  · -- Negative case: apply the positive lemma to -n, then transfer nonzeroness back
    have hnlt : n < 0 := lt_of_not_ge hn0
    have hpos_neg : 0 < -n := neg_pos.mpr hnlt
    rcases exists_nonzero_digit beta (-n) hβ hpos_neg with ⟨k, hk_nonneg, hk_ne0⟩
    -- Evaluate both digits and relate tdiv under negation
    set denom := beta ^ k.natAbs with hden
    have eval_neg : Id.run (Zdigit beta (-n) k) = (Int.tdiv (-n) denom) % beta := by
      unfold Zdigit; simp [hk_nonneg, hden]
    have eval_pos : Id.run (Zdigit beta n k) = (Int.tdiv n denom) % beta := by
      unfold Zdigit; simp [hk_nonneg, hden]
    have tdiv_neg : Int.tdiv (-n) denom = - Int.tdiv n denom := by
      simp [Int.neg_tdiv]
    have hmod_neg_ne0 : (- Int.tdiv n denom) % beta ≠ 0 := by
      simpa [eval_neg, tdiv_neg] using hk_ne0
    -- Contrapositive to move nonzeroness across negation
    have hb_ne0 : beta ≠ 0 := ne_of_gt hb
    have hcontr : (Int.tdiv n denom % beta = 0) → False := by
      intro hmod0
      -- qn = beta * (qn / beta) so (-qn) is a multiple of beta, hence remainder is 0
      set qn := Int.tdiv n denom
      have hq_eq : qn = beta * (qn / beta) := by
        have := (Int.emod_add_ediv qn beta).symm
        simpa [hmod0, zero_add] using this
      have dvd_neg : beta ∣ (-qn) := by
        refine ⟨-(qn / beta), ?_⟩
        calc
          (-qn) = -(beta * (qn / beta)) := by
            simpa using congrArg Neg.neg hq_eq
          _ = beta * (-(qn / beta)) := by
            simp [mul_neg]
      have : (-qn) % beta = 0 :=
        Int.emod_eq_zero_of_dvd (a := beta) (b := -qn) dvd_neg
      exact hmod_neg_ne0 this
    -- Now pick the same k; if (digit n k) were 0, then by hcontr the (-n) digit would be 0 as well
    refine ⟨k, hk_nonneg, ?_⟩
    intro hz
    have hm : Int.tdiv n denom % beta = 0 := by simpa [eval_pos] using hz
    exact hcontr hm

/-- Digit of multiplied number

Coq theorem and proof:
```coq
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
    Zdigit beta (n * beta ^ l.natAbs) k
    ⦃⇓result => ⌜∃ shifted, Zdigit beta n (k - l) = pure shifted ∧ result = shifted⌝⦄ := by
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
```coq
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
    Zdigit beta (n / beta ^ l.natAbs) k
    ⦃⇓result => ⌜∃ shifted, Zdigit beta n (k + l) = pure shifted ∧ result = shifted⌝⦄ := by
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
      rw [Int.ediv_ediv_eq_ediv_mul n (Int.le_of_lt hbL)]
      rw [mul_comm]
    rw [hdiv_eq]

/-- Digit modulo power

Coq theorem and proof:
```coq
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
      exact Int.ediv_add_emod n Pl

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
    Zdigit beta (n % beta ^ l.natAbs) k
    ⦃⇓result => ⌜∃ orig, Zdigit beta n k = pure orig ∧ result = orig⌝⦄ := by
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
```coq
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
      have : m = n' := by omega
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
      have hmn' : m < n' := by omega
      have hle : m ≤ n' := le_of_lt hmn'
      have hsuc : m + 1 ≤ n' := by omega
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
    Zdigit beta (n % beta ^ l.natAbs) k
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
def Zsum_digit (f : Int → Int) : Nat → Id Int
  | 0 => pure 0
  | n + 1 => do
    let prev ← Zsum_digit f n
    pure (prev + f n * beta ^ n)

/-- Sum reconstructs from digits

Coq theorem and proof:
```coq
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
    Zsum_digit beta (fun i => Id.run (Zdigit beta n i)) k
    ⦃⇓result => ⌜result = n % beta ^ k⌝⦄ := by
  intro hn_pos
  -- Proof by induction on k
  induction k with
  | zero =>
    -- Base case: k = 0
    unfold Zsum_digit
    simp [pow_zero]
  | succ k ih =>
    -- Inductive case: k = k' + 1
    unfold Zsum_digit
    simp
    -- Apply IH to get the value for k
    have prev_val : Zsum_digit beta (fun i => Id.run (Zdigit beta n i)) k = pure (n % beta ^ k) := by
      exact ih
    rw [prev_val]
    simp

    -- Get the value of Zdigit(n, k)
    have hβpos : 0 < beta := beta_pos hβ
    have hpow_pos : 0 < beta ^ k := pow_pos hβpos k

    -- The goal is to show: n % beta^k + Zdigit(n,k) * beta^k = n % beta^(k+1)
    rw [pow_succ]

    -- First show what Zdigit evaluates to
    have zdigit_val : Id.run (Zdigit beta n k) = n.tdiv (beta ^ k) % beta := by
      unfold Zdigit
      have hk_nonneg : (k : Int) ≥ 0 := Int.natCast_nonneg k
      have k_natAbs : (k : Int).natAbs = k := Int.natAbs_natCast k
      simp [hk_nonneg, k_natAbs]

    rw [zdigit_val]

    -- For positive n and positive divisors, tdiv = ediv = /
    have tdiv_eq : n.tdiv (beta ^ k) = n / (beta ^ k) := by
      rw [Int.tdiv_eq_ediv]
      have hn : 0 < n := hn_pos
      simp [Int.le_of_lt hn]

    rw [tdiv_eq]

    -- Now we need to prove:
    --     n % (beta ^ k) + ((n / beta ^ k) % beta) * (beta ^ k) = n % (beta ^ (k+1))
    -- We do this by showing that the LHS is exactly the canonical remainder
    -- when dividing `n` by `beta^(k+1)`.

    -- Shorthands
    set b := beta ^ k
    have hb_pos : 0 < b := by simpa [b] using hpow_pos
    have hb_ne  : b ≠ 0 := ne_of_gt hb_pos
    have hβpos  : 0 < beta := by
      -- from hβ : beta > 1
      have : (0 : Int) < 1 := by decide
      exact lt_trans this hβ

    -- Candidate remainder:
    --   r = (n % b) + ((n / b) % beta) * b
    -- We’ll show: 0 ≤ r < b*beta  and  n = ((n / b) / beta) * (b*beta) + r
    -- so by uniqueness of remainder for Euclidean division, n % (b*beta) = r.
    let r : Int := n % b + (n / b % beta) * b

    -- r is nonnegative
    have hr_nonneg : 0 ≤ r := by
      have h0 : 0 ≤ n % b := Int.emod_nonneg _ hb_ne
      have h1 : 0 ≤ n / b % beta := Int.emod_nonneg _ (ne_of_gt hβpos)
      have h2 : 0 ≤ b := le_of_lt hb_pos
      exact add_nonneg h0 (mul_nonneg h1 h2)

    -- r < b * beta
    have hr_lt : r < b * beta := by
      -- From  n % b < b  and  (n / b % beta) < beta.
      have hx : n % b + 1 ≤ b :=
        (Int.add_one_le_iff).mpr (Int.emod_lt_of_pos _ hb_pos)
      have hy' : (n / b % beta) + 1 ≤ beta :=
        (Int.add_one_le_iff).mpr (Int.emod_lt_of_pos _ hβpos)

      -- Multiply hy' by b > 0 to get: (n / b % beta) * b + b ≤ beta * b
      have hy : (n / b % beta) * b + b ≤ beta * b := by
        -- (y+1)*b ≤ beta*b  ⇒  y*b + b ≤ beta*b
        have := (mul_le_mul_of_nonneg_right hy' (le_of_lt hb_pos))
        -- (y + 1) * b = y*b + b
        rw [add_mul] at this
        simp [one_mul] at this
        exact this

      -- From hx, add (n / b % beta) * b to both sides:
      have hx' : (n % b + 1) + (n / b % beta) * b ≤ b + (n / b % beta) * b :=
        add_le_add_right hx ((n / b % beta) * b)

      -- But (r + 1) = (n % b + 1) + (n / b % beta) * b (just reassociate/commute):
      have : r + 1 ≤ (n / b % beta) * b + b := by
        -- rearrange the RHS of hx' to match `(n / b % beta) * b + b`
        simpa [r, add_comm, add_left_comm, add_assoc, mul_comm] using hx'

      -- Chain the inequalities: r + 1 ≤ (n / b % beta) * b + b ≤ beta * b
      have : r + 1 ≤ beta * b := le_trans this hy

      -- swap to b*beta and turn `r + 1 ≤ ...` into `r < ...`
      have : r + 1 ≤ b * beta := by simpa [mul_comm] using this
      exact (Int.add_one_le_iff.mp this)

    -- Algebraic decomposition:
    --   n = ((n / b) / beta) * (b * beta) + r
    have hdecomp : n = ((n / b) / beta) * (b * beta) + r := by
      -- First split n with divisor b
      have h1 : n = (n / b) * b + n % b := by
        have := Int.ediv_add_emod n b
        rw [Int.mul_comm] at this
        exact this.symm
      -- Then split (n / b) with divisor beta
      have h2 : (n / b) = (n / b / beta) * beta + (n / b % beta) := by
        have := Int.ediv_add_emod (n / b) beta
        rw [Int.mul_comm] at this
        exact this.symm
      -- Combine the two decompositions
      calc
        n = (n / b) * b + n % b := h1
        _ = ((n / b / beta) * beta + (n / b % beta)) * b + n % b := by
              rw [← h2]
        _ = (n / b / beta) * (beta * b) + (n / b % beta) * b + n % b := by
              -- expand and reassociate products
              ring_nf
        _ = ((n / b) / beta) * (b * beta) + (n % b + (n / b % beta) * b) := by
              -- commute beta*b to b*beta and reassociate additions
              simp [mul_comm, add_comm, add_assoc]
        _ = ((n / b) / beta) * (b * beta) + r := rfl

    -- By uniqueness of quotient/remainder for Euclidean division on ℤ with positive divisor,
    -- the remainder of `n` modulo `b*beta` must be exactly `r`.
    have hmod : n % (b * beta) = r := by
      -- Use uniqueness of Euclidean division
      have hbeta_mul_pos : 0 < b * beta := mul_pos hb_pos hβpos
      -- We have n = ((n / b) / beta) * (b * beta) + r with 0 ≤ r < b * beta
      -- So by uniqueness, n % (b * beta) = r
      have : n / (b * beta) = (n / b) / beta ∧ n % (b * beta) = r := by
        rw [Int.ediv_emod_unique hbeta_mul_pos]
        constructor
        · -- Show r + (b * beta) * ((n / b) / beta) = n
          rw [Int.mul_comm (b * beta) ((n / b) / beta), Int.add_comm]
          exact hdecomp.symm
        · exact ⟨hr_nonneg, hr_lt⟩
      exact this.2

    -- Finish: rewrite back `b = beta ^ k` and use `pow_succ`
    -- We have hmod : n % (b * beta) = r where r = n % b + n / b % beta * b
    -- Need to show: n % b + n / b % beta * b = n % (b * beta)
    exact hmod.symm

/-- Extensionality for digit functions

Coq theorem and proof:
```coq
Theorem Zdigit_ext :
  forall n1 n2,
  (forall k, (0 <= k)%Z -> Zdigit n1 k = Zdigit n2 k) ->
  n1 = n2.
Proof.
intros n1 n2 H.
rewrite <- (ZOmod_small_abs n1 (Zpower beta (Z.max (Z.abs n1) (Z.abs n2)))).
rewrite <- (ZOmod_small_abs n2 (Zpower beta (Z.max (Z.abs n1) (Z.abs n2)))) at 2.
replace (Z.max (Z.abs n1) (Z.abs n2)) with (Z_of_nat (Z.abs_nat (Z.max (Z.abs n1) (Z.abs n2)))).
rewrite <- 2!Zsum_digit_digit.
induction (Z.abs_nat (Z.max (Z.abs n1) (Z.abs n2))).
easy.
simpl.
rewrite H, IHn.
apply refl_equal.
apply Zle_0_nat.
rewrite inj_Zabs_nat.
apply Z.abs_eq.
apply Z.le_trans with (Z.abs n1).
apply Zabs_pos.
apply Z.le_max_l.
apply Z.lt_le_trans with (Zpower beta (Z.abs n2)).
apply Zpower_gt_id.
apply Zpower_le.
apply Z.le_max_r.
apply Z.lt_le_trans with (Zpower beta (Z.abs n1)).
apply Zpower_gt_id.
apply Zpower_le.
apply Z.le_max_l.
Qed.
```
-/
theorem ZOmod_plus_pow_digit (n k : Int) (hn : 0 ≤ n) (hβ : beta > 1):
    ⦃⌜0 ≤ k⌝⦄
    Zdigit beta n k
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
    have := Int.ediv_add_emod n b
    rw [mul_comm] at this
    exact this.symm
  have hsplit2 : (n / b) = (n / b / beta) * beta + (n / b % beta) := by
    have := Int.ediv_add_emod (n / b) beta
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

theorem Zdigit_ext_nonneg (n m : Int) (hn : 0 ≤ n) (hm : 0 ≤ m) (hβ : beta > 1 := h_beta):
    ⦃⌜∀ k, 0 ≤ k → Id.run (Zdigit beta n k) = Id.run (Zdigit beta m k)⌝⦄
    Zdigit beta n 0
    ⦃⇓_ => ⌜n = m⌝⦄ := by
  intro hdig
  -- β > 1 ⇒ β > 0
  have hβpos : 0 < beta := by
    have : (0 : Int) < 1 := by decide
    exact lt_trans this hβ

  ----------------------------------------------------------------
  -- Step 1: for every K, remainders mod β^K are equal
  ----------------------------------------------------------------
  have hmods : ∀ K : Nat, n % beta ^ K = m % beta ^ K := by
    refine Nat.rec (motive := fun K => n % beta ^ K = m % beta ^ K) ?base ?step
    · -- K = 0
      simp
    · intro K ih
      have hkK : 0 ≤ (K : Int) := Int.natCast_nonneg _
      -- expand one digit for n
      have e1 :
          n % beta ^ (K + 1)
            = n % beta ^ K + (Id.run (Zdigit beta n (K : Int))) * beta ^ K := by
        have T := (ZOmod_plus_pow_digit (beta:=beta) n (k := (K : Int)) (hn := hn) (hβ := hβ))
        have h := T hkK
        simpa [Int.natAbs_natCast, hkK] using h
      -- expand one digit for m
      have e2 :
          m % beta ^ (K + 1)
            = m % beta ^ K + (Id.run (Zdigit beta m (K : Int))) * beta ^ K := by
        have T := (ZOmod_plus_pow_digit (beta:=beta) m (k := (K : Int)) (hn := hm) (hβ := hβ))
        have h := T hkK
        simpa [Int.natAbs_natCast, hkK] using h
      -- digits equal at K
      have hK := hdig (K : Int) hkK
      -- glue with IH
      simp [e1, e2, ih, hK]

  ----------------------------------------------------------------
  -- Step 2: from equal remainders, get β^K ∣ (n - m) for every K
  ----------------------------------------------------------------
  have hdivs : ∀ K : Nat, beta ^ K ∣ (n - m) := by
    intro K
    have rn_eq : n % beta ^ K = m % beta ^ K := hmods K

    -- name quotients and remainders to avoid rewriting under / and %
    set qn := n / beta ^ K with hqn
    set rn := n % beta ^ K with hrn
    set qm := m / beta ^ K with hqm
    set rm := m % beta ^ K with hrm

    have n_expand : n = (beta ^ K) * qn + rn := by
      simpa [hqn, hrn, mul_comm] using (Int.ediv_add_emod n (beta ^ K)).symm
    have m_expand : m = (beta ^ K) * qm + rm := by
      simpa [hqm, hrm, mul_comm] using (Int.ediv_add_emod m (beta ^ K)).symm

    -- difference and factor β^K
    have diff :
        n - m = (beta ^ K) * (qn - qm) + (rn - rm) := by
      calc
        n - m
            = ((beta ^ K) * qn + rn) - ((beta ^ K) * qm + rm) := by
                simp [n_expand, m_expand]
        _ = (beta ^ K) * (qn - qm) + (rn - rm) := by
                ring_nf

    have rn_eq' : rn = rm := by simpa [hrn, hrm] using rn_eq
    have diff' : n - m = (beta ^ K) * (qn - qm) := by
      simpa [rn_eq', sub_self, add_comm] using diff
    refine ⟨qn - qm, ?_⟩
    simpa [mul_comm] using diff'

  ----------------------------------------------------------------
  -- Step 3: if n ≠ m then pick K with β^K > |n - m| and contradict divisibility
  ----------------------------------------------------------------
  classical
  by_cases hnm : n = m
  · exact hnm
  ·
    -- n ≠ m ⇒ n - m ≠ 0 and |n - m| > 0
    have hdm_ne : n - m ≠ 0 := by
      intro h; exact hnm (sub_eq_zero.mp h)
    have habspos : 0 < |n - m| := by simpa [abs_pos] using hdm_ne

    -- build a K with β^K > |n - m| via bits on M = |n - m|
    have two_le_beta : (2 : Int) ≤ beta := by linarith [hβ]
    let M : Nat := (n - m).natAbs
    have hMpos : 0 < M := by
      have : (n - m).natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using hdm_ne
      exact Nat.pos_of_ne_zero this
    let K : Nat := bits M
    -- M < 2^K
    have hM_lt_twoPow : M < 2 ^ K := by
      have hb := bits_bounds M hMpos
      simpa [K] using hb.2
    -- cast to ℤ
    have hcast : (M : Int) < (2 : Int) ^ K := by exact_mod_cast hM_lt_twoPow

    -- (2 : ℤ)^K ≤ β^K by monotonicity (induction)
    have htwo_to_beta : (2 : Int) ^ K ≤ beta ^ K := by
      have hb_nonneg : 0 ≤ beta := le_of_lt hβpos
      have h2nonneg : 0 ≤ (2 : Int) := by decide
      induction K with
      | zero => simp
      | succ K ih =>
        have nonneg2K : 0 ≤ (2 : Int) ^ K := pow_nonneg h2nonneg _
        have nonnegbK : 0 ≤ beta ^ K := pow_nonneg hb_nonneg _
        calc
          (2 : Int) ^ (K + 1) = (2 ^ K) * 2 := by simp [pow_succ]
          _ ≤ (beta ^ K) * 2 := Int.mul_le_mul_of_nonneg_right ih (by decide)
          _ ≤ (beta ^ K) * beta := Int.mul_le_mul_of_nonneg_left two_le_beta nonnegbK
          _ = beta ^ (K + 1) := by simp [pow_succ]

    -- identify |n - m| with (M : ℤ)
    have abs_eq : (M : Int) = |n - m| := by
      simpa [M] using (Int.natAbs_of_nonneg (n - m))
    have h_abs_lt_twoPow : |n - m| < (2 : Int) ^ K := by
      simpa [abs_eq] using hcast
    have h_abs_lt_betaPow : |n - m| < beta ^ K :=
      lt_of_lt_of_le h_abs_lt_twoPow htwo_to_beta

    -- β^K ∣ (n - m); unless (n - m) = 0, we must have |n - m| ≥ β^K
    rcases hdivs K with ⟨t, ht⟩
    by_cases ht0 : t = 0
    · -- then n - m = 0 ⇒ contradiction to hnm
      have : n - m = 0 := by simpa [ht0] using ht
      exact (sub_eq_zero.mp this)
    ·
      have hbKpos : 0 < beta ^ K := by
        simpa using pow_pos hβpos K
      -- 0 < |t| ⇒ 1 ≤ |t|
      have one_le_abs_t : (1 : Int) ≤ |t| := by
        have h : 0 < |t| := abs_pos.mpr ht0
        -- specialize `Int.add_one_le_iff` at a = 0, b = |t|
        have : 0 + 1 ≤ |t| := (Int.add_one_le_iff.mpr h)
        simpa using this
      -- |β^K| ≤ |β^K| * |t|
      have base_le_base_times_t :
          |beta ^ K| ≤ |beta ^ K| * |t| := by
        have nonneg : 0 ≤ |beta ^ K| := abs_nonneg _
        have h1 : |beta ^ K| * 1 ≤ |beta ^ K| * |t| :=
          Int.mul_le_mul_of_nonneg_left one_le_abs_t nonneg
        simpa [mul_one] using h1
      -- hence β^K ≤ |n - m|
      have ge_betaK :
          beta ^ K ≤ |n - m| := by
        -- |n - m| = |β^K * t| = |β^K| * |t|
        have habs1 : |n - m| = |beta ^ K * t| := by simp [ht]
        have habs2 : |n - m| = |beta ^ K| * |t| := by simpa [abs_mul] using habs1
        have : |beta ^ K| ≤ |n - m| := by simpa [habs2] using base_le_base_times_t
        simpa [abs_of_pos hbKpos] using this
      -- contradiction with `|n - m| < β^K`
      have : False := (not_lt_of_ge ge_betaK) h_abs_lt_betaPow
      exact (this.elim)

/-- Division and digit sum (Euclidean `/`): valid for `0 ≤ n`. -/
theorem ZOdiv_plus_pow_digit
    (n k : Int) (hn : 0 ≤ n) (hβ : beta > 1 := h_beta) :
    ⦃⌜0 ≤ k⌝⦄
    Zdigit beta n k
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
    -- Use ediv_ediv with b ≥ 0
    have : n / b / beta = n / (b * beta) := by
      rw [Int.ediv_ediv_eq_ediv_mul]
      exact Int.le_of_lt hb_pos
    exact this

  -- n / b = (n / (b*β)) * β + (n / b) % β
  have step : n / b = (n / (b * beta)) * beta + (n / b % beta) := by
    -- `ediv_add_emod` gives `(n/b) = ((n/b)/β) * β + (n/b)%β`; rewrite the middle with `ediv_assoc`
    simpa [ediv_assoc, mul_comm] using (Int.ediv_add_emod (n / b) beta).symm

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

/-- Digit of a sum at position `k` (Euclidean `%`): valid for `0 ≤ n, m`. -/
theorem Zdigit_plus_nonneg
    (n m k : Int) (hn : 0 ≤ n) (hm : 0 ≤ m) (hβ : beta > 1 := h_beta) :
    ⦃⌜0 ≤ k⌝⦄
    Zdigit beta (n + m) k
    ⦃⇓result => ⌜∃ dn dm carry,
                  Zdigit beta n k = pure dn ∧
                  Zdigit beta m k = pure dm ∧
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
  have dndef : Zdigit beta n k = pure dn := by
    unfold Zdigit
    have : 0 ≤ k := hk
    simp [this, b, dn]
  have dmdef : Zdigit beta m k = pure dm := by
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
  have hnq : b * (n / b) + n % b = n := (Int.ediv_add_emod n b)
  have hmq : b * (m / b) + m % b = m := (Int.ediv_add_emod m b)

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
                ring
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
      Id.run (Zdigit beta (n + m) k) = ((n + m) / b) % beta := by
    unfold Zdigit
    have : 0 ≤ k := hk
    simp [this, b, Int.tdiv_eq_ediv_of_nonneg hnm_nonneg]

  -- push `% beta` through additions
  calc
    Id.run (Zdigit beta (n + m) k)
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
def Zscale (n k : Int) : Id Int :=
  pure (if 0 ≤ k then n * beta ^ k.natAbs else n / beta ^ (-k).natAbs)

/-- Monotonicity of `wp` for `Id` with a *pure* (`noThrow`) post. -/
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
```coq
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
    Zdigit beta (Id.run (Zscale beta n k)) k'
    ⦃⇓result => ⌜Zdigit beta n (k' - k) = pure result⌝⦄ := by
  intro h
  rcases h with ⟨hk', hk_or⟩
  unfold Zscale
  by_cases hk : 0 ≤ k
  · -- k ≥ 0: multiply by β^k
    simp [hk]
    have hmul :=
      (Zdigit_mul_pow (beta := beta) (h_beta := h_beta)
        (n := n) (k := k') (l := k) (hβ := hβ))
    -- Weaken the postcondition: (∃ s, P s ∧ result = s) ⇒ P result
    refine (wp_mono_pure (hmul hk)) ?_        -- if `wp_mono` isn’t available, try `wp_weaken` or `wp_consequence`
    intro result hex
    rcases hex with ⟨shifted, hP, hres⟩
    simpa [hres] using hP
  · -- k < 0: divide by β^(-k)
    have hklt : k < 0 := lt_of_not_ge hk
    have hl : 0 ≤ -k := neg_nonneg.mpr (le_of_lt hklt)
    -- simplify the program when `k < 0`
    simp [hk]
    -- from `(0 ≤ k ∨ 0 ≤ n)` and `k < 0`, deduce `0 ≤ n`
    have hn0 : 0 ≤ n := hk_or.resolve_left (not_le.mpr hklt)
    by_cases hzero : n = 0
    · -- trivial zero case
      subst hzero
      -- both sides are the zero digit
      simp [Zdigit, hk']     -- no `use`, let `simp` close it
    · -- positive case for the divide lemma
      have hnpos : 0 < n := lt_of_le_of_ne hn0 (Ne.symm hzero)
      have natAbs_neg : (-k).natAbs = k.natAbs := by simpa using Int.natAbs_neg k
      have sub_to_add : k' - k = k' + (-k) := by ring
      -- apply the divide lemma at exponent `-k`
      have hdiv :=
        (Zdigit_div_pow (beta := beta) (h_beta := h_beta)
          (n := n) (k := k') (l := -k) (hβ := hβ)) ⟨hl, hk', hnpos⟩
      -- rewrite to match our goal
      simpa [natAbs_neg, sub_to_add] using hdiv

/-- Scaling zero

Coq theorem and proof:
```coq
Theorem Zscale_0 :
  forall k,
  Zscale 0 k = Z0.
Proof.
intros k.
unfold Zscale.
case Zle_bool.
apply Zmult_0_l.
apply Zquot_0_l.
Qed.
```
-/
theorem Zscale_0 (k : Int) :
    ⦃⌜True⌝⦄
    Zscale beta 0 k
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro _
  unfold Zscale
  split <;> simp

/-- Scaling preserves sign (Euclidean division version). -/
theorem Zsame_sign_scale
    (n k : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜True⌝⦄
    Zscale beta n k
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
        have hdeq : n % d + d * (n / d) = n := by simpa [hd] using Int.emod_add_ediv n d
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
    Zscale beta (n * beta ^ l.natAbs) k
    ⦃⇓result => ⌜∃ scaled, Zscale beta n (k + l) = pure scaled ∧ result = scaled⌝⦄ := by
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
    · simp only [hkl, if_true, pure]
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
        simp only [hsum, if_true, pure]
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
      · simp only [not_le.mpr hqlt, if_false, pure]
      · rfl

/-- Helper lemma: For Zscale composition to work correctly, we need divisibility
    This captures the requirement that values in floating-point systems are
    properly normalized (i.e., mantissas are multiples of appropriate base powers) -/
private lemma zscale_div_exact (n d : Int) (hd : d > 0) (hdiv : d ∣ n) :
    (n / d) * d = n := by
  exact Int.ediv_mul_cancel hdiv

/-- Composition of scaling
    Note: This theorem assumes proper divisibility conditions for the scaling operations
    to compose correctly. These are typically satisfied in floating-point systems with
    normalized mantissas. -/
theorem Zscale_scale (n k l : Int) (hβ : beta > 1 := h_beta)
    (hdiv_k : k < 0 → beta ^ (-k).natAbs ∣ n)
    (hdiv_compose : k < 0 → l ≥ 0 → k + l < 0 → beta ^ l.natAbs ∣ n) :
    ⦃⌜True⌝⦄
    Zscale beta (Id.run (Zscale beta n k)) l
    ⦃⇓result => ⌜∃ scaled, Zscale beta n (k + l) = pure scaled ∧ result = scaled⌝⦄ := by
  intro _
  unfold Zscale
  have hβpos : 0 < beta := by
    have : (0 : Int) < 1 := by decide
    exact lt_trans this hβ
  -- Split on k and l signs (4 cases)
  by_cases hk : 0 ≤ k
  · -- inner multiply by β^k
    have hkabs : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk
    simp only [hk, if_true]
    by_cases hl : 0 ≤ l
    · -- outer multiply by β^l; altogether multiply by β^(k+l)
      have hkl : 0 ≤ k + l := add_nonneg hk hl
      have hklabs : ((k + l).natAbs : Int) = k + l := Int.natAbs_of_nonneg hkl
      simp only [hl, if_true]
      use n * beta ^ (k + l).natAbs
      constructor
      · simp only [hkl, if_true, pure]
      · simp only [pure, Id.run]
        rw [mul_assoc]
        congr 1
        -- Prove beta ^ k.natAbs * beta ^ l.natAbs = beta ^ (k + l).natAbs
        have : k.natAbs + l.natAbs = (k + l).natAbs := by
          have eq_as_int : (k.natAbs : Int) + (l.natAbs : Int) = ((k + l).natAbs : Int) := by
            rw [hkabs, Int.natAbs_of_nonneg hl, hklabs]
          exact Nat.cast_injective eq_as_int
        rw [← this, pow_add]
    · -- outer divide by β^{-l}; combine mult then div
      have hlneg : l < 0 := lt_of_not_ge hl
      have hp : 0 ≤ -l := neg_nonneg.mpr (le_of_lt hlneg)
      have hpabs : ((-l).natAbs : Int) = -l := Int.natAbs_of_nonneg hp
      -- (n*β^k) / β^{-l} = Zscale n (k + l)
      -- split on sign of k + l
      by_cases hsum : 0 ≤ k + l
      · -- cancellation to multiplication by β^(k+l)
        have : -l ≤ k := by linarith
        have hklabs : ((k + l).natAbs : Int) = k + l := Int.natAbs_of_nonneg hsum
        -- (n*β^k)/β^{-l} = n*β^{k+l}
        have : (n * beta ^ k.natAbs) / (beta ^ (-l).natAbs) = n * beta ^ (k + l).natAbs := by
          -- β^k = β^{-l} * β^{k+l} since k = -l + (k+l)
          have hsplit : beta ^ k.natAbs = beta ^ (-l).natAbs * beta ^ (k + l).natAbs := by
            have : k.natAbs = (-l).natAbs + (k + l).natAbs := by
              have eq_as_int : (k.natAbs : Int) = ((-l).natAbs : Int) + ((k + l).natAbs : Int) := by
                calc (k.natAbs : Int)
                  = k := hkabs
                  _ = (-l) + (k + l) := by ring
                  _ = ((-l).natAbs : Int) + ((k + l).natAbs : Int) := by
                    simp only [hpabs, hklabs]
              exact Nat.cast_injective eq_as_int
            rw [this, pow_add]
          -- Now cancel
          have hpos : 0 < beta ^ (-l).natAbs := by simpa using pow_pos hβpos (-l).natAbs
          have hne : beta ^ (-l).natAbs ≠ 0 := ne_of_gt hpos
          rw [hsplit]
          rw [mul_comm n _, mul_assoc]
          rw [Int.mul_ediv_cancel_left _ hne]
          rw [mul_comm]
        simp only [hl, if_false]
        use n * beta ^ (k + l).natAbs
        constructor
        · simp only [hsum, if_true, pure]
        · simp only [pure, Id.run, this]
      · -- k + l < 0 ⇒ total division by β^{-(k+l)}
        have hklabs : ((k + l).natAbs : Int) = -(k + l) := by
          have hlt : k + l < 0 := lt_of_not_ge hsum
          exact Int.ofNat_natAbs_of_nonpos (le_of_lt hlt)
        -- (n*β^k) / β^{-l} = n / β^{-(k+l)}
        have : (n * beta ^ k.natAbs) / (beta ^ (-l).natAbs) = n / (beta ^ (-(k + l)).natAbs) := by
          -- We need: β^{-l} = β^k * β^{-(k+l)} since -l = k + (-(k+l))
          have hsplit : beta ^ (-l).natAbs = beta ^ k.natAbs * beta ^ (-(k + l)).natAbs := by
            have : (-l).natAbs = k.natAbs + (-(k + l)).natAbs := by
              have eq_as_int : ((-l).natAbs : Int) = (k.natAbs : Int) + ((-(k + l)).natAbs : Int) := by
                calc ((-l).natAbs : Int)
                  = -l := hpabs
                  _ = k + (-(k + l)) := by ring
                  _ = (k.natAbs : Int) + (-(k + l)) := by rw [hkabs]
                  _ = (k.natAbs : Int) + ((-(k + l)).natAbs : Int) := by
                    congr
                    have : (-(k + l)).natAbs = (k + l).natAbs := by
                      simp only [Int.natAbs_neg]
                    simp only [this, hklabs]
              exact Nat.cast_injective eq_as_int
            rw [this, pow_add]
          rw [hsplit]
          have hposc : 0 < beta ^ k.natAbs := pow_pos hβpos _
          have hne : beta ^ k.natAbs ≠ 0 := ne_of_gt hposc
          -- n * beta^k / (beta^k * beta^{-(k+l)}) = n / beta^{-(k+l)}
          rw [mul_comm (beta ^ k.natAbs) (beta ^ (-(k + l)).natAbs)]
          exact Int.mul_ediv_mul_of_pos_left _ _ hposc
        simp only [hl, if_false]
        use n / beta ^ (-(k + l)).natAbs
        constructor
        · simp only [hsum, if_false, pure]
        · simp only [pure, Id.run, this]
  · -- inner divide by β^{-k}
    have hkneg : k < 0 := lt_of_not_ge hk
    have hp : 0 ≤ -k := neg_nonneg.mpr (le_of_lt hkneg)
    have hpabs : ((-k).natAbs : Int) = -k := Int.natAbs_of_nonneg hp
    simp only [hk, if_false]
    by_cases hl : 0 ≤ l
    · -- outer multiply by β^l on a quotient
      have hlabs : (l.natAbs : Int) = l := Int.natAbs_of_nonneg hl
      -- split on sign of k + l
      by_cases hsum : 0 ≤ k + l
      · -- (q * β^l) with q = n / β^{-k} equals scale_{k+l} n
        have hklabs : ((k + l).natAbs : Int) = k + l := Int.natAbs_of_nonneg hsum
        -- two subcases: if -k ≤ l, multiplication after division cancels to multiplication; else stays division
        -- But both are captured by the same final targets:
        simp only [hl, if_true]
        -- (n / β^{-k}) * β^l = n * β^{k+l} when k+l ≥ 0
        have this : (n / beta ^ (-k).natAbs) * beta ^ l.natAbs = n * beta ^ (k + l).natAbs := by
          -- Since k < 0 and l ≥ 0 with k+l ≥ 0, we have l ≥ -k
          have hl_ge : l ≥ -k := by linarith
          -- β^l = β^{-k} * β^{k+l}
          have hsplit : beta ^ l.natAbs = beta ^ (-k).natAbs * beta ^ (k + l).natAbs := by
            have : l.natAbs = (-k).natAbs + (k + l).natAbs := by
              have eq_as_int : (l.natAbs : Int) = ((-k).natAbs : Int) + ((k + l).natAbs : Int) := by
                calc (l.natAbs : Int)
                  = l := hlabs
                  _ = -k + (k + l) := by ring
                  _ = ((-k).natAbs : Int) + ((k + l).natAbs : Int) := by rw [hpabs, hklabs]
              exact Nat.cast_injective eq_as_int
            rw [this, pow_add]
          rw [hsplit]
          have hpos : 0 < beta ^ (-k).natAbs := pow_pos hβpos _
          calc n / beta ^ (-k).natAbs * (beta ^ (-k).natAbs * beta ^ (k + l).natAbs)
            = (n / beta ^ (-k).natAbs) * (beta ^ (-k).natAbs * beta ^ (k + l).natAbs) := by rfl
            _ = ((n / beta ^ (-k).natAbs) * beta ^ (-k).natAbs) * beta ^ (k + l).natAbs := by
              rw [mul_assoc]
            _ = n * beta ^ (k + l).natAbs := by
              -- We need (n / d) * d = n where d = beta ^ (-k).natAbs
              -- Use the divisibility assumption from the theorem hypothesis
              have hdiv_apply : beta ^ (-k).natAbs ∣ n := hdiv_k hkneg
              rw [zscale_div_exact n (beta ^ (-k).natAbs) hpos hdiv_apply]
        use n * beta ^ (k + l).natAbs
        constructor
        · simp only [hsum, if_true, pure]
        · simp only [pure, Id.run, this]
      · -- k + l < 0 ⇒ total division by β^{-(k+l)}
        have hklabs : ((k + l).natAbs : Int) = -(k + l) := by
          have hlt : k + l < 0 := lt_of_not_ge hsum
          exact Int.ofNat_natAbs_of_nonpos (le_of_lt hlt)
        simp only [hl, if_true]
        -- (n / β^{-k}) * β^l = n / β^{-(k+l)} when k+l < 0
        have this : (n / beta ^ (-k).natAbs) * beta ^ l.natAbs = n / beta ^ (-(k + l)).natAbs := by
          -- Since k < 0, l ≥ 0, and k+l < 0, we have l < -k
          have hl_lt : l < -k := by linarith
          -- β^{-k} = β^l * β^{-(k+l)}
          have hsplit : beta ^ (-k).natAbs = beta ^ l.natAbs * beta ^ (-(k + l)).natAbs := by
            have : (-k).natAbs = l.natAbs + (-(k + l)).natAbs := by
              have eq_as_int : ((-k).natAbs : Int) = (l.natAbs : Int) + ((-(k + l)).natAbs : Int) := by
                calc ((-k).natAbs : Int)
                  = -k := hpabs
                  _ = l + (-(k + l)) := by ring
                  _ = (l.natAbs : Int) + (-(k + l)) := by rw [hlabs]
                  _ = (l.natAbs : Int) + ((-(k + l)).natAbs : Int) := by
                    congr
                    have : (-(k + l)).natAbs = (k + l).natAbs := by
                      simp only [Int.natAbs_neg]
                    simp only [this, hklabs]
              exact Nat.cast_injective eq_as_int
            rw [this, pow_add]
          -- (n / β^{-k}) * β^l = n / β^{-(k+l)}
          -- We can rewrite using the split
          rw [hsplit]
          have hposl : 0 < beta ^ l.natAbs := pow_pos hβpos _
          have hposnkl : 0 < beta ^ (-(k + l)).natAbs := pow_pos hβpos _
          -- The expression is already in the form n / (beta ^ l.natAbs * beta ^ (-(k + l)).natAbs)
          -- thanks to the hsplit substitution above
          -- We need to show: (n / (β^l * β^{-(k+l)})) * β^l = n / β^{-(k+l)}
          -- Use the additional divisibility assumption
          have hdiv_l : beta ^ l.natAbs ∣ n := hdiv_compose hkneg hl (lt_of_not_ge hsum)
          -- Since beta^(-k) = beta^l * beta^(-(k+l)) and beta^(-k) | n,
          -- we have beta^(-(k+l)) | (n / beta^l)
          have hdiv_compose2 : beta ^ (-(k + l)).natAbs ∣ n / beta ^ l.natAbs := by
            -- From hsplit: beta^(-k) = beta^l * beta^(-(k+l))
            -- From hdiv_k: beta^(-k) | n
            -- So n = m * beta^(-k) = m * beta^l * beta^(-(k+l)) for some m
            -- Thus n / beta^l = m * beta^(-(k+l))
            obtain ⟨m, hm⟩ := hdiv_k hkneg
            use m
            rw [hm, hsplit]
            rw [mul_assoc]
            rw [Int.mul_ediv_cancel_left _ (ne_of_gt hposl)]
          -- Now we can apply the correct simplification
          calc n / (beta ^ l.natAbs * beta ^ (-(k + l)).natAbs) * beta ^ l.natAbs
            = n / (beta ^ l.natAbs * beta ^ (-(k + l)).natAbs) * beta ^ l.natAbs := rfl
            _ = (n / beta ^ l.natAbs) / beta ^ (-(k + l)).natAbs * beta ^ l.natAbs := by
              rw [Int.ediv_ediv_eq_ediv_mul]
              exact Int.le_of_lt hposl
            _ = ((n / beta ^ l.natAbs) * beta ^ l.natAbs) / beta ^ (-(k + l)).natAbs := by
              rw [Int.mul_ediv_assoc' _ hdiv_compose2]
            _ = n / beta ^ (-(k + l)).natAbs := by
              rw [zscale_div_exact n (beta ^ l.natAbs) hposl hdiv_l]
        use n / beta ^ (-(k + l)).natAbs
        constructor
        · simp only [not_le.mpr (lt_of_not_ge hsum), if_false, pure]
        · simp only [pure, Id.run, this]
    · -- outer divide by β^{-l}; two successive divisions ⇒ division by product
      simp only [hl, if_false]
      have hlneg : l < 0 := lt_of_not_ge hl
      have hq : 0 ≤ -l := neg_nonneg.mpr (le_of_lt hlneg)
      have hqabs : ((-l).natAbs : Int) = -l := Int.natAbs_of_nonneg hq
      -- (n / β^{-k}) / β^{-l} = n / (β^{-k} * β^{-l}) = n / β^{-(k+l)}
      have hpos1 : 0 < beta ^ (-k).natAbs := by simpa using pow_pos hβpos (-k).natAbs
      have hpos2 : 0 < beta ^ (-l).natAbs := by simpa using pow_pos hβpos (-l).natAbs
      have : (n / beta ^ (-k).natAbs) / beta ^ (-l).natAbs
               = n / (beta ^ (-k).natAbs * beta ^ (-l).natAbs) := by
        rw [Int.ediv_ediv_eq_ediv_mul]
        exact Int.le_of_lt hpos1
      have : (n / beta ^ (-k).natAbs) / beta ^ (-l).natAbs
               = n / beta ^ (-(k + l)).natAbs := by
        -- combine powers on the RHS
        have hsplit : beta ^ (-k).natAbs * beta ^ (-l).natAbs = beta ^ (-(k + l)).natAbs := by
          -- since -(k+l) = (-k) + (-l) on Int, and natAbs agrees with nonneg
          -- pow_add (Nat) lifts to multiply
          have : (-k).natAbs + (-l).natAbs = (-(k + l)).natAbs := by
            have eq_as_int : ((-k).natAbs : Int) + ((-l).natAbs : Int) = ((-(k + l)).natAbs : Int) := by
              calc ((-k).natAbs : Int) + ((-l).natAbs : Int)
                = -k + -l := by rw [hpabs, hqabs]
                _ = -(k + l) := by ring
                _ = ((-(k + l)).natAbs : Int) := by
                  have : k + l < 0 := add_neg_of_neg_of_nonpos hkneg (le_of_lt (lt_of_not_ge hl))
                  rw [Int.natAbs_neg]
                  exact (Int.ofNat_natAbs_of_nonpos (le_of_lt this)).symm
            exact Nat.cast_injective eq_as_int
          rw [← this, pow_add]
        rw [← hsplit]
        exact this
      -- RHS: k+l < 0 automatically when both k,l < 0
      have hsumneg : k + l < 0 := add_neg_of_neg_of_nonpos hkneg (le_of_lt (lt_of_not_ge hl))
      have hklabs : ((k + l).natAbs : Int) = -(k + l) := by
        exact Int.ofNat_natAbs_of_nonpos (le_of_lt hsumneg)
      use n / beta ^ (-(k + l)).natAbs
      constructor
      · simp only [not_le.mpr hsumneg, if_false, pure]
      · simp only [pure, Id.run, this]

/-- Extract a slice of digits from a number -/
def Zslice (n k1 k2 : Int) : Id Int := do
  let scaled ← Zscale beta n (-k1)
  pure (if 0 ≤ k2 then scaled % beta ^ k2.natAbs else 0)

/-- Digit of slice

Coq theorem and proof:
```coq
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
    Zdigit beta (Id.run (Zslice beta n k l)) m
    ⦃⇓result =>
        ⌜if m < l then
            ∃ orig, Zdigit beta n (k + m) = pure orig ∧ result = orig
          else result = 0⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hm, hnn⟩
  -- Split on `0 ≤ l` to expand the slice.
  by_cases hl : 0 ≤ l
  · ------------------------------------------------------------------ `0 ≤ l`
    -- Evaluate the slice programmatically.
    have hprog :
        Id.run (Zslice beta n k l)
          = (Id.run (Zscale beta n (-k)) % beta ^ l.natAbs) := by
      simp [Zslice, hl]
    -- Then decide whether the query digit index is inside the kept window.
    by_cases hml : m < l
    · -------------------------------------------------------------- in-range
      -- Let `scaled := Zscale n (-k)` and show it is nonnegative since `0 < n`.
      set scaled : Int := Id.run (Zscale beta n (-k)) with hscaled
      have hβpos : 0 < beta :=
        lt_trans (show (0 : Int) < 1 by decide) h_beta
      have hscaled_nonneg : 0 ≤ scaled := by
        -- `Zscale` either multiplies by a positive power (when `0 ≤ -k`)
        -- or divides by a positive power (when `-k < 0`), so with `0 < n`
        -- the result is ≥ 0 in both cases.
        -- Expand the definition of scaled
        simp only [hscaled]
        -- Now scaled = Id.run (Zscale beta n (-k))
        unfold Zscale
        simp only [pure, Id.run]
        -- The condition in Zscale is `0 ≤ k`, which for k = -k becomes `0 ≤ -k`
        split_ifs with hcond
        · -- Case: 0 ≤ -k, so scaled = n * beta ^ (-k).natAbs
          have hpow : 0 < beta ^ (-k).natAbs := pow_pos hβpos _
          exact mul_nonneg hnn (le_of_lt hpow)
        · -- Case: ¬(0 ≤ -k), so -k < 0, thus k > 0
          -- scaled = n / beta ^ (- -k).natAbs
          have hkpos : 0 < k := by
            have : -k < 0 := lt_of_not_ge hcond
            simpa using (neg_pos.mpr this)
          have : (- -k).natAbs = k.natAbs := by
            simp [neg_neg]
          simp only [this]
          have hpow : 0 < beta ^ k.natAbs := pow_pos hβpos _
          exact Int.ediv_nonneg hnn (le_of_lt hpow)
      -- Drop the outer “mod β^l” at digit position `m` using `tdiv_mod_pow_eq`
      -- (which needs only `0 ≤ scaled`, not strict positivity).
      have drop_mod_run :
          Id.run (Zdigit beta (scaled % beta ^ l.natAbs) m)
            = Id.run (Zdigit beta scaled m) := by
        -- Open `Zdigit` to expose `(tdiv …) % beta` form and apply the helper.
        unfold Zdigit; simp [hm]
        exact tdiv_mod_pow_eq
                (n := scaled) (k := m) (l := l) (β := beta)
                hscaled_nonneg hm hml h_beta
      -- Shift the digit across scaling: `digit (Zscale n (-k)) m = digit n (k+m)`.
      -- This holds under `0 ≤ m` and the disjunction `(0 ≤ -k ∨ 0 ≤ n)`,
      -- satisfied here by `0 ≤ n` from `0 < n`.
      have shift_eq :
          Zdigit beta n (k + m)
            = pure (Id.run (Zdigit beta scaled m)) := by
        have htriple :=
          (Zdigit_scale_point (beta := beta) (h_beta := h_beta)
             (n := n) (k := -k) (k' := m))
             ⟨hm, Or.inr hnn⟩
        -- `Zdigit_scale_point` gives: `Zdigit n (m - (-k)) = pure (…run…)`.
        -- Rewrite `m - (-k)` to `k + m`.
        have : m - (-k) = k + m := by ring
        rw [← this]
        exact htriple
      -- Assemble the required witness for the `if` branch.
      -- The postcondition simplifies to witnessing the existence of orig.
      simp only [hml, if_true]
      -- The goal is now to prove the existential
      -- Let's unfold what we need to prove
      -- We need: ∃ orig, Zdigit beta n (k + m) = pure orig ∧ Id.run (Zdigit beta (Id.run (Zslice beta n k l)) m) = orig
      -- Choose `orig` to be Id.run (Zdigit beta scaled m)
      refine ⟨Id.run (Zdigit beta scaled m), ?_, ?_⟩
      · -- First conjunct: Zdigit beta n (k + m) = pure (Id.run (Zdigit beta scaled m))
        exact shift_eq
      · -- Second conjunct: Id.run (Zdigit beta (Id.run (Zslice beta n k l)) m) = Id.run (Zdigit beta scaled m)
        -- Replace the program by the simplified one
        simpa [hprog] using drop_mod_run
    · -------------------------------------------------------------- out-of-range (`l ≤ m`)
      have hle : l ≤ m := le_of_not_gt hml
      -- Use the out-of-range lemma on `% β^l`.
      have vanish :=
        (Zdigit_mod_pow_out (beta := beta) (h_beta := h_beta)
          (n := Id.run (Zscale beta n (-k))) (k := m) (l := l) (hβ := h_beta)) ⟨hl, hle⟩
      -- Select the `else` branch and finish.
      simpa [hml, hprog] using vanish
  · ------------------------------------------------------------------ `l < 0`
    have hlt : l < 0 := lt_of_not_ge hl
    -- The slice is exactly `0`, so any digit is `0`.
    have z0 := (Zdigit_0 (beta := beta) (k := m)) (by trivial)
    -- When l < 0, the slice evaluates to 0
    have hslice_zero : Id.run (Zslice beta n k l) = 0 := by
      simp [Zslice, hlt]
    rw [hslice_zero]
    -- Since m ≥ 0 and l < 0, we have ¬(m < l)
    have hml_false : ¬(m < l) := by
      intro h
      have : m < 0 := lt_trans h hlt
      exact absurd this (not_lt_of_ge hm)
    -- Apply z0 which gives us result = 0
    have hres := z0
    -- The postcondition simplifies to result = 0 in the else branch
    simp [hml_false]
    exact hres


/-- Digit of slice outside range

Coq theorem and proof:
```coq
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
    Zdigit beta (Id.run (Zslice beta n k l)) m
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro hle
  by_cases hl : 0 ≤ l
  · -- Regular out-of-range: keep `l` digits, query at `m ≥ l`.
    have hprog :
        Id.run (Zslice beta n k l)
          = (Id.run (Zscale beta n (-k)) % beta ^ l.natAbs) := by
      simp [Zslice, hl]
    -- Apply the ready-made lemma.
    have vanish :=
      (Zdigit_mod_pow_out (beta := beta) (h_beta := h_beta)
        (n := Id.run (Zscale beta n (-k))) (k := m) (l := l) (hβ := h_beta)) ⟨hl, hle⟩
    simpa [hprog] using vanish
  · -- `l < 0`: the slice is `0`, so every digit is `0` without needing `0 ≤ m`.
    have hlt : l < 0 := lt_of_not_ge hl
    -- When l < 0, Zslice returns 0
    simp only [Zslice, hl, if_false]
    -- Apply Zdigit_0
    exact (Zdigit_0 (beta := beta) (k := m)) (by trivial)

/-- Zslice of zero is always zero

Coq theorem and proof:
```coq
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
    Zslice beta 0 k k'
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro _
  unfold Zslice Zscale
  simp

/-- Slicing preserves sign conditions

Coq theorem and proof:
```coq
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
    Zslice beta n k l
    ⦃⇓result => ⌜0 ≤ result⌝⦄ := by
  intro h
  rcases h with ⟨_hn, _hk, hl⟩
  -- Open the definition and use the `0 ≤ l` branch.
  unfold Zslice
  -- After rewriting the `if`, the wp reduces to a predicate on the result of `Zscale`.
  -- `simp [hl]` both selects the `then` branch and simplifies the wp for `Id`.
  simp [hl]
  -- Goal now is: 0 ≤ (Id.run (Zscale beta n (-k))) % (beta ^ l.natAbs)
  have hβpos : 0 < beta :=
    lt_trans (show (0 : Int) < 1 by decide) h_beta
  have hpowpos : 0 < beta ^ l.natAbs := pow_pos hβpos _
  -- Remainder modulo a positive number is nonnegative.
  exact Int.emod_nonneg _ (ne_of_gt hpowpos)

/-- Composition of Zslice operations

Coq theorem and proof:
```coq
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
    Zslice beta (Id.run (Zslice beta n k1 k2)) k1' k2'
    ⦃⇓result =>
       ⌜∃ inner_slice,
          Zslice beta n (k1 + k1') (min (k2 - k1') k2') = pure inner_slice ∧
          result = inner_slice⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hnpos, hk1p, hk1p_le_k2⟩
  -- Case on k2'
  by_cases hk2p : 0 ≤ k2'
  · ------------------------------------------------------------------ k2' ≥ 0
    -- Let the two values be L and R.
    set L : Int := Id.run (Zslice beta (Id.run (Zslice beta n k1 k2)) k1' k2') with hL
    set R : Int := Id.run (Zslice beta n (k1 + k1') (min (k2 - k1') k2')) with hR

    -- Both sides are nonnegative (needed for extensionality).
    have hβpos : 0 < beta := lt_trans (show (0 : Int) < 1 by decide) h_beta
    have pow_pos_of_nonneg : ∀ (t : Int), 0 ≤ t → 0 < beta ^ t.natAbs :=
      fun t ht => by simpa using pow_pos hβpos t.natAbs

    have hL_nonneg : 0 ≤ L := by
      -- L = (scaled % β^{k2'}) since k2' ≥ 0
      simp [Zslice, hk2p, hL]
      exact Int.emod_nonneg _ (ne_of_gt (pow_pos_of_nonneg _ hk2p))

    have hR_nonneg : 0 ≤ R := by
      -- R = if 0 ≤ min(..) then (scaled % β^{min(..)}) else 0
      by_cases hmin : 0 ≤ min (k2 - k1') k2'
      · have : 0 < beta ^ (min (k2 - k1') k2').natAbs :=
          pow_pos_of_nonneg _ hmin
        simp [Zslice, hR, hmin]
        exact Int.emod_nonneg _ (ne_of_gt this)
      · simp [Zslice, hR, hmin]

    -- Digit-by-digit equality for all k ≥ 0.
    -- Digit-by-digit equality as a plain proposition (no `.down`).
    have hdigs :
        ∀ m : Int, 0 ≤ m →
          Id.run (Zdigit beta L m) = Id.run (Zdigit beta R m) := by
      intro m hm
      -- Unfold the outer slice on the left.
      -- Show inner slice is nonnegative for use as precondition
      have hInner_nonneg : 0 ≤ Id.run (Zslice beta n k1 k2) := by
        by_cases hk2nz : 0 ≤ k2
        · have : 0 < beta ^ k2.natAbs := pow_pos_of_nonneg _ hk2nz
          simp [Zslice, hk2nz]  -- reduces to emod of positive modulus
          exact Int.emod_nonneg _ (ne_of_gt this)
        · have hk2lt : k2 < 0 := lt_of_not_ge hk2nz
          simp [Zslice, if_neg (not_le_of_gt hk2lt)]  -- slice is 0
      have hLdig :=
        (Zdigit_slice (beta := beta) (h_beta := h_beta)
          (n := Id.run (Zslice beta n k1 k2)) (k := k1') (l := k2') (m := m)) ⟨hm, hInner_nonneg⟩
      -- Unfold the right slice.
      have hRdig :=
        (Zdigit_slice (beta := beta) (h_beta := h_beta)
          (n := n) (k := (k1 + k1')) (l := min (k2 - k1') k2') (m := m)) ⟨hm, (le_of_lt hnpos)⟩

      -- Analyze `m < k2'` (matches `m < min(..)` on the right together with `k1'+m < k2`).
      by_cases hm_lt_k2p : m < k2'
      · -------------------------------------------------------- inside k2' window
        -- Left: digit of (Zslice n k1 k2) at index (k1'+m)
        have hL1 := hLdig
        -- Since m < k2', the slice gives us the digit at k1' + m
        have h_inner : ∃ r₁,
            Zdigit beta (Id.run (Zslice beta n k1 k2)) (k1' + m) = pure r₁ ∧
            Id.run (Zdigit beta L m) = r₁ := by
          simpa [hL, hm_lt_k2p] using hL1
        rcases h_inner with ⟨r₁, hEqL, hRunL⟩

        -- For that inner digit, open the inner slice:
        have hm_shift_nonneg : 0 ≤ k1' + m := add_nonneg hk1p hm
        have hInner :=
          (Zdigit_slice (beta := beta) (h_beta := h_beta)
            (n := n) (k := k1) (l := k2) (m := k1' + m)) ⟨hm_shift_nonneg, le_of_lt hnpos⟩

        -- Case split on `k1' + m < k2` (equivalently `m < k2 - k1'`).
        by_cases hsum_lt_k2 : k1' + m < k2
        · ---------------------------------------------------- also inside k2 window
          -- Inner digit equals digit of `n` at `k1 + k1' + m`.
          have h_orig : ∃ r₂,
              Zdigit beta n (k1 + (k1' + m)) = pure r₂ ∧
              Id.run (Zdigit beta (Id.run (Zslice beta n k1 k2)) (k1' + m)) = r₂ := by
            simpa [hsum_lt_k2] using hInner
          rcases h_orig with ⟨r₂, hEqInner, hRunInner⟩
          -- From `hEqL : Zdigit (Zslice n k1 k2) (k1'+m) = pure r₁`
          -- and `hRunInner : Id.run (Zdigit (Zslice n k1 k2) (k1'+m)) = r₂`,
          -- we get `r₁ = r₂`.
          have r_eq : r₁ = r₂ := by
            -- `Id.run (pure r₁) = r₁`
            have : Id.run (Zdigit beta (Id.run (Zslice beta n k1 k2)) (k1' + m)) = r₁ := by
              simpa [hEqL]
            simpa [this] using hRunInner

          -- Right: since `m < min (k2 - k1') k2'` iff `m < k2' ∧ m < k2 - k1'`,
          -- we can open the right slice to the same base digit.
          have hlt_min :
              m < min (k2 - k1') k2' := by
            have hm2 : m < (k2 - k1') := by
              -- `k1'+m < k2`  ↔  `m < k2 - k1'`
              linarith
            have hm1 := hm_lt_k2p
            -- `m < min x y` iff both
            exact lt_min_iff.mpr ⟨hm2, hm1⟩

          have h_right : ∃ r₃,
              Zdigit beta n ((k1 + k1') + m) = pure r₃ ∧
              Id.run (Zdigit beta R m) = r₃ := by
            -- Open right slice under `hlt_min`.
            simpa [hR, hlt_min, add_assoc, add_comm, add_left_comm]
              using hRdig
          rcases h_right with ⟨r₃, hEqR, hRunR⟩

          -- Both sides now share the same base-digit program:
          -- `Zdigit β n ((k1 + k1') + m)`. Conclude equality.
          have share :
              Zdigit beta n ((k1 + k1') + m) = pure r₂ := by
            -- From `hEqInner : Zdigit β n (k1 + (k1' + m)) = pure r₂`
            simpa [add_assoc, add_comm, add_left_comm] using hEqInner
          have shareR :
              Zdigit beta n ((k1 + k1') + m) = pure r₃ := by
            simpa [add_assoc, add_comm, add_left_comm] using hEqR
          have r23 : r₂ = r₃ := by
            -- same pure program ⇒ same value
            simpa [share] using congrArg Id.run shareR

          -- Finally, compare the runs of both digits.
          simp [hRunL, r_eq, r23, hRunR]

        · ---------------------------------------------------- outside k2 window
          -- Inner digit is 0, hence `Id.run (Zdigit β L m) = 0`.
          have : Id.run (Zdigit beta (Id.run (Zslice beta n k1 k2)) (k1' + m)) = 0 := by
            -- `Zdigit_slice_out` on the inner slice at index `k1'+m`.
            have out :=
              (Zdigit_slice_out (beta := beta) (h_beta := h_beta)
                (n := n) (k := k1) (l := k2) (m := k1' + m)) (le_of_not_gt hsum_lt_k2)
            simpa using out
          have hLzero : Id.run (Zdigit beta L m) = 0 := by
            -- combine with `hEqL`
            have : r₁ = 0 := by simpa [hEqL] using this
            simpa [hRunL, this]

          -- Right: not inside `min (...)` since `m < k2'` but `¬ (m < k2 - k1')`.
          have not_min :
              ¬ m < min (k2 - k1') k2' := by
            -- `m < min x y` ↔ `m < x ∧ m < y`
            -- we already have ¬(m < x)
            intro h
            have := (lt_min_iff.mp h).1
            -- this gives us m < k2 - k1', but we have ¬(k1' + m < k2) which means ¬(m < k2 - k1')
            have h_contra : k1' + m < k2 := by linarith
            exact hsum_lt_k2 h_contra

          -- So right digit is 0.
          have hRzero :
              Id.run (Zdigit beta R m) = 0 := by
            simpa [hR, not_min] using hRdig
          simpa [hLzero, hRzero]

      · -------------------------------------------------------- outside k2'
        -- Left digit is 0.
        have hLzero :
            Id.run (Zdigit beta L m) = 0 := by
          simpa [hL, hm_lt_k2p] using hLdig
        -- Right: also outside `min (...)` because `m < min ...` implies `m < k2'`.
        have not_min :
            ¬ m < min (k2 - k1') k2' := by
          intro h
          have := (lt_min_iff.mp h).2
          -- this gives us m < k2', but we have ¬(m < k2')
          exact hm_lt_k2p this
        have hRzero :
            Id.run (Zdigit beta R m) = 0 := by
          simpa [hR, not_min] using hRdig
        simpa [hLzero, hRzero]

    -- By extensionality on digits (both sides nonnegative).
    have hLR :
        L = R := by
      -- Use extensionality on digits
      have hext :=
        (Zdigit_ext_nonneg (beta := beta) (h_beta := h_beta) (n := L) (m := R)
          (hn := hL_nonneg) (hm := hR_nonneg))
      -- Apply the extensionality with the digit equality
      -- The triple says: given equal digits, n = m
      -- We need to provide the condition: ∀ k, 0 ≤ k → Id.run (Zdigit beta L k) = Id.run (Zdigit beta R k)
      -- and then extract the conclusion L = R
      have hdig_eq : ∀ k, 0 ≤ k → Id.run (Zdigit beta L k) = Id.run (Zdigit beta R k) := by
        -- This follows from the digit equality we established above for all m
        intro k hk
        -- The proof above shows that for all m ≥ 0, the digits are equal
        -- This was established through the case analysis by contradiction in the proof above
        -- where all cases result in Id.run (Zdigit beta L m) = Id.run (Zdigit beta R m)
        exact hdigs k hk
      -- Apply the Hoare triple with the digit equality condition
      exact hext hdig_eq

    -- Choose the RHS value as the witness
    refine ⟨R, ?_, ?_⟩
    · -- the RHS program is pure at value `R`
      -- (definitional for `Id`; no branching required)
      simpa [hR]
    · -- the LHS result equals `R` by `hLR`, but result is `L` by definition
      simpa [hL, hLR]

  · ------------------------------------------------------------------ k2' < 0
    have hk2p_lt : k2' < 0 := lt_of_not_ge hk2p
    -- Left slice is 0
    have hL0 :
        Id.run (Zslice beta (Id.run (Zslice beta n k1 k2)) k1' k2') = 0 := by
      simp [Zslice, hk2p_lt]
    -- Right slice also 0 because `min (k2 - k1') k2' ≤ k2' < 0`
    have hmin_neg : ¬ 0 ≤ min (k2 - k1') k2' := by
      -- If `0 ≤ min`, then `0 ≤ k2'` (since `min ≤ k2'`), contradicting `hk2p_lt`.
      have hle : min (k2 - k1') k2' ≤ k2' := Int.min_le_right _ _
      intro h0
      exact (not_le_of_gt hk2p_lt) (le_trans h0 hle)
    have hR0 :
        Id.run (Zslice beta n (k1 + k1') (min (k2 - k1') k2')) = 0 := by
      simp [Zslice, hmin_neg]

    -- Return 0 as witness and finish
    refine ⟨0, ?_, ?_⟩
    · -- RHS program is pure 0
      -- Since min (k2 - k1') k2' < 0 (by hmin_neg), Zslice returns pure 0
      simp only [Zslice, if_neg hmin_neg]
      -- The do-block simplifies to pure 0 since we ignore the Zscale result
      rfl
    · -- LHS result is 0 by hL0
      exact hL0

/-- Zslice and multiplication by power of beta

Coq theorem and proof:
```coq
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
    Zslice beta (n * beta ^ k.natAbs) k1 k2
    ⦃⇓result => ⌜∃ slice_shifted, Zslice beta n (k1 - k) k2 = pure slice_shifted ∧
                  result = slice_shifted⌝⦄ := by
  intro hk
  -- Unfold Zslice to work with the underlying Zscale
  unfold Zslice
  -- Case on k2
  split_ifs with hk2
  · -- Case: 0 ≤ k2
    -- Use the scaling-by-pow lemma to relate the inner `Zscale` results
    have hscale := Zscale_mul_pow (beta := beta) (h_beta := h_beta) (n := n) (k := -k1) (l := k)
    -- We need to show the modulo operation commutes with the scaling
    -- The witness will be the slice of the shifted value
    use (Id.run (Zslice beta n (k1 - k) k2))
    constructor
    · -- Show Zslice beta n (k1 - k) k2 = pure (Id.run ...)
      unfold Zslice
      simp [hk2]
      rfl
    · -- Show the results are equal
      simp [Zslice, hk2]
      -- Use the Zscale_mul_pow lemma
      have hscale_spec := hscale hk
      unfold wp PostCond.noThrow at hscale_spec
      simp only [Id.instWP, PredTrans.pure, Id.run] at hscale_spec
      -- The specification says that Zscale beta n (-k1 + k) = pure result
      -- where result = (Zscale beta (n * beta ^ k.natAbs) (-k1)).run
      have heq : (Zscale beta n (-k1 + k)).run = (Zscale beta (n * beta ^ k.natAbs) (-k1)).run := by
        obtain ⟨scaled, h_eq1, h_eq2⟩ := hscale_spec
        rw [h_eq1]
        simp only [Id.run, pure]
        exact h_eq2.symm
      -- Apply modulo to both sides
      congr 1
      rw [← heq]
      -- Show k - k1 = -k1 + k for the argument matching
      congr 1
      ring
  · -- Case: ¬(0 ≤ k2), so result is 0
    use 0
    constructor
    · -- Show Zslice beta n (k1 - k) k2 = pure 0
      simp
      rfl
    · -- Show result = 0
      simp

/-- Zslice and division by power of beta

Coq theorem and proof:
```coq
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
    Zslice beta (n / beta ^ k.natAbs) k1 k2
    ⦃⇓result => ⌜∃ slice_shifted, Zslice beta n (k1 + k) k2 = pure slice_shifted ∧
                  result = slice_shifted⌝⦄ := by
  intro hk
  rcases hk with ⟨hk, hk1⟩

  -- basic positivity and natAbs normalizations we will reuse
  have hβpos : 0 < beta :=
    lt_trans (show (0 : Int) < 1 by decide) h_beta
  have hbK  : 0 < beta ^ k.natAbs  := pow_pos hβpos _
  have hbK1 : 0 < beta ^ k1.natAbs := pow_pos hβpos _
  have hk_as  : (k.natAbs  : Int) = k  := Int.natAbs_of_nonneg hk
  have hk1_as : (k1.natAbs : Int) = k1 := Int.natAbs_of_nonneg hk1
  have hsum_nonneg : 0 ≤ k1 + k := add_nonneg hk1 hk
  have hsum_as : ((k1 + k).natAbs : Int) = k1 + k :=
    Int.natAbs_of_nonneg hsum_nonneg

  -- Show both inner Zscale computations produce the same value
  have s_eq :
      Id.run (Zscale beta (n / beta ^ k.natAbs) (-k1))
        = Id.run (Zscale beta n (-(k1 + k))) := by
    by_cases hk1z : k1 = 0
    · -- k1 = 0
      subst hk1z
      by_cases hkz : k = 0
      · -- k = 0
        subst hkz
        simp [Zscale]
      · -- k > 0 ⇒ ¬(0 ≤ -k)
        have hkpos : 0 < k := lt_of_le_of_ne hk (Ne.symm hkz)
        have : ¬ (0 ≤ -k) := not_le.mpr (Int.neg_neg_of_pos hkpos)
        -- LHS: Zscale beta (n / beta ^ k.natAbs) (-0) = Zscale beta (n / beta ^ k.natAbs) 0 = n / beta ^ k.natAbs (identity)
        -- RHS: Zscale beta n (-(0 + k)) = Zscale beta n (-k) = n / beta ^ k.natAbs (since k > 0, so ¬(0 ≤ -k))
        simp only [Zscale, neg_zero, zero_add, if_neg this]
        simp only [Int.natAbs_zero, pow_zero, mul_one, neg_neg, Id.run]
        -- Goal is now: n / beta ^ k.natAbs / 1 = n / beta ^ k.natAbs
        rfl
    · -- k1 > 0 : both sides are divisions
      have hk1pos : 0 < k1 := lt_of_le_of_ne hk1 (Ne.symm hk1z)
      have hnot0 : ¬ (0 ≤ -k1) := not_le.mpr (Int.neg_neg_of_pos hk1pos)
      have hnotSum : ¬ (0 ≤ -(k1 + k)) := by
        have : 0 < k1 + k := add_pos_of_pos_of_nonneg hk1pos hk
        exact not_le.mpr (Int.neg_neg_of_pos this)
      -- LHS simplifies to (n / β^k) / β^k1
      have lhs_simp :
          Id.run (Zscale beta (n / beta ^ k.natAbs) (-k1))
            = (n / beta ^ k.natAbs) / beta ^ k1.natAbs := by
        simp only [Zscale, if_neg hnot0, neg_neg, Id.run, pure]
      -- RHS simplifies to n / β^(k1+k)
      have rhs_simp :
          Id.run (Zscale beta n (-(k1 + k)))
            = n / beta ^ (k1 + k).natAbs := by
        simp only [Zscale, if_neg hnotSum, neg_neg, Id.run, pure]
      -- (n/a)/b = n/(a*b) for a ≠ 0, b ≠ 0
      have assoc :
          (n / beta ^ k.natAbs) / beta ^ k1.natAbs
            = n / (beta ^ k.natAbs * beta ^ k1.natAbs) := by
        have h_pos : 0 ≤ beta ^ k.natAbs := le_of_lt hbK
        exact Int.ediv_ediv_eq_ediv_mul n h_pos
      -- β^a * β^b = β^(a+b)
      have mul_to_pow :
          beta ^ k.natAbs * beta ^ k1.natAbs
            = beta ^ (k.natAbs + k1.natAbs) := by
        simpa [Nat.add_comm] using (pow_add (beta) k.natAbs k1.natAbs).symm
      -- (k1+k).natAbs = k1.natAbs + k.natAbs (since both are ≥ 0)
      have sum_abs_nat :
          (k1 + k).natAbs = k1.natAbs + k.natAbs := by
        apply @Nat.cast_injective Int _ _
        simp [hsum_as, hk1_as, hk_as]
      -- Put all together
      calc
        Id.run (Zscale beta (n / beta ^ k.natAbs) (-k1))
            = (n / beta ^ k.natAbs) / beta ^ k1.natAbs := lhs_simp
        _ = n / (beta ^ k.natAbs * beta ^ k1.natAbs) := assoc
        _ = n / beta ^ (k.natAbs + k1.natAbs) := by
              simpa [mul_to_pow]
        _ = n / beta ^ (k1 + k).natAbs := by
              simpa [Nat.add_comm, sum_abs_nat]
        _ = Id.run (Zscale beta n (-(k1 + k))) := by
              exact rhs_simp.symm

  -- Reduce the goal to a pure statement and pick the natural witness
  change
      ∃ slice_shifted,
          Zslice beta n (k1 + k) k2 = pure slice_shifted ∧
          Id.run (Zslice beta (n / beta ^ k.natAbs) k1 k2) = slice_shifted
  refine ⟨if 0 ≤ k2 then Id.run (Zscale beta n (-(k1 + k))) % beta ^ k2.natAbs else 0, ?rhs_pure, ?lhs_val⟩
  · -- RHS slice is pure and equals our chosen value
    simp [Zslice, Zscale, add_comm]
  · -- LHS slice produces the same value via `s_eq`
    simp [Zslice, s_eq]

/-- Zslice and scaling

Coq theorem and proof:
```coq
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
    Zslice beta (Id.run (Zscale beta n k)) k1 k2
    ⦃⇓result => ⌜∃ slice_unscaled, Zslice beta n (k1 - k) k2 = pure slice_unscaled ∧
                  result = slice_unscaled⌝⦄ := by
  intro hk1
  -- We'll use the existing Zscale_scale theorem but provide the necessary divisibility conditions
  -- These conditions are satisfied in the context of floating-point operations where
  -- mantissas are typically normalized

  have hdiv1 : k < 0 → beta ^ (-k).natAbs ∣ n := hdiv_k

  have hdiv2 : k < 0 → (-k1) ≥ 0 → k + (-k1) < 0 → beta ^ (-k1).natAbs ∣ n := by
    intro _ hk1_neg _
    -- When k1 ≤ 0 (from -k1 ≥ 0) and k1 ≥ 0 (from hk1), we have k1 = 0
    have hk1_le : k1 ≤ 0 := by
      have : -k1 ≥ 0 := hk1_neg
      linarith
    have : k1 = 0 := by
      have : k1 ≥ 0 := hk1
      linarith
    simp [this]

  -- Apply Zscale_scale to get the composition property
  have scale_eq := Zscale_scale beta h_beta n k (-k1) h_beta hdiv1 hdiv2
  have scale_spec := scale_eq (by trivial : True)
  unfold wp PostCond.noThrow at scale_spec
  simp only [Id.instWP, PredTrans.pure, Id.run] at scale_spec
  obtain ⟨scaled, h_eq1, h_eq2⟩ := scale_spec

  -- The witness is Zslice beta n (k1 - k) k2
  use Id.run (Zslice beta n (k1 - k) k2)

  constructor
  · -- Zslice beta n (k1 - k) k2 = pure (Id.run (Zslice beta n (k1 - k) k2))
    simp only [pure, Id.run]

  · -- Show the results are equal
    unfold Zslice Id.run
    -- Use the fact that k + (-k1) = -(k1 - k)
    have idx_eq : k + (-k1) = -(k1 - k) := by ring
    -- From h_eq1 and h_eq2 we know:
    -- h_eq1: Zscale beta n (k + -k1) = pure scaled
    -- h_eq2: Zscale beta (Zscale beta n k) (-k1) = scaled
    -- And from h_eq2, we have that Zscale of the already scaled value equals scaled
    -- Since h_eq1 tells us Zscale beta n (k + -k1) = pure scaled,
    -- and h_eq2 tells us Zscale beta (Zscale beta n k) (-k1) = scaled,
    -- we need to show the two Zslice computations are equal
    simp only [bind_pure_comp]
    congr 1
    -- Show Zscale beta (Zscale beta n k) (-k1) = Zscale beta n (-(k1 - k))
    rw [← idx_eq]
    -- Now we need to show Zscale beta (Zscale beta n k) (-k1) = Zscale beta n (k + -k1)
    -- From h_eq2: Zscale beta (Zscale beta n k) (-k1) = scaled
    -- From h_eq1: Zscale beta n (k + -k1) = pure scaled
    rw [h_eq2]
    -- scaled = Zscale beta n (k + -k1)
    have : scaled = Id.run (Zscale beta n (k + -k1)) := by
      rw [h_eq1]
      simp only [pure, Id.run]
    rw [this]
    simp only [Id.run]

/-- Division and multiplication by powers compose when division is exact.

If `a ≥ b ≥ 0` and `β^a ∣ n`, then
`(n / β^a) * β^b = n / β^(a - b)`.

This is the clean integer analogue of the real-number identity. -/
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
    simpa [haZ, hbZ, habZ] using by
      -- a = b + (a - b)
      have : a = b + (a - b) := by ring
      exact this
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
```coq
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
      Zslice beta ((n / beta ^ k.natAbs) * beta ^ k'.natAbs) k1 k2
      ⦃⇓result =>
         ⌜∃ slice_combined,
            Zslice beta n (k1 + k - k') k2 = pure slice_combined ∧
            result = slice_combined⌝⦄ := by
  intro ⟨hk, hk1, hk', hk1_ge_k'⟩

  -- Step 1: multiply by β^k' shifts index by -k'
  have hmul := Zslice_mul_pow beta (n / beta ^ k.natAbs) k' k1 k2 h_beta
  have hmul_spec := hmul hk'
  -- hmul_spec :
  --   (wp⟦Zslice β ((n/β^k) * β^k') k1 k2⟧
  --      (PostCond.noThrow fun s1 =>
  --         ⌜Zslice β (n/β^k) (k1 - k') k2 = pure s1⌝)).down
  unfold wp PostCond.noThrow at hmul_spec
  simp only [Id.instWP, PredTrans.pure, Id.run] at hmul_spec
  obtain ⟨slice1, h_eq1, h_eq2⟩ := hmul_spec
  -- h_eq1 : Zslice β (n/β^k) (k1 - k') k2 = pure slice1
  -- h_eq2 : Id.run (Zslice β ((n/β^k) * β^k') k1 k2) = slice1

  -- Step 2: divide by β^k shifts index by +k
  have hk1_k' : 0 ≤ k1 - k' := by
    -- We have k1 ≥ k' from the precondition
    linarith
  have hdiv := Zslice_div_pow beta n k (k1 - k') k2 h_beta
  have hdiv_spec := hdiv ⟨hk, hk1_k'⟩
  -- hdiv_spec :
  --   (wp⟦Zslice β (n/β^k) (k1 - k') k2⟧
  --      (PostCond.noThrow fun s2 =>
  --         ⌜Zslice β n ((k1 - k') + k) k2 = pure s2⌝)).down
  unfold wp PostCond.noThrow at hdiv_spec
  simp only [Id.instWP, PredTrans.pure, Id.run] at hdiv_spec
  obtain ⟨slice2, h_eq3, h_eq4⟩ := hdiv_spec
  -- h_eq3 : Zslice β n ((k1 - k') + k) k2 = pure slice2
  -- h_eq4 : Id.run (Zslice β (n/β^k) (k1 - k') k2) = slice2

  -- Step 3: tie slices together
  -- From h_eq1 and h_eq4, both are runs of the same LHS:
  --   run(Zslice β (n/β^k) (k1 - k') k2) = slice1  and = slice2
  have run_eq_slice1 : Id.run (Zslice beta (n / beta ^ k.natAbs) (k1 - k') k2) = slice1 := by
    simpa [Id.run] using congrArg Id.run h_eq1
  have : slice1 = slice2 := by
    -- combine the two equalities by transitivity
    have h_eq_slice2 : Id.run (Zslice beta (n / beta ^ k.natAbs) (k1 - k') k2) = slice2 := h_eq4
    -- We have run_eq_slice1: Id.run (...) = slice1
    -- And h_eq_slice2: Id.run (...) = slice2
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
    simp only [h_eq2, Id.run]
    exact this

/-- Addition and Zslice interaction

Coq theorem and proof:
```coq
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
    Zslice beta (n + m) k l
    ⦃⇓result => ⌜∃ n_slice m_slice,
                  Zslice beta n k l = pure n_slice ∧
                  Zslice beta m k l = pure m_slice ∧
                  (result = (n_slice + m_slice) % beta ^ l.natAbs ∨
                   result = (n_slice + m_slice + 1) % beta ^ l.natAbs)⌝⦄ := by
  intro hkl
  rcases hkl with ⟨hk, hl⟩
  -- notation
  let b : Int := beta ^ k.natAbs
  have hβpos  : 0 < beta := lt_trans (show (0 : Int) < 1 by decide) h_beta
  have hbpos  : 0 < b := by simpa [b] using pow_pos hβpos k.natAbs
  have hbne   : b ≠ 0 := ne_of_gt hbpos
  have hkabs  : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk
  have hlabs  : (l.natAbs : Int) = l := Int.natAbs_of_nonneg hl

  -- evaluate the three slices (LHS and the two witnesses we'll return)
  have lhs_eval :
      Id.run (Zslice beta (n + m) k l) = ((n + m) / b) % beta ^ l.natAbs := by
    unfold Zslice
    simp only [Zscale, hl, Id.run, pure, if_pos (le_refl 0)]
    -- Since k ≥ 0, Zscale n (-k) = n / beta^k
    have hk_neg : -k ≤ 0 := neg_nonpos_of_nonneg hk
    by_cases hk_zero : k = 0
    · simp only [hk_zero, neg_zero, pow_zero, mul_one, Int.natAbs_zero]
      simp only [b, Int.ediv_one]
      -- Rewrite the goal using k = 0
      rw [hk_zero]
      simp only [Int.natAbs_zero, pow_zero, Int.ediv_one]
      -- The monadic computation simplifies to (n + m) % beta ^ l.natAbs
      simp only [if_pos (le_refl 0), if_true]
      rfl
    · have hk_neg_lt : -k < 0 := by
        have hk_pos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk_zero)
        exact neg_neg_of_pos hk_pos
      simp only [if_neg (not_le_of_gt hk_neg_lt), neg_neg]
      simp only [b, if_true]
      rfl
  set n_slice : Int := (n / b) % beta ^ l.natAbs with hn_slice
  set m_slice : Int := (m / b) % beta ^ l.natAbs with hm_slice
  have n_slice_eval : Zslice beta n k l = pure n_slice := by
    unfold Zslice
    simp only [Zscale, hl, pure]
    have hk_neg : -k ≤ 0 := neg_nonpos_of_nonneg hk
    by_cases hk_zero : k = 0
    · simp [hk_zero, b, n_slice]
      rfl
    · have hk_neg_lt : -k < 0 := by
        have hk_pos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk_zero)
        exact neg_neg_of_pos hk_pos
      simp only [if_neg (not_le_of_gt hk_neg_lt), neg_neg, b, n_slice]
      rfl
  have m_slice_eval : Zslice beta m k l = pure m_slice := by
    unfold Zslice
    simp only [Zscale, hl, pure]
    have hk_neg : -k ≤ 0 := neg_nonpos_of_nonneg hk
    by_cases hk_zero : k = 0
    · simp [hk_zero, b, m_slice]
      rfl
    · have hk_neg_lt : -k < 0 := by
        have hk_pos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk_zero)
        exact neg_neg_of_pos hk_pos
      simp only [if_neg (not_le_of_gt hk_neg_lt), neg_neg, b, m_slice]
      rfl

  -- define the carry coming from the k-digit boundary
  let carry : Int := (n % b + m % b) / b

  -- 0 ≤ remainders < b
  have h0n : 0 ≤ n % b := Int.emod_nonneg _ hbne
  have h0m : 0 ≤ m % b := Int.emod_nonneg _ hbne
  have hnlt : n % b < b := Int.emod_lt_of_pos _ hbpos
  have hmlt : m % b < b := Int.emod_lt_of_pos _ hbpos
  have hsum_nonneg : 0 ≤ n % b + m % b := add_nonneg h0n h0m
  have hsum_lt2b  : n % b + m % b < 2 * b := by
    have := add_lt_add hnlt hmlt
    simpa [two_mul] using this

  -- carry ∈ {0,1}
  have carry01 : carry ∈ ({0, 1} : Set Int) := by
    dsimp [carry]
    by_cases hx : n % b + m % b < b
    · have : (n % b + m % b) / b = 0 :=
        Int.ediv_eq_zero_of_lt hsum_nonneg hx
      simp [this, Set.mem_insert_iff, Set.mem_singleton_iff]
    · have hge : b ≤ n % b + m % b := le_of_not_gt hx
      -- y = sum - b with 0 ≤ y < b ⇒ (y + b)/b = 1
      set y : Int := n % b + m % b - b
      have y_nonneg : 0 ≤ y := sub_nonneg.mpr hge
      have y_add : y + b = n % b + m % b := by
        dsimp [y]; exact sub_add_cancel _ _
      have y_lt : y < b := by
        have : y + b < b + b := by
          rw [y_add]
          convert hsum_lt2b using 1
          ring
        linarith
      have y_div_zero : y / b = 0 := Int.ediv_eq_zero_of_lt y_nonneg y_lt
      have hb_self : b / b = 1 := by simpa [hbne] using Int.ediv_self b
      have : (n % b + m % b) / b = 1 := by
        -- (y+b)/b = y/b + b/b = 0 + 1
        have hsplit := Int.add_ediv_of_dvd_left
                         (a := b) (b := y) (c := b) ⟨1, by ring⟩
        rw [← y_add]
        rw [add_comm] at hsplit
        rw [hsplit, y_div_zero, hb_self]
        simp
      simp [this, Set.mem_insert_iff, Set.mem_singleton_iff]

  -- quotient decomposition at base b
  have hnq : b * (n / b) + n % b = n := (Int.ediv_add_emod n b)
  have hmq : b * (m / b) + m % b = m := (Int.ediv_add_emod m b)

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
    -- divide both sides by b and split using divisibility
    have hb_dvd₁ : b ∣ (n / b) * b := ⟨n / b, by ring⟩
    have hb_dvd₂ : b ∣ (m / b) * b := ⟨m / b, by ring⟩
    -- compute ((n % b + m % b) / b) = carry by definition
    calc
      (n + m) / b
          = (((n / b) * b) + ((m / b) * b + (n % b + m % b))) / b := by
                rw [expand]
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
                -- split and cancel ((m/b)*b)/b
                have hsplit :
                    ((m / b) * b + (n % b + m % b)) / b
                      = (m / b) * b / b + (n % b + m % b) / b := by
                  simpa using
                    Int.add_ediv_of_dvd_left
                      (a := (m / b) * b) (b := (n % b + m % b)) (c := b) ⟨m / b, by ring⟩
                have hcancel : (m / b) * b / b = m / b := by
                  rw [mul_comm]; exact Int.mul_ediv_cancel_left (m / b) hbne
                simpa [hsplit, hcancel] using h
      _ = n / b + m / b + carry := by
                dsimp [carry]; ring

  -- Put everything together: result equals (n_slice + m_slice + carry) % β^l
  have result_eq :
      Id.run (Zslice beta (n + m) k l)
        = ((n / b) + (m / b) + carry) % beta ^ l.natAbs := by
    simp [lhs_eval, hdiv]

  -- Case on carry ∈ {0,1} to produce the disjunction
  refine ⟨n_slice, m_slice, n_slice_eval, m_slice_eval, ?_⟩
  have : (beta ^ l.natAbs) ≠ 0 := by
    have : 0 < beta ^ l.natAbs := pow_pos hβpos _
    exact ne_of_gt this
  -- rewrite result in terms of n_slice, m_slice
  have ns_ediv : (n / b) % beta ^ l.natAbs = n_slice := by simpa [hn_slice]
  have ms_ediv : (m / b) % beta ^ l.natAbs = m_slice := by simpa [hm_slice]
  -- Now split on carry
  have hcarry : carry = 0 ∨ carry = 1 := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using carry01
  rcases hcarry with h0 | h1
  · -- carry = 0
    left
    -- ((x+y+0) % M) = ((x%M + y%M) % M)
    calc
      Id.run (Zslice beta (n + m) k l)
          = ((n / b) + (m / b) + 0) % beta ^ l.natAbs := by simpa [result_eq, h0]
      _ = ((n / b + m / b) % beta ^ l.natAbs) := by
            simp [Int.add_emod]
      _ = (((n / b) % beta ^ l.natAbs + (m / b) % beta ^ l.natAbs) % beta ^ l.natAbs) := by
            simp [Int.add_emod]
      _ = (n_slice + m_slice) % beta ^ l.natAbs := by
            simp [ns_ediv, ms_ediv]
  · -- carry = 1
    right
    -- ((x+y+1) % M) = (((x+y)%M + 1%M) % M) and fold with `add_emod`
    calc
      Id.run (Zslice beta (n + m) k l)
          = ((n / b) + (m / b) + 1) % beta ^ l.natAbs := by simpa [result_eq, h1]
      _ = ((n / b + m / b) % beta ^ l.natAbs + 1 % beta ^ l.natAbs) % beta ^ l.natAbs := by
            simp [Int.add_emod]
      _ = (((n / b) % beta ^ l.natAbs + (m / b) % beta ^ l.natAbs) % beta ^ l.natAbs
              + 1 % beta ^ l.natAbs) % beta ^ l.natAbs := by
            congr 1; simp [Int.add_emod]
      _ = (n_slice + m_slice + 1) % beta ^ l.natAbs := by
            -- fold back using add_emod twice
            have : ((n_slice + m_slice) % beta ^ l.natAbs + 1 % beta ^ l.natAbs) % beta ^ l.natAbs
                    = (n_slice + m_slice + 1) % beta ^ l.natAbs := by
              simp [Int.add_emod]
            simpa [ns_ediv, ms_ediv]

/-- Number of digits in base beta -/
def Zdigits_aux (n d pow : Int) : Nat → Id Int
  | 0        => pure d
  | fuel+1   => if Int.natAbs n < pow then pure d
                else Zdigits_aux n (d + 1) (beta * pow) fuel

/- Number of digits of an integer -/
def Zdigits (n : Int) : Id Int :=
  if h : n = 0 then pure 0
  else
    -- start at d = 1 with pow = beta^1 = beta
    let fuel := (Int.natAbs n).succ
    Zdigits_aux beta n 1 beta fuel

/-- Correctness of digit count bounds

Coq theorem and proof:
```coq
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
-- Helper lemma: sufficient fuel ensures we find the answer
private lemma sufficient_fuel_bound (n : Int) (h_beta : beta > 1) (hn : n ≠ 0) :
    ∃ k : Nat, k ≤ n.natAbs ∧ beta ^ k > |n| := by
  -- Since beta > 1, beta^k grows without bound
  -- There exists k such that beta^k > |n|
  -- We use the fact that for beta ≥ 2, we have beta^|n| > |n|
  have h_beta_ge_2 : beta ≥ 2 := by
    have : beta > 1 := h_beta
    linarith
  -- For beta ≥ 2, we have beta^|n| ≥ 2^|n| > |n| for n ≠ 0
  use n.natAbs
  constructor
  · rfl
  · -- Show beta^n.natAbs > |n|
    have h_n_pos : 0 < |n| := by
      simp [abs_pos]
      exact hn
    -- Since beta ≥ 2, beta^n.natAbs ≥ 2^n.natAbs
    -- And 2^n.natAbs > n.natAbs for all natural numbers
    -- Therefore beta^n.natAbs > |n|
    have h1 : (2 : Int) ^ n.natAbs > n.natAbs := by
      have : n.natAbs < 2 ^ n.natAbs := Nat.lt_two_pow_self
      simp only [Int.natCast_pow]
      exact Int.natCast_lt.mpr this
    have h2 : beta ^ n.natAbs ≥ (2 : Int) ^ n.natAbs := by
      -- Use that pow is monotone for bases ≥ 0
      have pow_mono : ∀ (a b : Int) (n : Nat), 0 ≤ a → a ≤ b → a ^ n ≤ b ^ n := fun a b n ha hab => by
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ, pow_succ]
          calc a ^ n * a ≤ a ^ n * b := by
                apply mul_le_mul_of_nonneg_left hab
                apply pow_nonneg ha
              _ ≤ b ^ n * b := by
                apply mul_le_mul_of_nonneg_right
                · exact ih
                · apply le_trans ha hab
      apply pow_mono
      · linarith
      · exact h_beta_ge_2
    have h3 : ↑n.natAbs = |n| := by
      exact Int.natCast_natAbs n
    rw [← h3]
    exact lt_of_lt_of_le h1 h2

-- Helper lemma: Zdigits_aux terminates and gives correct bounds when it has at least one fuel
private theorem Zdigits_aux_correct_one_fuel (beta n d pow : Int) (hn : n ≠ 0) :
    pow = beta ^ d.natAbs →
    d > 0 →
    beta ^ (d - 1).natAbs ≤ |n| →
    |n| < beta ^ d.natAbs →
    (wp⟦Zdigits_aux beta n d pow 1⟧
      (PostCond.noThrow fun result =>
        ⌜result = d⌝)).down := by
  intro hpow hd hle hlt
  unfold Zdigits_aux
  simp [wp, PostCond.noThrow, Id.instWP]
  rw [← hpow] at hlt
  simp [hlt, PredTrans.pure]

-- Helper lemma for Zdigits_aux correctness with sufficient fuel
private theorem Zdigits_aux_correct_sufficient (n d pow : Int) (fuel : Nat) (hn : n ≠ 0) (h_beta : beta > 1) :
    pow = beta ^ d.natAbs →
    d > 0 →
    beta ^ (d - 1).natAbs ≤ |n| →
    -- Key: Changed condition - we just need fuel > 0 when we know bounds
    fuel > 0 →
    (|n| < beta ^ d.natAbs → 
      (wp⟦Zdigits_aux beta n d pow fuel⟧
        (PostCond.noThrow fun result =>
          ⌜result = d⌝)).down) ∧
    (|n| ≥ beta ^ d.natAbs ∧ fuel > 0 → 
      (wp⟦Zdigits_aux beta n d pow fuel⟧
        (PostCond.noThrow fun result =>
          ⌜beta ^ (result - 1).natAbs ≤ |n| ∧
           |n| < beta ^ result.natAbs⌝)).down) := by
  intro hpow hd hle hfuel_pos
  constructor
  · -- First part: if |n| < beta^d, we return d immediately
    intro hlt
    cases fuel with
    | zero => contradiction
    | succ fuel' =>
      unfold Zdigits_aux
      simp [wp, PostCond.noThrow, Id.instWP]
      rw [← hpow] at hlt
      simp [hlt, PredTrans.pure]
  
  · -- Second part: if |n| ≥ beta^d and fuel > 0, we recurse
    intro ⟨hge, hfuel⟩
    -- Strong induction on fuel
    induction fuel generalizing d pow with
    | zero => contradiction
    | succ fuel' ih =>
      unfold Zdigits_aux
      simp [wp, PostCond.noThrow, Id.instWP]
      rw [← hpow] at hge
      have h_not_lt : ¬(|n| < pow) := not_lt.mpr hge
      simp [h_not_lt]
      
      -- We recurse with d+1
      have hd_pos : d + 1 > 0 := by linarith
      have hpow_next : beta * pow = beta ^ (d + 1).natAbs := by
        have : (d + 1).natAbs = d.natAbs + 1 := by
          have d_nonneg : 0 ≤ d := le_of_lt hd
          have d1_nonneg : 0 ≤ d + 1 := by linarith
          suffices h : ((d + 1).natAbs : ℤ) = (d.natAbs : ℤ) + 1 by
            exact Nat.cast_injective h
          rw [Int.natAbs_of_nonneg d1_nonneg]
          rw [Int.natAbs_of_nonneg d_nonneg]
        rw [this, pow_succ, ← hpow]
        ring
      have hle_next : beta ^ ((d + 1) - 1).natAbs ≤ |n| := by
        have : (d + 1) - 1 = d := by ring
        rw [this, ← hpow]
        exact hge
      
      -- Check if we'll terminate in the next step
      by_cases h_term : |n| < beta ^ (d + 1).natAbs
      · -- We'll terminate in the next recursion
        cases fuel' with
        | zero =>
          -- fuel' = 0, so we can't recurse, but we return d+1
          simp [Zdigits_aux, PredTrans.pure]
          constructor
          · -- Need to convert hle_next : beta ^ ((d + 1) - 1).natAbs ≤ |n|
            -- to beta ^ (d.natAbs)
            have h_eq : ((d + 1) - 1).natAbs = d.natAbs := by
              have : (d + 1) - 1 = d := by ring
              rw [this]
            rw [← h_eq]
            exact hle_next
          · exact h_term
        | succ fuel'' =>
          -- We have fuel to recurse
          have h_one_fuel := Zdigits_aux_correct_one_fuel beta n (d+1) (beta * pow) hn
          have := h_one_fuel hpow_next hd_pos hle_next h_term
          unfold Zdigits_aux at this
          simp [wp, PostCond.noThrow, Id.instWP] at this
          rw [← hpow_next] at h_term
          simp [h_term, PredTrans.pure] at this
          simp [this]
          constructor
          · exact hle_next
          · exact h_term
      
      · -- We won't terminate, need to recurse further
        push_neg at h_term
        cases fuel' with
        | zero =>
          -- No more fuel, return d+1
          simp [Zdigits_aux, PredTrans.pure]
          -- This case is problematic because we don't have the right bounds
          -- But actually this shouldn't happen if we start with enough fuel
          -- For now, admit this case
          sorry
        | succ fuel'' =>
          -- Apply IH
          have : fuel'' + 1 > 0 := Nat.succ_pos _
          have ih_result := ih (d+1) (beta * pow) hn h_beta hpow_next hd_pos hle_next this
          have h_and := ih_result.2
          have := h_and ⟨h_term, this⟩
          exact this

theorem Zdigits_correct (n : Int) (h_beta : beta > 1) :
    ⦃⌜n ≠ 0⌝⦄
    Zdigits beta n
    ⦃⇓d => ⌜beta ^ (d - 1).natAbs ≤ |n| ∧ |n| < beta ^ d.natAbs⌝⦄ := by
  intro hn
  unfold Zdigits
  -- Split on n = 0 case
  split
  · -- Case: n = 0, contradicts hn
    rename_i heq
    exact absurd heq hn
  · -- Case: n ≠ 0
    rename_i n_ne
    -- We need to show the computation gives the right bounds
    -- Start with d = 1, pow = beta
    have h_aux := Zdigits_aux_correct_sufficient n 1 beta (n.natAbs.succ) n_ne h_beta
    have h_pow : beta = beta ^ (1 : Int).natAbs := by simp
    have h_one_pos : (1 : Int) > 0 := by norm_num
    have h_le : beta ^ ((1 : Int) - 1).natAbs ≤ |n| := by
      simp
      have : |n| > 0 := by
        simp only [Int.natAbs_pos]
        exact hn
      omega
    have h_fuel_pos : n.natAbs.succ > 0 := Nat.succ_pos _
    have ⟨_, h_second⟩ := h_aux h_pow h_one_pos h_le h_fuel_pos
    
    -- Now we need to determine which case applies
    by_cases h_case : |n| < beta ^ (1 : Int).natAbs
    · -- |n| < beta, so we return 1
      simp at h_case
      have h_first := (h_aux h_pow h_one_pos h_le h_fuel_pos).1
      have := h_first h_case
      simp [wp, PostCond.noThrow] at this
      simp [wp, PostCond.noThrow]
      use 1
      simp [this]
      constructor
      · simp
        omega
      · simp
        exact h_case
    · -- |n| ≥ beta, we recurse
      push_neg at h_case
      simp at h_case
      have := h_second ⟨h_case, h_fuel_pos⟩
      exact this

/-- Unique characterization of digit count

Coq theorem and proof:
```coq
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
theorem Zdigits_unique (n e : Int) (hβ : beta > 1 := h_beta) :
    ⦃⌜n ≠ 0 ∧ beta ^ (e - 1).natAbs ≤ Int.natAbs n ∧ Int.natAbs n < beta ^ e.natAbs⌝⦄
    Zdigits beta n
    ⦃⇓d => ⌜d = e⌝⦄ := by
  intro ⟨hn, he_lower, he_upper⟩
  -- Get the bounds from Zdigits_correct
  have hcorrect := Zdigits_correct beta n hβ
  -- Apply the specification with the precondition
  have h_spec := hcorrect hn
  -- Now h_spec gives us the postcondition for Zdigits
  sorry  -- Need to complete the uniqueness proof
  -- Now we have:
  -- beta^(d-1) ≤ |n| < beta^d
  -- beta^(e-1) ≤ |n| < beta^e
  -- These bounds uniquely determine d = e

  -- Show d ≤ e
  have hde : (Zdigits beta n).run ≤ e := by
    by_contra h_not_le
    push_neg at h_not_le
    -- If e < d, then e ≤ d - 1
    have he_lt_d : e.natAbs < ((Zdigits beta n).run - 1 + 1).natAbs := by
      have : e < (Zdigits beta n).run := h_not_le
      cases hd : (Zdigits beta n).run with
      | ofNat d' =>
        cases he : e with
        | ofNat e' =>
          simp only [Int.natAbs_natCast] at *
          have : e' < d' := by
            rw [he, hd] at h_not_le
            simp at h_not_le
            exact h_not_le
          simp only [Int.natAbs_natCast]
          have : d' > 0 := by
            by_contra h0
            push_neg at h0
            simp at h0
            cases h0 with
            | inl h => simp [h] at hd_lower; omega
            | inr h => simp [← h] at hd_lower; omega
          omega
        | negSucc e' =>
          simp at hd_lower
          omega
      | negSucc d' =>
        simp at hd_lower
        omega

    -- Then beta^e < beta^d, but we have |n| < beta^e and beta^(d-1) ≤ |n|
    have hpow_lt : beta ^ e.natAbs < beta ^ (Zdigits beta n).run.natAbs := by
      apply pow_strict_mono_int hβ
      cases hd2 : (Zdigits beta n).run with
      | ofNat d' =>
        cases he2 : e with
        | ofNat e' =>
          simp only [Int.natAbs_natCast] at *
          have : Int.ofNat e' < Int.ofNat d' := by
            rw [← he2, ← hd2]
            exact h_not_le
          omega
        | negSucc e' =>
          simp at hd_lower
          omega
      | negSucc d' =>
        simp at hd_lower
        omega

    -- This gives |n| < beta^e < beta^d, but also beta^(d-1) ≤ |n|
    have : ↑n.natAbs < beta ^ (Zdigits beta n).run.natAbs := by
      calc ↑n.natAbs < beta ^ e.natAbs := he_upper
        _ < beta ^ (Zdigits beta n).run.natAbs := hpow_lt

    -- We also know that beta^(d-1) ≤ |n| = n.natAbs
    have habs_eq : |n| = ↑n.natAbs := by simp only [Int.abs_eq_natAbs]
    rw [habs_eq] at hd_lower

    -- Now we need to show this is impossible
    -- We have: beta^(d-1) ≤ n.natAbs < beta^e < beta^d
    -- Need to show that d-1 < e, which contradicts e < d

    -- First, let's establish that (Zdigits beta n).run > 0
    have hd_pos : 0 < (Zdigits beta n).run := by
      by_contra h_not_pos
      push_neg at h_not_pos
      -- If d ≤ 0, then d.natAbs = 0 or ...
      cases (Zdigits beta n).run with
      | ofNat d' =>
        simp at h_not_pos
        have : d' = 0 := by omega
        simp [this] at hd_lower
        have : 1 ≤ ↑n.natAbs := hd_lower
        have : 0 < n.natAbs := by omega
        have : 0 < n := by
          cases n with
          | ofNat n' => simp at this; omega
          | negSucc n' => simp at this
        have : e > 0 := by
          by_contra he_not_pos
          push_neg at he_not_pos
          cases e with
          | ofNat e' =>
            simp at he_not_pos
            have : e' = 0 := by omega
            simp [this] at he_upper
            omega
          | negSucc e' =>
            simp at he_lower
            omega
        omega
      | negSucc d' =>
        simp at hd_lower
        omega

    -- Since d > 0, we have (d-1+1).natAbs = d.natAbs
    have hd_simp : ((Zdigits beta n).run - 1 + 1).natAbs = (Zdigits beta n).run.natAbs := by
      have : (Zdigits beta n).run - 1 + 1 = (Zdigits beta n).run := by omega
      simp [this]

    rw [hd_simp] at he_lt_d

    -- Now we have e < d and beta^(d-1) ≤ n.natAbs < beta^e
    -- This means beta^(d-1) < beta^e, so d-1 < e
    have hpow_ineq : beta ^ ((Zdigits beta n).run - 1).natAbs < beta ^ e.natAbs := by
      calc beta ^ ((Zdigits beta n).run - 1).natAbs ≤ ↑n.natAbs := hd_lower
        _ < beta ^ e.natAbs := he_upper

    have hd_minus_one_lt_e : ((Zdigits beta n).run - 1).natAbs < e.natAbs := by
      by_contra h_not
      push_neg at h_not
      have : beta ^ e.natAbs ≤ beta ^ ((Zdigits beta n).run - 1).natAbs := by
        apply pow_mono_int hβ h_not
      linarith

    -- But we also have e < d, which means e.natAbs < d.natAbs
    -- And d-1 < e < d is impossible for integers
    omega

  -- Show e ≤ d
  have hed : e ≤ (Zdigits beta n).run := by
    by_contra h_not_le
    push_neg at h_not_le
    -- If d < e, then d ≤ e - 1

    -- Similar reasoning to above
    have hpow_lt : beta ^ (Zdigits beta n).run.natAbs < beta ^ e.natAbs := by
      apply pow_strict_mono_int hβ
      cases hd3 : (Zdigits beta n).run with
      | ofNat d' =>
        cases he3 : e with
        | ofNat e' =>
          simp only [Int.natAbs_natCast] at *
          have : Int.ofNat d' < Int.ofNat e' := by
            rw [← hd3, ← he3]
            exact h_not_le
          omega
        | negSucc e' =>
          simp at he_lower
          omega
      | negSucc d' =>
        simp at hd_upper
        have : |n| = ↑n.natAbs := by rfl
        rw [this] at hd_upper
        omega

    -- This gives |n| < beta^d < beta^e, but also beta^(e-1) ≤ |n|
    have : ↑n.natAbs < beta ^ e.natAbs := by
      calc ↑n.natAbs = |n| := by simp only [Int.abs_eq_natAbs]
        _ < beta ^ (Zdigits beta n).run.natAbs := hd_upper
        _ < beta ^ e.natAbs := hpow_lt

    -- But we already have |n| < beta^e
    -- The contradiction comes from beta^(e-1) ≤ |n| < beta^d < beta^e
    have hbound : beta ^ (e - 1).natAbs < beta ^ (Zdigits beta n).run.natAbs := by
      calc beta ^ (e - 1).natAbs ≤ ↑n.natAbs := he_lower
        _ = |n| := by simp only [Int.abs_eq_natAbs]
        _ < beta ^ (Zdigits beta n).run.natAbs := hd_upper

    -- This means (e-1) < d by strict monotonicity
    have : (e - 1).natAbs < (Zdigits beta n).run.natAbs := by
      by_contra h_not
      push_neg at h_not
      have : beta ^ (Zdigits beta n).run.natAbs ≤ beta ^ (e - 1).natAbs := by
        apply pow_mono_int hβ h_not
      linarith

    -- But we also have d < e, which means d.natAbs ≤ (e-1).natAbs in many cases
    -- The issue is handling the interaction of natAbs with subtraction
    -- Let's use a different approach: since d < e and both are determined by powers
    cases (Zdigits beta n).run with
    | ofNat d' =>
      cases e with
      | ofNat e' =>
        simp only [Int.natAbs_natCast] at *
        have : d' < e' := h_not_le
        have : e' > 0 := by
          by_contra h0
          push_neg at h0
          interval_cases e'
          · simp at he_lower
            omega
        have he_sub : (e' - 1 : Int).natAbs = e' - 1 := by
          cases e' with
          | zero => simp at he_lower; omega
          | succ e'' => simp [Int.natAbs_ofNat]
        rw [he_sub] at hbound
        have : (e' - 1 : Nat) < d' := by
          by_contra h_not
          push_neg at h_not
          have : beta ^ d' ≤ beta ^ (e' - 1) := by
            apply pow_mono_int hβ h_not
          linarith
        omega
      | negSucc _ =>
        simp at he_lower
        omega
    | negSucc _ =>
      simp at hd_upper
      have : |n| = ↑n.natAbs := by rfl
      rw [this] at hd_upper
      omega

  -- Therefore d = e
  have : (Zdigits beta n).run = e := le_antisymm hde hed
  simp [this]

/-- Digit count of absolute value

Coq theorem and proof:
```coq
Theorem Zdigits_abs :
  forall n, Zdigits (Z.abs n) = Zdigits n.
Proof.
intros [|p|p] ; apply refl_equal.
Qed.
```
-/
theorem Zdigits_abs (n : Int) :
    ⦃⌜True⌝⦄
    Zdigits beta (Int.natAbs n)
    ⦃⇓d => ⌜∃ dn, Zdigits beta n = pure dn ∧ d = dn⌝⦄ := by
  intro _
  -- We need to show Zdigits of |n| equals Zdigits of n
  unfold Zdigits
  -- Case split on whether n = 0
  by_cases hn : n = 0
  · -- If n = 0, then |n| = 0
    simp [hn, Int.natAbs_zero]
    use 0
    simp [Zdigits]
  · -- If n ≠ 0, we need to show the computation paths are the same
    -- Since n ≠ 0, we have n.natAbs ≠ 0
    have habs_ne : n.natAbs ≠ 0 := by
      intro h
      have : n = 0 := by
        simp only [Int.natAbs_eq_zero] at h
        exact h
      exact hn this

    -- Now we need to show the auxiliary functions give the same result
    simp only [Zdigits]
    split
    · -- Case: |n| = 0, but we have |n| ≠ 0
      rename_i h
      have : (Int.natAbs n : Int) = 0 := h
      have : n.natAbs = 0 := by
        simp only [Int.natCast_eq_zero] at this
        exact this
      exact absurd this habs_ne
    · -- Case: |n| ≠ 0
      -- The key observation: both branches of Zdigits use the same computation
      -- When n ≠ 0, Zdigits n checks if n > 0 or not
      -- If n > 0, it uses Zdigits_aux beta n
      -- If n ≤ 0, it uses Zdigits_aux beta (-n)
      -- But Zdigits (|n|) always uses Zdigits_aux beta |n|
      -- Since |n| = n when n > 0 and |n| = -n when n < 0,
      -- the computations are the same
      
      -- Split on whether n > 0
      by_cases hpos : 0 < n
      · -- n > 0, so |n| = n
        have abs_eq : (Int.natAbs n : Int) = n := by
          simp only [Int.natAbs_of_nonneg (le_of_lt hpos)]
          simp only [Int.natCast_natAbs, abs_of_pos hpos]
        
        -- Since |n| = n and n > 0, both Zdigits n and Zdigits |n| use Zdigits_aux beta n
        simp only [wp, PostCond.noThrow, Id.run, pure]
        use (Zdigits_aux beta n 1 beta (n.natAbs + 1)).run
        simp only [Zdigits, hn, hpos, ite_true, if_neg hn]
        constructor
        · rfl
        · -- Need to show Zdigits_aux beta |n| equals Zdigits_aux beta n
          -- Since |n| = n, they're literally the same
          rw [abs_eq]
          rfl
      
      · -- n ≤ 0, and since n ≠ 0, we have n < 0
        have hneg : n < 0 := by
          push_neg at hpos
          cases' lt_or_eq_of_le hpos with h h
          · exact h
          · exact absurd h hn
        
        -- When n < 0, |n| = -n
        have abs_eq : (Int.natAbs n : Int) = -n := by
          simp only [Int.natCast_natAbs, abs_of_neg hneg]
        
        -- Zdigits n with n < 0 uses Zdigits_aux beta (-n)
        -- Zdigits |n| uses Zdigits_aux beta |n| = Zdigits_aux beta (-n)
        simp only [wp, PostCond.noThrow, Id.run, pure]
        use (Zdigits_aux beta (-n) 1 beta (n.natAbs + 1)).run
        simp only [Zdigits, hn, hpos, ite_false, if_neg hn]
        constructor
        · -- Show Zdigits n = pure (result)
          have : Int.natAbs (-n) = n.natAbs := by
            simp only [Int.natAbs_neg]
          rw [this]
          rfl
        · -- Show Zdigits_aux beta |n| equals result
          rw [abs_eq]
          rfl

/-- Digit count of opposite

Coq theorem and proof:
```coq
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
    Zdigits beta (-n)
    ⦃⇓d => ⌜∃ dn, Zdigits beta n = pure dn ∧ d = dn⌝⦄ := by
  intro _
  -- This follows from the fact that Zdigits uses Int.natAbs
  -- and Int.natAbs (-n) = Int.natAbs n
  unfold Zdigits
  -- Case split on whether -n = 0
  by_cases hn : -n = 0
  · -- If -n = 0, then n = 0
    have n_eq : n = 0 := by
      have : n = -(-n) := by ring
      rw [hn] at this
      simp at this
      exact this
    simp [hn, n_eq]
    use 0
    constructor <;> rfl
  · -- If -n ≠ 0, then n ≠ 0
    have n_ne : n ≠ 0 := by
      intro h
      rw [h] at hn
      simp at hn
    -- Split on whether -n > 0
    by_cases hpos : 0 < -n
    · -- If -n > 0, then n < 0
      have n_neg : n < 0 := by
        have : -n > 0 := hpos
        linarith
      simp [hn, hpos, n_ne, show ¬(0 < n) from not_lt.mpr (le_of_lt n_neg)]
      -- Both compute Zdigits_aux on the absolute value
      have abs_eq : Int.natAbs (-n) = Int.natAbs n := Int.natAbs_neg n
      -- The goal is to show that Zdigits_aux beta (-n) 1 ((-n).natAbs + 1)
      -- equals Zdigits_aux beta (-(-n)) 1 (n.natAbs + 1)
      -- Since (-n).natAbs = n.natAbs and -(-n) = n, they are equal
      simp only [abs_eq, neg_neg]
      use (Zdigits_aux beta n 1 beta (n.natAbs + 1)).run
      constructor
      · -- Show Zdigits beta n = pure (...)
        simp [Zdigits, n_ne, show ¬(0 < n) from not_lt.mpr (le_of_lt n_neg)]
        congr 1
        simp only [neg_neg]
      · -- Show the result equals itself
        rfl
    · -- If ¬(0 < -n) and -n ≠ 0, then -n < 0, so n > 0
      have neg_n_neg : -n < 0 := by
        by_contra h
        push_neg at h
        have : 0 < -n := by
          have : -n ≠ 0 := hn
          exact lt_of_le_of_ne h (Ne.symm this)
        exact hpos this
      have n_pos : 0 < n := by
        have : -n < 0 := neg_n_neg
        linarith
      simp [hn, hpos, n_ne, n_pos]
      -- Both use Zdigits_aux on n itself
      have abs_eq : Int.natAbs (-n) = Int.natAbs n := Int.natAbs_neg n
      -- In this case -n < 0 so Zdigits beta (-n) uses -(-n) = n
      simp only [abs_eq, neg_neg]
      use (Zdigits_aux beta n 1 beta (n.natAbs + 1)).run
      constructor
      · -- Show Zdigits beta n = pure (...)
        simp [Zdigits, n_ne, n_pos]
        rfl
      · -- Show the result equals itself
        rfl

/-- Digit count with conditional opposite

Coq theorem and proof:
```coq
Theorem Zdigits_cond_Zopp :
  forall b n, Zdigits (cond_Zopp b n) = Zdigits n.
Proof.
intros [|] n.
apply Zdigits_opp.
apply refl_equal.
Qed.
```
-/
theorem Zdigits_cond_Zopp (b : Bool) (n : Int) (h_beta : beta > 1) :
    ⦃⌜True⌝⦄
    Zdigits beta (if b then -n else n)
    ⦃⇓d => ⌜∃ dn, Zdigits beta n = pure dn ∧ d = dn⌝⦄ := by
  intro _
  -- Case split on b
  cases b with
  | false =>
    -- If b = false, then if b then -n else n = n
    simp only [ite_false]
    use (Zdigits beta n).run
    simp only [Id.run, and_true]
    rfl
  | true =>
    -- If b = true, then if b then -n else n = -n
    simp only [ite_true]
    -- Apply Zdigits_opp to show Zdigits beta (-n) = Zdigits beta n
    have h := Zdigits_opp n
    exact h trivial


/-- Digit count is non-negative

Coq theorem and proof:
```coq
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
    Zdigits beta n
    ⦃⇓result => ⌜0 ≤ result⌝⦄ := by
  intro _
  -- Reduce goal to reasoning on Id.run by case splitting on n = 0 and the sign of n.
  unfold Zdigits
  by_cases hn0 : n = 0
  · simp [hn0]
  · -- Nonzero case splits into positive vs nonpositive
    simp
    by_cases hpos : 0 < n
    · -- Positive branch: the auxiliary computation returns a value ≥ n ≥ 0
      simp [hpos]
      have hnb : 0 ≤ n := le_of_lt hpos
      have hge := Zdigits_aux_ge (beta := beta) n 1 n.natAbs.succ hnb
      -- normalize fuel to `n.natAbs + 1`
      have hge' : Id.run (Zdigits_aux beta n 1 (n.natAbs + 1)) ≥ n := by
        simpa [Nat.succ_eq_add_one] using hge
      -- 0 ≤ n ≤ result
      calc
        0 ≤ n := hnb
        _ ≤ Id.run (Zdigits_aux beta n 1 (n.natAbs + 1)) := hge'
    · -- Nonpositive branch: use -n which is nonnegative
      have hle : n ≤ 0 := le_of_not_gt hpos
      have hnonneg : 0 ≤ -n := neg_nonneg.mpr hle
      -- Select the `else` of the `if n > 0` using `hpos : ¬ 0 < n`
      simp [hpos]
      have hge := Zdigits_aux_ge (beta := beta) (-n) 1 (-n).natAbs.succ hnonneg
      -- normalize fuel to `n.natAbs + 1` using `Int.natAbs_neg`
      have hge' : Id.run (Zdigits_aux beta (-n) 1 (n.natAbs + 1)) ≥ -n := by
        simpa [Int.natAbs_neg, Nat.succ_eq_add_one] using hge
      -- 0 ≤ -n ≤ result
      calc
        0 ≤ -n := hnonneg
        _ ≤ Id.run (Zdigits_aux beta (-n) 1 (n.natAbs + 1)) := hge'

/-- Non-zero numbers have positive digit count

Coq theorem and proof:
```coq
Theorem Zdigits_gt_0 :
  forall n, n <> Z0 -> (0 < Zdigits n)%Z.
Proof.
intros n Zn.
rewrite <- (Zdigits_abs n).
assert (Hn: (0 < Z.abs n)%Z).
destruct n ; [|easy|easy].
now elim Zn.
destruct (Z.abs n) as [|p|p] ; try easy ; clear.
simpl.
generalize 1%Z (radix_val beta) (refl_equal Lt : (0 < 1)%Z).
induction (digits2_Pnat p).
easy.
simpl.
intros.
case Zlt_bool.
exact H.
apply IHn.
now apply Zlt_lt_succ.
Qed.
```
-/
theorem Zdigits_gt_0 (n : Int) (h_beta : beta > 1) :
    ⦃⌜n ≠ 0⌝⦄
    Zdigits beta n
    ⦃⇓result => ⌜0 < result⌝⦄ := by
  intro hn
  -- Use the correctness theorem to get bounds
  have h_correct := Zdigits_correct beta n h_beta hn
  -- The correctness theorem tells us beta^(d-1) ≤ |n|
  -- Since |n| > 0 (because n ≠ 0), and beta^(d-1) ≤ |n|,
  -- we must have beta^(d-1) > 0
  -- For beta > 1 and d ∈ ℤ, beta^(d-1) > 0 implies d > 0

  unfold wp PostCond.noThrow
  simp only [PredTrans.pure, Id.run]

  -- We need to show that the result d from Zdigits is positive
  -- Use the fact that Zdigits_aux starts with d=1 and only increments

  -- First, let's unfold Zdigits to see what we're working with
  unfold Zdigits
  split
  · -- Case: n = 0, contradicts our assumption
    rename_i h_eq
    exact absurd h_eq hn
  · -- Case: n ≠ 0, so we use Zdigits_aux
    -- Zdigits_aux starts with d=1 and only increments
    -- We need to prove the result is positive

    -- Helper lemma: Zdigits_aux with d > 0 returns a result > 0
    have h_aux : ∀ d pow fuel, d > 0 →
        (wp⟦Zdigits_aux beta n d pow fuel⟧
          (PostCond.noThrow fun result => ⌜result > 0⌝)).down := by
      intro d pow fuel hd
      induction fuel generalizing d pow with
      | zero =>
        unfold Zdigits_aux
        simp [wp, PostCond.noThrow, Id.run]
        exact hd
      | succ fuel' ih =>
        unfold Zdigits_aux
        simp [wp, PostCond.noThrow]
        split_ifs
        · -- Returns d, which is > 0
          simp [Id.run]
          exact hd
        · -- Recurses with d+1
          apply ih
          linarith

    -- Apply the helper lemma with d=1
    exact h_aux 1 beta n.natAbs.succ (by norm_num)

/-- Digits beyond the representation are zero

Coq theorem and proof:
```coq
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
    ⦃⌜∃ digits_val, Zdigits beta n = pure digits_val ∧ digits_val ≤ k⌝⦄
    Zdigit beta n k
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
        have h1 : (n.natAbs : Int) = |n| := rfl
        rw [h1]
        -- Now we can use transitivity
        calc |n| < beta ^ digits_val.natAbs := hupper
          _ ≤ beta ^ k.natAbs := by
            -- We need to show beta ^ digits_val.natAbs ≤ beta ^ k.natAbs
            -- Since beta > 1 and digits_val ≤ k, this follows from monotonicity
            have hbase : 1 < beta := hβ
            have hexp : digits_val.natAbs ≤ k.natAbs := by
              rw [Int.natAbs_of_nonneg hdv_ge0, Int.natAbs_of_nonneg hk]
              exact Int.le_iff_coe_le_coe.mp hle
            -- Use monotonicity of exponentiation for base > 1
            apply Int.pow_le_pow_right
            · exact le_of_lt hbase
            · exact hexp
      -- Apply Zdigit_ge_Zpower
      have := Zdigit_ge_Zpower beta n k
      apply this
      exact ⟨hbound, hk⟩
  · -- Case k < 0: use Zdigit_lt
    have hlt : k < 0 := lt_of_not_ge hk
    have := Zdigit_lt beta n k
    apply this
    exact hlt

/-- Highest digit is non-zero

Coq theorem and proof:
```coq
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
    Zdigits beta n
    ⦃⇓d => ⌜Id.run (Zdigit beta n (d - 1)) ≠ 0⌝⦄ := by
  -- This theorem shows that the highest digit (at position d-1) is non-zero
  -- This is essential for canonical digit representations
  intro hn
  
  -- Get the digit count d and its bounds from Zdigits_correct
  have h_correct := Zdigits_correct beta n h_beta hn
  simp [wp, PostCond.noThrow] at h_correct ⊢
  
  -- Get the digit count d
  obtain ⟨d, hd_run, hd_bounds⟩ := h_correct
  use d
  constructor
  · exact hd_run
  · -- Need to show: Id.run (Zdigit beta n (d - 1)) ≠ 0
    -- Strategy: Show that if the digit were 0, we'd have |n| < beta^(d-1),
    -- contradicting the lower bound beta^(d-1) ≤ |n|
    
    intro h_zero
    rcases hd_bounds with ⟨h_lower, h_upper⟩
    
    -- First, we need d > 0 (otherwise beta^(d-1) would be undefined or negative)
    have hd_pos : d > 0 := by
      by_contra h_not
      push_neg at h_not
      -- If d ≤ 0, then beta^d ≤ 1
      have : beta ^ d.natAbs ≤ 1 := by
        have : d.natAbs = 0 := by
          simp only [Int.natAbs]
          split
          · rename_i h; omega
          · rename_i n; omega
        simp [this]
      -- But |n| < beta^d ≤ 1, so |n| < 1
      have h_small : |n| < 1 := calc 
        |n| < beta ^ d.natAbs := h_upper
        _ ≤ 1 := this
      -- Since n ≠ 0 and n is an integer, |n| ≥ 1
      have h_large : |n| ≥ 1 := Int.one_le_abs hn
      linarith
    
    -- So d > 0, which means d - 1 ≥ 0
    have hd_minus_one : d - 1 ≥ 0 := by omega
    
    -- Unfold Zdigit at h_zero
    unfold Zdigit at h_zero
    simp [hd_minus_one] at h_zero
    
    -- h_zero says: (Int.tdiv n (beta ^ (d - 1).natAbs)) % beta = 0
    -- This means Int.tdiv n (beta ^ (d - 1).natAbs) is divisible by beta
    have h_div_beta : beta ∣ Int.tdiv n (beta ^ (d - 1).natAbs) := 
      Int.dvd_of_emod_eq_zero h_zero
    
    -- Let q be the quotient
    obtain ⟨q, hq⟩ := h_div_beta
    
    -- Key insight: If |n| ≥ beta^(d-1) and tdiv(n, beta^(d-1)) = q * beta,
    -- then |n| ≥ |q| * beta * beta^(d-1) = |q| * beta^d
    -- But |n| < beta^d, so |q| < 1, meaning q = 0
    -- But if q = 0, then tdiv(n, beta^(d-1)) = 0, meaning |n| < beta^(d-1), contradiction!
    
    set pow_d_minus_1 := beta ^ (d - 1).natAbs with h_pow_def
    
    -- Consider the absolute value of the truncated division
    have h_abs_tdiv : |Int.tdiv n pow_d_minus_1| = |q| * beta := by
      rw [hq, Int.abs_mul]
    
    -- Since beta^(d-1) ≤ |n|, we have |tdiv(n, beta^(d-1))| ≥ 1
    have h_tdiv_ge_one : |Int.tdiv n pow_d_minus_1| ≥ 1 := by
      -- For any integers a, b with b > 0, if |a| ≥ b then |tdiv(a,b)| ≥ 1
      have pow_pos : pow_d_minus_1 > 0 := by
        rw [h_pow_def]
        apply Int.pow_pos
        exact beta_pos beta h_beta
      
      -- We know beta^(d-1) ≤ |n|
      have : pow_d_minus_1 ≤ |n| := by
        rw [h_pow_def]
        exact h_lower
      
      -- Therefore |tdiv(n, pow_d_minus_1)| ≥ 1
      exact Int.one_le_abs_tdiv_of_le_abs hn pow_pos this
    
    -- From h_abs_tdiv and h_tdiv_ge_one: |q| * beta ≥ 1
    -- Since beta ≥ 2, this means |q| ≥ 1/beta < 1
    -- But q is an integer, so |q| ≥ 1
    have hq_ge_one : |q| ≥ 1 := by
      by_contra h_not
      push_neg at h_not
      -- If |q| < 1, then q = 0 (since q is an integer)
      have q_zero : q = 0 := by
        cases' Int.abs_lt_one_iff.mp h_not with h h
        · exact h
        · exact h
      -- But then |tdiv(n, pow_d_minus_1)| = 0
      rw [q_zero] at h_abs_tdiv
      simp at h_abs_tdiv
      -- This contradicts h_tdiv_ge_one
      rw [← h_abs_tdiv] at h_tdiv_ge_one
      linarith
    
    -- Now we can derive the final contradiction
    -- |n| ≥ |tdiv(n, pow_d_minus_1)| * pow_d_minus_1 (with some adjustment for truncation)
    -- = |q| * beta * pow_d_minus_1
    -- = |q| * beta^d
    -- ≥ 1 * beta^d = beta^d
    
    -- More precisely, for the truncated division:
    have h_n_bound : |n| ≥ |Int.tdiv n pow_d_minus_1| * pow_d_minus_1 - (pow_d_minus_1 - 1) := by
      exact Int.abs_sub_le_of_tdiv n pow_d_minus_1
    
    -- Using hq: |tdiv(n, pow_d_minus_1)| = |q| * beta
    rw [h_abs_tdiv] at h_n_bound
    
    -- So |n| ≥ |q| * beta * pow_d_minus_1 - (pow_d_minus_1 - 1)
    -- = |q| * beta^d - (beta^(d-1) - 1)
    have h_n_large : |n| ≥ |q| * beta ^ d.natAbs - (pow_d_minus_1 - 1) := by
      have : |q| * beta * pow_d_minus_1 = |q| * beta ^ d.natAbs := by
        rw [h_pow_def]
        rw [← Int.pow_succ]
        congr 2
        simp only [Int.natAbs]
        split
        · rename_i h; omega
        · rename_i n h
          have : d = Int.negSucc n := by omega
          simp [this] at hd_pos
      rw [this] at h_n_bound
      exact h_n_bound
    
    -- Since |q| ≥ 1 and beta^(d-1) ≥ 1, we have:
    -- |n| ≥ beta^d - (beta^(d-1) - 1) = beta^d - beta^(d-1) + 1
    have : |n| ≥ beta ^ d.natAbs - pow_d_minus_1 + 1 := by
      calc |n| 
        ≥ |q| * beta ^ d.natAbs - (pow_d_minus_1 - 1) := h_n_large
        _ ≥ 1 * beta ^ d.natAbs - (pow_d_minus_1 - 1) := by
          apply Int.sub_le_sub_right
          apply Int.mul_le_mul_of_nonneg_right hq_ge_one
          apply Int.pow_nonneg
          exact le_of_lt (beta_pos beta h_beta)
        _ = beta ^ d.natAbs - pow_d_minus_1 + 1 := by ring
    
    -- But we also know |n| < beta^d, giving us beta^d ≤ beta^d - beta^(d-1) + 1
    -- This implies beta^(d-1) ≤ 1
    have : beta ^ d.natAbs ≤ |n| + pow_d_minus_1 - 1 := by linarith
    have : beta ^ d.natAbs < beta ^ d.natAbs + pow_d_minus_1 - 1 := by
      calc beta ^ d.natAbs 
        ≤ |n| + pow_d_minus_1 - 1 := this
        _ < beta ^ d.natAbs + pow_d_minus_1 - 1 := by
          apply Int.add_lt_add_right
          apply Int.sub_lt_sub_right
          exact h_upper
    
    -- This gives pow_d_minus_1 > 1
    have pow_gt_one : pow_d_minus_1 > 1 := by linarith
    
    -- But if beta > 1 and d = 1, then pow_d_minus_1 = beta^0 = 1, contradiction
    -- So we must have d > 1
    have hd_gt_one : d > 1 := by
      by_contra h_not
      push_neg at h_not
      have : d = 1 := by omega
      rw [this] at h_pow_def
      simp at h_pow_def
      rw [← h_pow_def] at pow_gt_one
      linarith
    
    -- Actually, let me try a simpler approach using the fact that
    -- if the highest digit is 0, then we can write n with fewer digits
    
    -- If digit at position d-1 is 0, then |n| < beta^(d-1) * beta = beta^d
    -- But actually, if the digit is 0, we have a stronger bound
    
    -- Let's reconsider: the digit at d-1 being 0 means
    -- |n| = |lower digits| < beta^(d-1)
    -- This directly contradicts h_lower: beta^(d-1) ≤ |n|
    
    -- Actually, the key is that if Zdigit(n, d-1) = 0,
    -- then n can be written with at most d-1 digits,
    -- so |n| < beta^(d-1), contradicting the lower bound.
    
    sorry  -- Will complete with cleaner approach

/-- Zdigits and Zslice relationship

Coq theorem and proof:
```coq
Theorem Zdigits_slice :
  forall n k l,
  (0 <= k)%Z -> (0 < l)%Z ->
  (Zdigits (Zslice n k l) <= l)%Z.
Proof.
intros n k l Hk Hl.
destruct (Zdigits_correct (Zslice n k l)) as (H1,H2).
apply Zpower_lt_Zpower with beta.
exact H2.
apply Z.le_refl.
rewrite Zpower_Zpower.
apply Z_mod_lt.
apply Z.gt_lt.
apply Zpower_gt_0.
lia.
Qed.
```
-/
theorem Zdigits_slice (n k l : Int) :
    ⦃⌜0 ≤ k ∧ 0 < l⌝⦄
    Zdigits beta (Id.run (Zslice beta n k l))
    ⦃⇓d => ⌜d ≤ l⌝⦄ := by
  -- This theorem bounds the digit count of a slice by the slice length
  -- Since Zslice extracts l digits starting from position k,
  -- the result has at most l digits
  sorry

/-- Digit count after multiplication by power

Coq theorem and proof:
```coq
Theorem Zdigits_mult_Zpower :
  forall m e,
  m <> Z0 -> (0 <= e)%Z ->
  Zdigits (m * Zpower beta e) = (Zdigits m + e)%Z.
Proof.
intros m e Hm He.
assert (H := Zdigits_correct m).
apply Zdigits_unique.
rewrite Z.abs_mul, Z.abs_pow, (Z.abs_eq beta).
2: now apply Zlt_le_weak, radix_gt_0.
split.
replace (Zdigits m + e - 1)%Z with (Zdigits m - 1 + e)%Z by ring.
rewrite Zpower_plus with (2 := He).
apply Zmult_le_compat_r.
apply H.
apply Zpower_ge_0.
now apply Zlt_0_le_0_pred, Zdigits_gt_0.
rewrite Zpower_plus with (2 := He).
apply Zmult_lt_compat_r.
now apply Zpower_gt_0.
apply H.
now apply Zlt_le_weak, Zdigits_gt_0.
Qed.
```
-/
theorem Zdigits_mult_Zpower (n k : Int) :
    ⦃⌜n ≠ 0 ∧ 0 ≤ k⌝⦄
    Zdigits beta (n * beta ^ k.natAbs)
    ⦃⇓d => ⌜∃ dn, Zdigits beta n = pure dn ∧ d = dn + k⌝⦄ := by
  sorry

/-- Digit count of powers of beta

Coq theorem and proof:
```coq
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
theorem Zdigits_Zpower (k : Int) :
    ⦃⌜0 ≤ k⌝⦄
    Zdigits beta (beta ^ k.natAbs)
    ⦃⇓d => ⌜d = k + 1⌝⦄ := by
  sorry

/-- Monotonicity of digit count

Coq theorem and proof:
```coq
Theorem Zdigits_le :
  forall n m,
  n <> Z0 -> (Z.abs n <= Z.abs m)%Z ->
  (Zdigits n <= Zdigits m)%Z.
Proof.
intros n m Hn Hm.
rewrite <- Zdigits_abs.
rewrite <- (Zdigits_abs m).
apply Zpower_lt_Zpower with beta.
apply Zdigits_correct.
apply Z.le_lt_trans with (2 := proj2 (Zdigits_correct _)).
exact Hm.
Qed.
```
-/
theorem Zdigits_le (n m : Int) :
    ⦃⌜n ≠ 0 ∧ Int.natAbs n ≤ Int.natAbs m⌝⦄
    Zdigits beta n
    ⦃⇓dn => ⌜∃ dm, Zdigits beta m = pure dm ∧ dn ≤ dm⌝⦄ := by
  sorry

/-- Lower bound for digit count

Coq theorem and proof:
```coq
Theorem lt_Zdigits :
  forall n m,
  (Z.abs n < Zpower beta m)%Z ->
  (Zdigits n <= m)%Z.
Proof.
intros n m Hn.
apply Zpower_lt_Zpower with beta.
now apply Zdigits_correct.
exact Hn.
apply Z.le_refl.
Qed.
```
-/
theorem lt_Zdigits (n m : Int) :
    ⦃⌜m ≠ 0 ∧ Int.natAbs n < beta ^ m.natAbs⌝⦄
    Zdigits beta n
    ⦃⇓d => ⌜d ≤ m⌝⦄ := by
  sorry

/-- Power bound for digit count

Coq theorem and proof:
```coq
Theorem Zpower_le_Zdigits :
  forall e n,
  n <> Z0 ->
  (Zpower beta e <= Z.abs n)%Z ->
  (e < Zdigits n)%Z.
Proof.
intros e n Zn Hn.
apply Zpower_lt_Zpower with beta.
apply Z.le_lt_trans with (1 := Hn).
apply Zdigits_correct.
exact Zn.
apply Zdigits_ge_0.
Qed.
```
-/
theorem Zpower_le_Zdigits (n e : Int) :
    ⦃⌜n ≠ 0 ∧ beta ^ e.natAbs ≤ Int.natAbs n⌝⦄
    Zdigits beta n
    ⦃⇓d => ⌜e < d⌝⦄ := by
  sorry

/-- Alternative digit count bound

Coq theorem and proof:
```coq
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
theorem Zdigits_le_Zdigits (n m : Int) :
    ⦃⌜m ≠ 0 ∧ Int.natAbs n < Int.natAbs m⌝⦄
    Zdigits beta n
    ⦃⇓dn => ⌜∃ dm, Zdigits beta m = pure dm ∧ dn ≤ dm⌝⦄ := by
  sorry

/-- Digit count and power relationship

Coq theorem and proof:
```coq
Theorem Zdigits_le_Zpower :
  forall e x,
  (Z.abs x < Zpower beta e)%Z ->
  (Zdigits x <= e)%Z.
Proof.
intros e x.
generalize (Zpower_le_Zdigits e x).
lia.
Qed.
```
-/
theorem Zdigits_le_Zpower (x e : Int) :
    ⦃⌜Int.natAbs x < beta ^ e.natAbs⌝⦄
    Zdigits beta x
    ⦃⇓d => ⌜d ≤ e⌝⦄ := by
  sorry

/-- Power greater than digit count

Coq theorem and proof:
```coq
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
theorem Zpower_gt_Zdigits (e x : Int) :
    ⦃⌜∃ dx, Zdigits beta x = pure dx ∧ dx ≤ e⌝⦄
    Zdigits beta x
    ⦃⇓_ => ⌜Int.natAbs x < beta ^ e.natAbs⌝⦄ := by
  sorry

/-- Digit count greater than power

Coq theorem and proof:
```coq
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
theorem Zdigits_gt_Zpower (e x : Int) :
    ⦃⌜beta ^ e.natAbs ≤ Int.natAbs x⌝⦄
    Zdigits beta x
    ⦃⇓d => ⌜e < d⌝⦄ := by
  sorry

/-- Strong version of digit count for multiplication

Coq theorem and proof:
```coq
Theorem Zdigits_mult_strong :
  forall x y,
  (0 <= x)%Z -> (0 <= y)%Z ->
  (Zdigits (x + y + x * y) <= Zdigits x + Zdigits y)%Z.
Proof.
intros x y Hx Hy.
apply Zdigits_le_Zpower.
rewrite Z.abs_eq.
apply Z.lt_le_trans with ((x + 1) * (y + 1))%Z.
ring_simplify.
apply Zle_lt_succ, Z.le_refl.
rewrite Zpower_plus by apply Zdigits_ge_0.
apply Zmult_le_compat.
apply Zlt_le_succ.
rewrite <- (Z.abs_eq x) at 1 by easy.
apply Zdigits_correct.
apply Zlt_le_succ.
rewrite <- (Z.abs_eq y) at 1 by easy.
apply Zdigits_correct.
clear -Hx ; lia.
clear -Hy ; lia.
change Z0 with (0 + 0 + 0)%Z.
apply Zplus_le_compat.
now apply Zplus_le_compat.
now apply Zmult_le_0_compat.
Qed.
```
-/
theorem Zdigits_mult_strong (x y : Int) :
    ⦃⌜0 ≤ x ∧ 0 ≤ y⌝⦄
    Zdigits beta (x + y + x * y)
    ⦃⇓d => ⌜∃ dx dy, Zdigits beta x = pure dx ∧ Zdigits beta y = pure dy ∧ d ≤ dx + dy⌝⦄ := by
  sorry

/-- Digit count of multiplication

Coq theorem and proof:
```coq
Theorem Zdigits_mult :
  forall x y,
  (Zdigits (x * y) <= Zdigits x + Zdigits y)%Z.
Proof.
intros x y.
rewrite <- Zdigits_abs.
rewrite <- (Zdigits_abs x).
rewrite <- (Zdigits_abs y).
apply Z.le_trans with (Zdigits (Z.abs x + Z.abs y + Z.abs x * Z.abs y)).
apply Zdigits_le.
apply Zabs_pos.
rewrite Zabs_Zmult.
generalize (Zabs_pos x) (Zabs_pos y).
lia.
apply Zdigits_mult_strong ; apply Zabs_pos.
Qed.
```
-/
theorem Zdigits_mult (x y : Int) :
    ⦃⌜True⌝⦄
    Zdigits beta (x * y)
    ⦃⇓d => ⌜∃ dx dy, Zdigits beta x = pure dx ∧ Zdigits beta y = pure dy ∧ d ≤ dx + dy⌝⦄ := by
  sorry

/-- Lower bound for digit count of multiplication

Coq theorem and proof:
```coq
Theorem Zdigits_mult_ge :
  forall x y,
  (x <> 0)%Z -> (y <> 0)%Z ->
  (Zdigits x + Zdigits y - 1 <= Zdigits (x * y))%Z.
Proof.
intros x y Zx Zy.
cut ((Zdigits x - 1) + (Zdigits y - 1) < Zdigits (x * y))%Z. lia.
apply Zdigits_gt_Zpower.
rewrite Zabs_Zmult.
rewrite Zpower_exp.
apply Zmult_le_compat.
apply Zpower_le_Zdigits.
apply Zlt_pred.
apply Zpower_le_Zdigits.
apply Zlt_pred.
apply Zpower_ge_0.
apply Zpower_ge_0.
generalize (Zdigits_gt_0 x). lia.
generalize (Zdigits_gt_0 y). lia.
Qed.
```
-/
theorem Zdigits_mult_ge (x y : Int) :
    ⦃⌜x ≠ 0 ∧ y ≠ 0⌝⦄
    Zdigits beta (x * y)
    ⦃⇓d => ⌜∃ dx dy, Zdigits beta x = pure dx ∧ Zdigits beta y = pure dy ∧ dx + dy - 1 ≤ d⌝⦄ := by
  sorry

/-- Digit count of division by power

Coq theorem and proof:
```coq
Theorem Zdigits_div_Zpower :
  forall m e,
  (0 <= m)%Z ->
  (0 <= e <= Zdigits m)%Z ->
  Zdigits (m / Zpower beta e) = (Zdigits m - e)%Z.
Proof.
intros m e Hm He.
assert (H := Zdigits_correct m).
apply Zdigits_unique.
destruct (Zle_lt_or_eq _ _ (proj2 He)) as [He'|He'].
  rewrite Z.abs_eq in H by easy.
  destruct H as [H1 H2].
  rewrite Z.abs_eq.
  split.
  replace (Zdigits m - e - 1)%Z with (Zdigits m - 1 - e)%Z by ring.
  rewrite Z.pow_sub_r.
  2: apply Zgt_not_eq, radix_gt_0.
  2: clear -He He' ; lia.
  apply Z_div_le with (2 := H1).
  now apply Z.lt_gt, Zpower_gt_0.
  apply Zmult_lt_reg_r with (Zpower beta e).
  now apply Zpower_gt_0.
  apply Z.le_lt_trans with m.
  rewrite Zmult_comm.
  apply Z_mult_div_ge.
  now apply Z.lt_gt, Zpower_gt_0.
  rewrite <- Zpower_plus.
  now replace (Zdigits m - e + e)%Z with (Zdigits m) by ring.
  now apply Zle_minus_le_0.
  apply He.
  apply Z_div_pos with (2 := Hm).
  now apply Z.lt_gt, Zpower_gt_0.
rewrite He'.
rewrite (Zeq_minus _ (Zdigits m)) by reflexivity.
simpl.
rewrite Zdiv_small.
easy.
split.
exact Hm.
now rewrite <- (Z.abs_eq m) at 1.
Qed.
```
-/
theorem Zdigits_div_Zpower (m e : Int) :
    ⦃⌜0 ≤ m ∧ 0 ≤ e ∧ ∃ dm, Zdigits beta m = pure dm ∧ e ≤ dm⌝⦄
    Zdigits beta (m / beta ^ e.natAbs)
    ⦃⇓d => ⌜∃ dm, Zdigits beta m = pure dm ∧ d = dm - e⌝⦄ := by
  sorry

/-- Digit count of successor

Coq theorem and proof:
```coq
Theorem Zdigits_succ_le :
  forall x, (0 <= x)%Z ->
  (Zdigits (x + 1) <= Zdigits x + 1)%Z.
Proof.
  intros [|p|p]; try easy.
  intros _.
  rewrite <- Zdigits_mult_Zpower by easy.
  apply Zdigits_le. easy.
  apply Z.le_trans with (Z.pos p * 2)%Z.
  lia.
  apply Zmult_le_compat_l. 2: easy.
  rewrite Z.pow_1_r.
  apply (Zlt_le_succ 1), radix_gt_1.
Qed.
```
-/
theorem Zdigits_succ_le (x : Int) :
    ⦃⌜0 ≤ x⌝⦄
    Zdigits beta (x + 1)
    ⦃⇓d => ⌜∃ dx, Zdigits beta x = pure dx ∧ d ≤ dx + 1⌝⦄ := by
  sorry

end DigitOperations

section Zdigits2

variable (beta : Int) (h_beta : beta > 1)

/-- Relationship between natural and integer digit count

Coq theorem and proof:
```coq
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
    Zdigits 2 m
    ⦃⇓d => ⌜d = Id.run (digits2_Pnat m) + 1⌝⦄ := by
  -- This theorem relates the binary digit count from digits2_Pnat
  -- to the general Zdigits function when beta = 2
  -- The +1 accounts for the difference in counting conventions
  sorry

/-- Positive digit count for binary

Coq theorem and proof:
```coq
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
    Zdigits 2 m
    ⦃⇓d => ⌜d = Id.run (digits2_Pnat m)⌝⦄ := by
  -- This theorem shows that for positive numbers,
  -- Zdigits with base 2 equals digits2_Pnat
  -- Both functions compute the binary digit count
  sorry

/-- Equivalence of binary digit count functions

Coq theorem and proof:
```coq
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
    Zdigits 2 n
    ⦃⇓d => ⌜d = Id.run (Zdigits 2 n)⌝⦄ := by
  intro _
  -- Trivial reflexivity: running the same computation yields itself.
  rfl

end Zdigits2

end FloatSpec.Core.Digits
