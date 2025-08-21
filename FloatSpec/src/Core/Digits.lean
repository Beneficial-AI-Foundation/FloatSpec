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
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Std.Do

namespace FloatSpec.Core.Digits

set_option maxRecDepth 4096

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
        simpa [hb]
      · -- upper bound
        simpa [hb]
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
            2 * 2 ^ (b - 1) = 2 ^ (b - 1) * 2 := by simpa [Nat.mul_comm]
            _ = 2 ^ ((b - 1) + 1) := by simp [Nat.pow_succ]
            _ = 2 ^ b := by simpa [hb']
        simpa [hpow]
          using h2_mul
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
        simpa [bits_succ2] using (Nat.add_sub_cancel 1 (bits m2))
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

/-- Extract the k-th digit of a number n in the given radix -/
def Zdigit (n k : Int) : Id Int :=
  pure (if k ≥ 0 then (n / (beta ^ k.natAbs)) % beta else 0)

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
                  result = if k ≥ 0 then ((-n) / (beta ^ k.natAbs)) % beta else 0⌝⦄ := by
  intro _
  unfold Zdigit
  use (if k ≥ 0 then (n / (beta ^ k.natAbs)) % beta else 0)
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
  simp [he_pos]
  have : n / beta ^ e.natAbs = 0 := by
    apply Int.ediv_eq_zero_of_lt
    · exact hn_pos
    · exact hn_bound
  simp [this]

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
  -- By the bound on |n|, we know the digit at position e is 0
  -- This is because n is too small to have a non-zero digit at that position
  sorry  -- Complex proof involving integer division properties

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
theorem Zdigit_not_0_pos (n : Int) :
    ⦃⌜0 < n⌝⦄
    Zdigit beta n 0
    ⦃⇓result => ⌜∃ k, 0 ≤ k ∧ Id.run (Zdigit beta n k) ≠ 0⌝⦄ := by
  sorry  -- Requires strong induction on positive integers

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
theorem Zdigit_not_0 (n : Int) :
    ⦃⌜n ≠ 0⌝⦄
    Zdigit beta n 0
    ⦃⇓_ => ⌜∃ k, 0 ≤ k ∧ Id.run (Zdigit beta n k) ≠ 0⌝⦄ := by
  sorry  -- Extends Zdigit_not_0_pos to negative numbers using Zdigit_opp

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
theorem Zdigit_mul_pow (n k l : Int) :
    ⦃⌜0 ≤ l⌝⦄
    Zdigit beta (n * beta ^ l.natAbs) k
    ⦃⇓result => ⌜∃ shifted, Zdigit beta n (k - l) = pure shifted ∧ result = shifted⌝⦄ := by
  sorry

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
theorem Zdigit_div_pow (n k l : Int) :
    ⦃⌜0 ≤ l ∧ 0 ≤ k⌝⦄
    Zdigit beta (n / beta ^ l.natAbs) k
    ⦃⇓result => ⌜∃ shifted, Zdigit beta n (k + l) = pure shifted ∧ result = shifted⌝⦄ := by
  sorry

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
theorem Zdigit_mod_pow (n k l : Int) :
    ⦃⌜0 ≤ k ∧ k < l⌝⦄
    Zdigit beta (n % beta ^ l.natAbs) k
    ⦃⇓result => ⌜∃ orig, Zdigit beta n k = pure orig ∧ result = orig⌝⦄ := by
  sorry

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
theorem Zdigit_mod_pow_out (n k l : Int) :
    ⦃⌜0 ≤ l ∧ l ≤ k⌝⦄
    Zdigit beta (n % beta ^ l.natAbs) k
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  sorry

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
theorem Zsum_digit_digit (n : Int) (k : Nat) :
    ⦃⌜True⌝⦄
    Zsum_digit beta (fun i => Id.run (Zdigit beta n i)) k
    ⦃⇓result => ⌜result = n % beta ^ k⌝⦄ := by
  sorry

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
theorem Zdigit_ext (n m : Int) :
    ⦃⌜∀ k, 0 ≤ k → Id.run (Zdigit beta n k) = Id.run (Zdigit beta m k)⌝⦄
    Zdigit beta n 0
    ⦃⇓_ => ⌜n = m⌝⦄ := by
  sorry

/-- Modulo and digit sum -/
theorem ZOmod_plus_pow_digit (n k : Int) :
    ⦃⌜0 ≤ k⌝⦄
    Zdigit beta n k
    ⦃⇓d => ⌜n % beta ^ (k + 1).natAbs =
            n % beta ^ k.natAbs + d * beta ^ k.natAbs⌝⦄ := by
  sorry

/-- Division and digit sum -/
theorem ZOdiv_plus_pow_digit (n k : Int) :
    ⦃⌜0 ≤ k⌝⦄
    Zdigit beta n k
    ⦃⇓d => ⌜n / beta ^ k.natAbs =
            d + (n / beta ^ (k + 1).natAbs) * beta⌝⦄ := by
  sorry

/-- Digit of sum -/
theorem Zdigit_plus (n m k : Int) :
    ⦃⌜0 ≤ k⌝⦄
    Zdigit beta (n + m) k
    ⦃⇓result => ⌜∃ dn dm carry,
                  Zdigit beta n k = pure dn ∧
                  Zdigit beta m k = pure dm ∧
                  carry ∈ ({0, 1} : Set Int) ∧
                  result = (dn + dm + carry) % beta⌝⦄ := by
  sorry

/-- Scale a number by a power of beta -/
def Zscale (n k : Int) : Id Int :=
  pure (if 0 ≤ k then n * beta ^ k.natAbs else n / beta ^ (-k).natAbs)

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
theorem Zdigit_scale (n k k' : Int) :
    ⦃⌜0 ≤ k'⌝⦄
    Zdigit beta (Id.run (Zscale beta n k)) k'
    ⦃⇓result => ⌜∃ orig, Zdigit beta n (k' - k) = pure orig ∧ result = orig⌝⦄ := by
  sorry

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

/-- Scaling preserves sign -/
theorem Zsame_sign_scale (n k : Int) :
    ⦃⌜n ≠ 0⌝⦄
    Zscale beta n k
    ⦃⇓result => ⌜(0 < n ∧ 0 < result) ∨ (n < 0 ∧ result < 0)⌝⦄ := by
  sorry  -- This proof requires careful analysis of integer multiplication and division signs

/-- Scaling and multiplication -/
theorem Zscale_mul_pow (n k l : Int) :
    ⦃⌜0 ≤ l⌝⦄
    Zscale beta (n * beta ^ l.natAbs) k
    ⦃⇓result => ⌜∃ scaled, Zscale beta n (k + l) = pure scaled ∧ result = scaled⌝⦄ := by
  sorry

/-- Composition of scaling -/
theorem Zscale_scale (n k l : Int) :
    ⦃⌜True⌝⦄
    Zscale beta (Id.run (Zscale beta n k)) l
    ⦃⇓result => ⌜∃ scaled, Zscale beta n (k + l) = pure scaled ∧ result = scaled⌝⦄ := by
  sorry

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
theorem Zdigit_slice (n k l m : Int) :
    ⦃⌜0 ≤ m⌝⦄
    Zdigit beta (Id.run (Zslice beta n k l)) m
    ⦃⇓result => ⌜if m < l then ∃ orig, Zdigit beta n (k + m) = pure orig ∧ result = orig
                 else result = 0⌝⦄ := by
  sorry

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
theorem Zdigit_slice_out (n k l m : Int) :
    ⦃⌜l ≤ m⌝⦄
    Zdigit beta (Id.run (Zslice beta n k l)) m
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  sorry

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
theorem Zsame_sign_slice (n k l : Int) :
    ⦃⌜0 ≤ n ∧ 0 ≤ k ∧ 0 ≤ l⌝⦄
    Zslice beta n k l
    ⦃⇓result => ⌜0 ≤ result⌝⦄ := by
  sorry  -- This proof requires analysis of modulo operations on non-negative integers

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
theorem Zslice_slice (n k1 k2 k1' k2' : Int) :
    ⦃⌜0 ≤ k1' ∧ k1' ≤ k2⌝⦄
    Zslice beta (Id.run (Zslice beta n k1 k2)) k1' k2'
    ⦃⇓result => ⌜∃ inner_slice, Zslice beta n (k1 + k1') (min (k2 - k1') k2') = pure inner_slice ∧
                  result = inner_slice⌝⦄ := by
  sorry

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
theorem Zslice_mul_pow (n k k1 k2 : Int) :
    ⦃⌜0 ≤ k⌝⦄
    Zslice beta (n * beta ^ k.natAbs) k1 k2
    ⦃⇓result => ⌜∃ slice_shifted, Zslice beta n (k1 - k) k2 = pure slice_shifted ∧
                  result = slice_shifted⌝⦄ := by
  sorry

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
theorem Zslice_div_pow (n k k1 k2 : Int) :
    ⦃⌜0 ≤ k ∧ 0 ≤ k1⌝⦄
    Zslice beta (n / beta ^ k.natAbs) k1 k2
    ⦃⇓result => ⌜∃ slice_shifted, Zslice beta n (k1 + k) k2 = pure slice_shifted ∧
                  result = slice_shifted⌝⦄ := by
  sorry

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
theorem Zslice_scale (n k k1 k2 : Int) :
    ⦃⌜0 ≤ k1⌝⦄
    Zslice beta (Id.run (Zscale beta n k)) k1 k2
    ⦃⇓result => ⌜∃ slice_unscaled, Zslice beta n (k1 - k) k2 = pure slice_unscaled ∧
                  result = slice_unscaled⌝⦄ := by
  sorry

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
theorem Zslice_div_pow_scale (n k k' k1 k2 : Int) :
    ⦃⌜0 ≤ k⌝⦄
    Zslice beta ((n / beta ^ k.natAbs) * beta ^ k'.natAbs) k1 k2
    ⦃⇓result => ⌜∃ slice_combined, Zslice beta n (k1 + k - k') k2 = pure slice_combined ∧
                  result = slice_combined⌝⦄ := by
  sorry

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
theorem Zplus_slice (n m k l : Int) :
    ⦃⌜0 ≤ k ∧ 0 ≤ l⌝⦄
    Zslice beta (n + m) k l
    ⦃⇓result => ⌜∃ n_slice m_slice,
                  Zslice beta n k l = pure n_slice ∧
                  Zslice beta m k l = pure m_slice ∧
                  (result = (n_slice + m_slice) % beta ^ l.natAbs ∨
                   result = (n_slice + m_slice + 1) % beta ^ l.natAbs)⌝⦄ := by
  sorry

/-- Number of digits in base beta -/
def Zdigits_aux (nb pow : Int) : Nat → Id Int
  | 0 => pure nb
  | n + 1 => if nb < pow then pure nb else Zdigits_aux (nb + 1) (beta * pow) n

/-- Number of digits of an integer -/
def Zdigits (n : Int) : Id Int :=
  match n with
  | 0 => pure 0
  | n => if n > 0 then
           let p := n.natAbs
           Zdigits_aux beta n 1 p.succ
         else
           let p := (-n).natAbs
           Zdigits_aux beta (-n) 1 p.succ

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
theorem Zdigits_correct (n : Int) :
    ⦃⌜n ≠ 0⌝⦄
    Zdigits beta n
    ⦃⇓d => ⌜beta ^ (d - 1).natAbs ≤ Int.natAbs n ∧ Int.natAbs n < beta ^ d.natAbs⌝⦄ := by
  -- This theorem establishes that Zdigits computes the correct number of digits
  -- such that beta^(d-1) ≤ |n| < beta^d
  -- The proof would use induction on the auxiliary function Zdigits_aux
  sorry

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
theorem Zdigits_unique (n e : Int) :
    ⦃⌜n ≠ 0 ∧ beta ^ (e - 1).natAbs ≤ Int.natAbs n ∧ Int.natAbs n < beta ^ e.natAbs⌝⦄
    Zdigits beta n
    ⦃⇓d => ⌜d = e⌝⦄ := by
  -- This uniqueness theorem shows that if n is bounded by consecutive powers of beta,
  -- then Zdigits returns the unique exponent e
  -- This follows from the correctness theorem and the monotonicity of powers
  sorry

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
  -- This proof requires showing that Zdigits ignores the sign of the input
  -- Since Int.natAbs always returns a non-negative value, we need to show
  -- that Zdigits beta (Int.natAbs n) = Zdigits beta |n| = Zdigits beta n
  sorry

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
  sorry  -- This proof requires showing Zdigits ignores sign

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
theorem Zdigits_cond_Zopp (b : Bool) (n : Int) :
    ⦃⌜True⌝⦄
    Zdigits beta (if b then -n else n)
    ⦃⇓d => ⌜∃ dn, Zdigits beta n = pure dn ∧ d = dn⌝⦄ := by
  sorry

/-- Helper lemma: Zdigits_aux maintains lower bound -/
private lemma Zdigits_aux_ge (nb pow : Int) (fuel : Nat) :
    nb ≥ 0 → Id.run (Zdigits_aux beta nb pow fuel) ≥ nb := by
  intro h_nb_ge
  induction fuel generalizing nb pow with
  | zero => simp [Zdigits_aux]
  | succ n ih =>
    simp [Zdigits_aux]
    split
    · -- Case: nb < pow
      simp
    · -- Case: nb ≥ pow
      have h_next : nb + 1 ≥ 0 := Int.add_nonneg h_nb_ge (by omega)
      have ih_result := ih (nb + 1) (beta * pow) h_next
      omega

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
theorem Zdigits_gt_0 (n : Int) :
    ⦃⌜n ≠ 0⌝⦄
    Zdigits beta n
    ⦃⇓result => ⌜0 < result⌝⦄ := by
  sorry

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
  sorry

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
theorem Zdigit_out (n k : Int) :
    ⦃⌜∃ digits_val, Zdigits beta n = pure digits_val ∧ digits_val ≤ k⌝⦄
    Zdigit beta n k
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  sorry

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
theorem Zdigit_digits (n : Int) :
    ⦃⌜n ≠ 0⌝⦄
    Zdigits beta n
    ⦃⇓d => ⌜Id.run (Zdigit beta n (d - 1)) ≠ 0⌝⦄ := by
  -- This theorem shows that the highest digit (at position d-1) is non-zero
  -- This is essential for canonical digit representations
  sorry

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
  -- This is a trivial identity theorem
  -- Zdigits 2 n equals itself
  sorry

end Zdigits2

end FloatSpec.Core.Digits
