-- Legacy Pff library compatibility layer
-- Translated from Coq file: flocq/src/Pff/Pff.v

import Std.Do.Triple
import FloatSpec.src.Core
import FloatSpec.src.Compat
import Mathlib.Data.Real.Basic
import FloatSpec.src.Calc.Operations
import FloatSpec.src.SimprocWP

open Real
open Std.Do

-- Compatibility definitions for Pff legacy support

-- Even number properties
def nat_even (n : Nat) : Prop := ∃ k, n = 2 * k

def nat_odd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

-- Even/Odd lemmas
theorem even_0 : nat_even 0 := ⟨0, rfl⟩

theorem odd_1 : nat_odd 1 := ⟨0, rfl⟩

theorem not_even_1 : ¬nat_even 1 := by
  intro ⟨k, hk⟩
  omega

theorem not_odd_0 : ¬nat_odd 0 := by
  intro ⟨k, hk⟩
  omega

-- Double operation
def nat_double (n : Nat) : Nat := 2 * n

-- Division by 2
def nat_div2 (n : Nat) : Nat := n / 2

-- Even/Odd characterization
theorem even_iff_double (n : Nat) : nat_even n ↔ n = nat_double (nat_div2 n) := by
  constructor
  · intro ⟨k, hk⟩
    simp only [nat_double, nat_div2]
    omega
  · intro h
    simp only [nat_double, nat_div2] at h
    exact ⟨n / 2, h⟩

theorem odd_iff_double (n : Nat) : nat_odd n ↔ n = nat_double (nat_div2 n) + 1 := by
  constructor
  · intro ⟨k, hk⟩
    simp only [nat_double, nat_div2]
    omega
  · intro h
    simp only [nat_double, nat_div2] at h
    exact ⟨n / 2, h⟩

-- ---------------------------------------------------------------------------
-- Missing parity lemmas over Nat (Coq compatibility)

noncomputable def Even_0_check : Unit :=
  ()

/-- Coq: `Even_0` — 0 is even. -/
theorem Even_0 :
    ⦃⌜True⌝⦄
    (pure Even_0_check : Id Unit)
    ⦃⇓_ => ⌜nat_even 0⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure, Even_0_check]
  exact even_0

noncomputable def Even_1_check : Unit :=
  ()

/-- Coq: `Even_1` — 1 is not even. -/
theorem Even_1 :
    ⦃⌜True⌝⦄
    (pure Even_1_check : Id Unit)
    ⦃⇓_ => ⌜¬ nat_even 1⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure, Even_1_check]
  exact not_even_1

noncomputable def Odd_0_check : Unit :=
  ()

/-- Coq: `Odd_0` — 0 is not odd. -/
theorem Odd_0 :
    ⦃⌜True⌝⦄
    (pure Odd_0_check : Id Unit)
    ⦃⇓_ => ⌜¬ nat_odd 0⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure, Odd_0_check]
  exact not_odd_0

noncomputable def Odd_1_check : Unit :=
  ()

/-- Coq: `Odd_1` — 1 is odd. -/
theorem Odd_1 :
    ⦃⌜True⌝⦄
    (pure Odd_1_check : Id Unit)
    ⦃⇓_ => ⌜nat_odd 1⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure, Odd_1_check]
  exact odd_1

-- Legacy tactical support (simplified)
section LegacyTactics

-- Case analysis preserving equality
def case_eq {α β : Type*} (x : α) (f : α → β) : β := f x

-- Simple automation for arithmetic
theorem arith_helper (a b c : Int) : a + b = c → a = c - b := by
  intro h
  linarith

end LegacyTactics

-- Power operations compatibility
theorem pow_inv (r : ℝ) (n : Nat) (h : r ≠ 0) :
  (r^n)⁻¹ = r⁻¹^n := by
  exact (inv_pow r n).symm

theorem pow_neg (r : ℝ) (z : Int) :
  r^(-z) = (r^z)⁻¹ := by
  exact zpow_neg r z

-- Real number compatibility
theorem abs_inv_compat (r : ℝ) : |r⁻¹| = |r|⁻¹ := by
  exact abs_inv r

-- Coq compat: `powerRZ_inv` — (r^z)⁻¹ = r^(-z)
noncomputable def powerRZ_inv_check (r : ℝ) (z : Int) : Unit :=
  ()

theorem powerRZ_inv (r : ℝ) (z : Int) :
    ⦃⌜True⌝⦄
    (pure (powerRZ_inv_check r z) : Id Unit)
    ⦃⇓_ => ⌜(r ^ z)⁻¹ = r ^ (-z)⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, powerRZ_inv_check]
  exact (zpow_neg r z).symm

-- Coq compat: `powerRZ_neg` — r^(-z) = (r^z)⁻¹
noncomputable def powerRZ_neg_check (r : ℝ) (z : Int) : Unit :=
  ()

theorem powerRZ_neg (r : ℝ) (z : Int) :
    ⦃⌜True⌝⦄
    (pure (powerRZ_neg_check r z) : Id Unit)
    ⦃⇓_ => ⌜r ^ (-z) = (r ^ z)⁻¹⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, powerRZ_neg_check]
  exact zpow_neg r z

-- (reserved for future compatibility lemmas)

-- ---------------------------------------------------------------------------
-- Integer rounding down by 1 (IRNDD) and basic properties (Coq alignment)

-- Coq: `IRNDD (r) = Z.pred (up r)`; predecessor of ceiling function
-- In Coq, `up r` is the smallest integer strictly greater than r.
-- This equals floor(r) in all cases:
--   - When r is not integer: up r = ceil r, so pred(up r) = ceil r - 1 = floor r
--   - When r IS integer: up r = r + 1, so pred(up r) = r = floor r
noncomputable def IRNDD (r : ℝ) : Int := Int.floor r

noncomputable def IRNDD_correct1_check (r : ℝ) : Unit :=
  ()

/-- Coq: `IRNDD_correct1` — IRNDD r ≤ r. -/
theorem IRNDD_correct1 (r : ℝ) :
    ⦃⌜True⌝⦄
    (pure (IRNDD_correct1_check r) : Id Unit)
    ⦃⇓_ => ⌜(IRNDD r : ℝ) ≤ r⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure, IRNDD_correct1_check, IRNDD]
  -- Goal: (Int.floor r : ℝ) ≤ r
  exact Int.floor_le r

noncomputable def IRNDD_correct2_check (r : ℝ) : Unit :=
  ()

/-- Coq: `IRNDD_correct2` — r < succ (IRNDD r). -/
theorem IRNDD_correct2 (r : ℝ) :
    ⦃⌜True⌝⦄
    (pure (IRNDD_correct2_check r) : Id Unit)
    ⦃⇓_ => ⌜r < ((Int.succ (IRNDD r)) : ℝ)⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure, IRNDD_correct2_check, IRNDD, Int.succ]

noncomputable def IRNDD_correct3_check (r : ℝ) : Unit :=
  ()

/-- Coq: `IRNDD_correct3` — r - 1 < IRNDD r. -/
theorem IRNDD_correct3 (r : ℝ) :
    ⦃⌜True⌝⦄
    (pure (IRNDD_correct3_check r) : Id Unit)
    ⦃⇓_ => ⌜r - 1 < (IRNDD r : ℝ)⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, IRNDD_correct3_check, IRNDD]
  -- Goal: r - 1 < ↑⌊r⌋
  exact Int.sub_one_lt_floor r

noncomputable def IRNDD_pos_check (r : ℝ) : Unit :=
  ()

/-- Coq: `IRNDD_pos` — 0 ≤ r → 0 ≤ IRNDD r. -/
theorem IRNDD_pos (r : ℝ) :
    ⦃⌜0 ≤ r⌝⦄
    (pure (IRNDD_pos_check r) : Id Unit)
    ⦃⇓_ => ⌜0 ≤ IRNDD r⌝⦄ := by
  intro hr
  simp [wp, PostCond.noThrow, pure, IRNDD_pos_check, IRNDD]
  exact Int.floor_nonneg.mpr hr

noncomputable def IRNDD_eq_check (r : ℝ) (z : Int) : Unit :=
  ()

/-- Coq: `IRNDD_eq` — if z ≤ r < succ z then IRNDD r = z. -/
theorem IRNDD_eq (r : ℝ) (z : Int) :
    ⦃⌜(z : ℝ) ≤ r ∧ r < ((Int.succ z) : ℝ)⌝⦄
    (pure (IRNDD_eq_check r z) : Id Unit)
    ⦃⇓_ => ⌜IRNDD r = z⌝⦄ := by
  intro ⟨hz_le, hz_lt⟩
  simp only [wp, PostCond.noThrow, pure, IRNDD_eq_check, IRNDD]
  -- Goal: Int.floor r = z
  -- Use Int.floor_eq_iff: ⌊a⌋ = z ↔ z ≤ a ∧ a < z + 1
  rw [Int.floor_eq_iff]
  constructor
  · exact hz_le
  · simp only [Int.succ, Int.cast_add, Int.cast_one] at hz_lt
    exact hz_lt

noncomputable def IRNDD_projector_check (z : Int) : Unit :=
  ()

/-- Coq: `IRNDD_projector` — IRNDD z = z for integer inputs. -/
theorem IRNDD_projector (z : Int) :
    ⦃⌜True⌝⦄
    (pure (IRNDD_projector_check z) : Id Unit)
    ⦃⇓_ => ⌜IRNDD (z : ℝ) = z⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, IRNDD_projector_check, IRNDD]
  -- Goal: Int.floor (z : ℝ) = z
  exact Int.floor_intCast z

-- ---------------------------------------------------------------------------
-- Integer parity lemmas (aligned with Coq: Odd/Even over Z)

-- ---------------------------------------------------------------------------
-- Log/exponential auxiliary lemmas from Coq Pff.v

noncomputable def ln_radix_pos_check (radix : ℝ) : Unit :=
  ()

/-- Coq: `ln_radix_pos` — 0 < ln radix. Requires radix > 1. -/
theorem ln_radix_pos (radix : ℝ) :
    ⦃⌜1 < radix⌝⦄
    (pure (ln_radix_pos_check radix) : Id Unit)
    ⦃⇓_ => ⌜0 < Real.log radix⌝⦄ := by
  intro hradix
  simp only [wp, PostCond.noThrow, pure, ln_radix_pos_check]
  -- Goal: 0 < Real.log radix
  -- Since radix > 1, log radix > log 1 = 0
  exact Real.log_pos hradix

-- Coq: `exp_ln_powerRZ` — exp (ln u * v) = u^v for integer u>0, v:Z
noncomputable def exp_ln_powerRZ_check (u v : Int) : Unit :=
  ()

theorem exp_ln_powerRZ (u v : Int) :
    ⦃⌜0 < u⌝⦄
    (pure (exp_ln_powerRZ_check u v) : Id Unit)
    ⦃⇓_ => ⌜Real.exp (Real.log (u : ℝ) * (v : ℝ)) = (u : ℝ) ^ v⌝⦄ := by
  intro hu
  simp only [wp, PostCond.noThrow, pure, exp_ln_powerRZ_check]
  -- Goal: Real.exp (Real.log (u : ℝ) * (v : ℝ)) = (u : ℝ) ^ v
  -- Use Real.rpow_def_of_pos: for 0 < x, x ^ y = exp(log x * y)
  -- Then use Real.rpow_intCast: x ^ (n : ℝ) = x ^ n
  have hu_pos : (0 : ℝ) < (u : ℝ) := by exact Int.cast_pos.mpr hu
  rw [← Real.rpow_intCast]
  rw [Real.rpow_def_of_pos hu_pos]
  ring_nf
  trivial

-- Coq: `exp_le_inv` — if exp x ≤ exp y then x ≤ y
noncomputable def exp_le_inv_check (x y : ℝ) : Unit :=
  ()

theorem exp_le_inv (x y : ℝ) :
    ⦃⌜Real.exp x ≤ Real.exp y⌝⦄
    (pure (exp_le_inv_check x y) : Id Unit)
    ⦃⇓_ => ⌜x ≤ y⌝⦄ := by
  intro h
  simp only [wp, PostCond.noThrow, pure, exp_le_inv_check]
  rw [Real.exp_le_exp] at h
  exact h

-- Coq: `exp_monotone` — if x ≤ y then exp x ≤ exp y
noncomputable def exp_monotone_check (x y : ℝ) : Unit :=
  ()

theorem exp_monotone (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    (pure (exp_monotone_check x y) : Id Unit)
    ⦃⇓_ => ⌜Real.exp x ≤ Real.exp y⌝⦄ := by
  intro h
  simp only [wp, PostCond.noThrow, pure, exp_monotone_check]
  rw [Real.exp_le_exp]
  exact h

-- Coq: `OddSEven` — if n is odd then succ n is even
noncomputable def OddSEven_check (n : Int) : Unit :=
  ()

theorem OddSEven (n : Int) :
    ⦃⌜Odd n⌝⦄
    (pure (OddSEven_check n) : Id Unit)
    ⦃⇓_ => ⌜Even (Int.succ n)⌝⦄ := by
  intro h
  simp only [wp, PostCond.noThrow, pure, OddSEven_check, Int.succ]
  exact Odd.add_one h

-- Coq: `EvenSOdd` — if n is even then succ n is odd
noncomputable def EvenSOdd_check (n : Int) : Unit :=
  ()

theorem EvenSOdd (n : Int) :
    ⦃⌜Even n⌝⦄
    (pure (EvenSOdd_check n) : Id Unit)
    ⦃⇓_ => ⌜Odd (Int.succ n)⌝⦄ := by
  intro h
  simp only [wp, PostCond.noThrow, pure, EvenSOdd_check, Int.succ]
  exact Even.add_one h

-- Coq: `OddSEvenInv` — if succ n is odd then n is even
noncomputable def OddSEvenInv_check (n : Int) : Unit :=
  ()

theorem OddSEvenInv (n : Int) :
    ⦃⌜Odd (Int.succ n)⌝⦄
    (pure (OddSEvenInv_check n) : Id Unit)
    ⦃⇓_ => ⌜Even n⌝⦄ := by
  intro h
  simp only [wp, PostCond.noThrow, pure, OddSEvenInv_check, Int.succ]
  have h2 : ¬Even (n + 1) := Int.not_even_iff_odd.mpr h
  have h3 : ¬¬Even n := mt Int.even_add_one.mpr h2
  exact not_not.mp h3

-- Coq: `EvenSOddInv` — if succ n is even then n is odd
noncomputable def EvenSOddInv_check (n : Int) : Unit :=
  ()

theorem EvenSOddInv (n : Int) :
    ⦃⌜Even (Int.succ n)⌝⦄
    (pure (EvenSOddInv_check n) : Id Unit)
    ⦃⇓_ => ⌜Odd n⌝⦄ := by
  intro h
  simp only [wp, PostCond.noThrow, pure, EvenSOddInv_check, Int.succ]
  have h2 : ¬Even n := Int.even_add_one.mp h
  exact Int.not_even_iff_odd.mp h2



-- Coq: `Odd1` — one is odd
noncomputable def Odd1_check : Unit :=
  ()

theorem Odd1 :
    ⦃⌜True⌝⦄
    (pure Odd1_check : Id Unit)
    ⦃⇓_ => ⌜Odd (1 : Int)⌝⦄ := by
  intro _; simp [wp, PostCond.noThrow, pure, Odd1_check]

-- Coq: `EvenO` — zero is even (integer parity)
noncomputable def EvenO_check : Unit :=
  ()

theorem EvenO :
    ⦃⌜True⌝⦄
    (pure (EvenO_check) : Id Unit)
  ⦃⇓_ => ⌜Even (0 : Int)⌝⦄ := by
  intro _; simp [wp, PostCond.noThrow, pure, EvenO_check]

-- Coq: `OddOpp` — odd is preserved by integer negation
noncomputable def OddOpp_check (z : Int) : Unit :=
  ()

theorem OddOpp (z : Int) :
    ⦃⌜Odd z⌝⦄
    (pure (OddOpp_check z) : Id Unit)
    ⦃⇓_ => ⌜Odd (-z)⌝⦄ := by
  intro h; simp only [wp, PostCond.noThrow, pure, OddOpp_check]; exact Odd.neg h

-- Coq: `EvenOpp` — even is preserved by integer negation
noncomputable def EvenOpp_check (z : Int) : Unit :=
  ()

theorem EvenOpp (z : Int) :
    ⦃⌜Even z⌝⦄
    (pure (EvenOpp_check z) : Id Unit)
    ⦃⇓_ => ⌜Even (-z)⌝⦄ := by
  sorry

-- Coq: `OddEvenDec` — for any integer, it is either odd or even
noncomputable def OddEvenDec_check (n : Int) : Unit :=
  ()

theorem OddEvenDec (n : Int) :
    ⦃⌜True⌝⦄
    (pure (OddEvenDec_check n) : Id Unit)
    ⦃⇓_ => ⌜Odd n ∨ Even n⌝⦄ := by
  sorry

-- Coq: `OddNEven` — odd numbers are not even
noncomputable def OddNEven_check (n : Int) : Unit :=
  ()

theorem OddNEven (n : Int) :
    ⦃⌜Odd n⌝⦄
    (pure (OddNEven_check n) : Id Unit)
    ⦃⇓_ => ⌜¬ Even n⌝⦄ := by
  sorry

-- Coq: `EvenNOdd` — even numbers are not odd
noncomputable def EvenNOdd_check (n : Int) : Unit :=
  ()

theorem EvenNOdd (n : Int) :
    ⦃⌜Even n⌝⦄
    (pure (EvenNOdd_check n) : Id Unit)
    ⦃⇓_ => ⌜¬ Odd n⌝⦄ := by
  sorry

-- Coq: `EvenPlus1` — if n and m are even then n + m is even
noncomputable def EvenPlus1_check (n m : Int) : Unit :=
  ()

theorem EvenPlus1 (n m : Int) :
    ⦃⌜Even n ∧ Even m⌝⦄
    (pure (EvenPlus1_check n m) : Id Unit)
    ⦃⇓_ => ⌜Even (n + m)⌝⦄ := by
  sorry

-- Coq: `OddPlus2` — if n is even and m is odd then n + m is odd
noncomputable def OddPlus2_check (n m : Int) : Unit :=
  ()

theorem OddPlus2 (n m : Int) :
    ⦃⌜Even n ∧ Odd m⌝⦄
    (pure (OddPlus2_check n m) : Id Unit)
    ⦃⇓_ => ⌜Odd (n + m)⌝⦄ := by
  sorry

-- Coq: `EvenMult1` — if n is even then n*m is even
noncomputable def EvenMult1_check (n m : Int) : Unit :=
  ()

theorem EvenMult1 (n m : Int) :
    ⦃⌜Even n⌝⦄
    (pure (EvenMult1_check n m) : Id Unit)
    ⦃⇓_ => ⌜Even (n * m)⌝⦄ := by
  sorry

-- Coq: `EvenMult2` — if m is even then n*m is even
noncomputable def EvenMult2_check (n m : Int) : Unit :=
  ()

theorem EvenMult2 (n m : Int) :
    ⦃⌜Even m⌝⦄
    (pure (EvenMult2_check n m) : Id Unit)
    ⦃⇓_ => ⌜Even (n * m)⌝⦄ := by
  sorry

-- Coq: `OddMult` — if n and m are odd then n*m is odd
noncomputable def OddMult_check (n m : Int) : Unit :=
  ()

theorem OddMult (n m : Int) :
    ⦃⌜Odd n ∧ Odd m⌝⦄
    (pure (OddMult_check n m) : Id Unit)
    ⦃⇓_ => ⌜Odd (n * m)⌝⦄ := by
  sorry

-- Coq: `EvenMultInv` — if n*m is even and n is odd then m is even
noncomputable def EvenMultInv_check (n m : Int) : Unit :=
  ()

theorem EvenMultInv (n m : Int) :
    ⦃⌜Even (n * m) ∧ Odd n⌝⦄
    (pure (EvenMultInv_check n m) : Id Unit)
    ⦃⇓_ => ⌜Even m⌝⦄ := by
  sorry

-- Integer power on Int for natural exponent (compat with Coq Zpower_nat)
noncomputable def Zpower_nat_int (n : Int) (k : Nat) : Int := n ^ k

-- Coq: `EvenExp` — if n is even then n^(S m) is even (nat exponent)
noncomputable def EvenExp_check (n : Int) (m : Nat) : Unit :=
  ()

theorem EvenExp (n : Int) (m : Nat) :
    ⦃⌜Even n⌝⦄
    (pure (EvenExp_check n m) : Id Unit)
    ⦃⇓_ => ⌜Even (Zpower_nat_int n (Nat.succ m))⌝⦄ := by
  sorry

-- Coq: `OddExp` — if n is odd then n^m is odd (nat exponent)
noncomputable def OddExp_check (n : Int) (m : Nat) : Unit :=
  ()

theorem OddExp (n : Int) (m : Nat) :
    ⦃⌜Odd n⌝⦄
    (pure (OddExp_check n m) : Id Unit)
    ⦃⇓_ => ⌜Odd (Zpower_nat_int n m)⌝⦄ := by
  sorry

-- Float-level parity wrappers and lemmas (Lean skeletons mirroring Coq)
def Feven {beta : Int}
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Prop :=
  Even p.Fnum

def Fodd {beta : Int}
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Prop :=
  Odd p.Fnum

noncomputable def FevenOrFodd_check {beta : Int}
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem FevenOrFodd {beta : Int}
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (FevenOrFodd_check (beta:=beta) p) : Id Unit)
    ⦃⇓_ => ⌜Feven (beta:=beta) p ∨ Fodd (beta:=beta) p⌝⦄ := by
  sorry

-- ---------------------------------------------------------------------------
-- Rounded-mode predicate framework (Coq FRound section, minimized shell)
-- We provide lightweight predicate encodings to state meta-theorems such as
-- RoundedModeP_inv2 / RoundedModeP_inv4. Detailed semantics (isMin/isMax,
-- boundedness, projector properties) are intentionally deferred.

-- Totality of a rounding relation P
def TotalP {α : Type} (P : ℝ → α → Prop) : Prop :=
  ∀ r : ℝ, ∃ p : α, P r p

-- Compatibility of P under equal real value and representation equality
def CompatibleP {α : Type} (P : ℝ → α → Prop) : Prop :=
  ∀ r1 r2 : ℝ, ∀ p q : α, P r1 p → r1 = r2 → p = q → P r2 q

-- Monotonicity placeholder (kept abstract for now)
def MonotoneP {α : Type} (P : ℝ → α → Prop) : Prop := True

-- Min/Max disjunction placeholder (kept abstract for now)
def MinOrMaxP {α : Type} (P : ℝ → α → Prop) : Prop := True

-- Rounded-mode package
def RoundedModeP {α : Type} (P : ℝ → α → Prop) : Prop :=
  TotalP P ∧ CompatibleP P ∧ MinOrMaxP P ∧ MonotoneP P

-- Uniqueness of a rounding relation P
def UniqueP {α : Type} (P : ℝ → α → Prop) : Prop :=
  ∀ r p q, P r p → P r q → p = q

-- Projector property placeholder
def ProjectorP {α : Type} (P : ℝ → α → Prop) : Prop := True

-- ---------------------------------------------------------------------------
-- Minimal bound skeleton + helper predicates (shared across Pff specs)

structure Fbound_skel where
  -- Minimal exponent field needed by several Pff theorems (e.g. RleRoundedAbs)
  dExp : Int := 0
  vNum : Int := 1

def isMin {α : Type} (b : Fbound_skel) (radix : Int) : ℝ → α → Prop :=
  fun _ _ => True

def isMax {α : Type} (b : Fbound_skel) (radix : Int) : ℝ → α → Prop :=
  fun _ _ => True

-- Coq-style boundedness predicate (placeholder)
def Fbounded {beta : Int}
    (bo : Fbound_skel)
    (f : FloatSpec.Core.Defs.FlocqFloat beta) : Prop := True

-- ---------------------------------------------------------------------------
-- Ulp placeholder (Coq-style `Fulp` on floats)

/-- Coq compatibility: abstract ulp on a float. In detailed developments,
`Fulp` ties to `ulp beta (FLT_exp ...) (F2R q)`. We keep it abstract here so
theorems can be stated and proved elsewhere. -/
noncomputable def Fulp {beta : Int} (q : FloatSpec.Core.Defs.FlocqFloat beta) : ℝ :=
  1

-- Coq: `RleBoundRoundl` — rounding preserves lower bounds
noncomputable def RleBoundRoundl_check {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) (r : ℝ) : Unit :=
  ()

/-- Coq: `RleBoundRoundl` — if `P` forms a rounded mode and `p ≤ r`, then
    any `q` produced by rounding `r` also satisfies `p ≤ q`. -/
theorem RleBoundRoundl {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) (r : ℝ) :
    ⦃⌜RoundedModeP P ∧ Fbounded (beta:=beta) b p ∧
        (_root_.F2R (beta:=beta) p ≤ r) ∧ P r q⌝⦄
    (pure (RleBoundRoundl_check (beta:=beta) b radix P p q r) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (beta:=beta) p ≤ _root_.F2R (beta:=beta) q⌝⦄ := by
  sorry

noncomputable def RleBoundRoundr_check {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) (r : ℝ) : Unit :=
  ()

/-- Coq: `RleBoundRoundr` — if `P` forms a rounded mode and `r ≤ _root_.F2R p`,
    any `q` produced by rounding `r` also satisfies `_root_.F2R q ≤ _root_.F2R p`. -/
theorem RleBoundRoundr {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) (r : ℝ) :
    ⦃⌜RoundedModeP P ∧ Fbounded (beta:=beta) b p ∧
        (r ≤ _root_.F2R (beta:=beta) p) ∧ P r q⌝⦄
    (pure (RleBoundRoundr_check (beta:=beta) b radix P p q r) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (beta:=beta) q ≤ _root_.F2R (beta:=beta) p⌝⦄ := by
  sorry

/-- Minimal normal mantissa (`nNormMin`) defined using a positive-exponent power. -/
noncomputable def nNormMin (radix : Int) (precision : Nat) : Int :=
  radix ^ (precision - 1)

-- Coq: `firstNormalPos_eq` — value of the first normal positive float
noncomputable def firstNormalPos {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat) :
    FloatSpec.Core.Defs.FlocqFloat beta :=
  ⟨nNormMin radix precision, -b.dExp⟩

noncomputable def firstNormalPos_eq_check {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat) : Unit :=
  ()

/-- Coq: `firstNormalPos_eq` — interpreting the `firstNormalPos` float at
    base `radix` equals the real value `(nNormMin radix precision : ℝ) * (radix : ℝ) ^ (-b.dExp)`.
    Following the file's Hoare-triple convention; proof deferred. -/
theorem firstNormalPos_eq {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat) :
    ⦃⌜True⌝⦄
    (pure (firstNormalPos_eq_check (beta:=beta) radix b precision) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (beta:=beta) (firstNormalPos (beta:=beta) radix b precision)
            = (nNormMin radix precision : ℝ) * (radix : ℝ) ^ (-b.dExp)⌝⦄ := by
  sorry

-- ---------------------------------------------------------------------------
-- Closest/Normal placeholders (from Pff.v sections)

-- Coq-style rounding relation to the closest representable float (placeholder)
def Closest {beta : Int}
    (bo : Fbound_skel) (radix : ℝ) (r : ℝ)
    (f : FloatSpec.Core.Defs.FlocqFloat beta) : Prop := True

-- Coq-style normality predicate (placeholder)
def Fnormal {beta : Int}
    (radix : ℝ) (bo : Fbound_skel)
    (f : FloatSpec.Core.Defs.FlocqFloat beta) : Prop := True

def Fsubnormal {beta : Int}
    (radix : ℝ) (bo : Fbound_skel)
    (f : FloatSpec.Core.Defs.FlocqFloat beta) : Prop := True

-- Minimal placeholder for the Coq `digit` function used in later statements.
noncomputable def Fdigit {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) : Nat := 0

-- Predicate: zero mantissa (Coq: `is_Fzero`). Placed early for downstream uses.
def is_Fzero {beta : Int} (x : FloatSpec.Core.Defs.FlocqFloat beta) : Prop :=
  x.Fnum = 0

-- Coq-style boundedness predicate (placeholder)
-- ---------------------------------------------------------------------------
-- Parity on floats and neighbor operations (skeleton placeholders)

-- Coq uses predicates like FNeven/FNodd and neighbors FNSucc/FNPred.
-- We introduce minimal placeholders so that theorem statements compile.
def FNeven {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Prop := True

def FNodd {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Prop := True

def FNSucc {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : FloatSpec.Core.Defs.FlocqFloat beta :=
  p

def FNPred {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : FloatSpec.Core.Defs.FlocqFloat beta :=
  p

-- Parity behavior of successor (Coq: FevenSucProp)
noncomputable def FevenSucProp_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem FevenSucProp {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (FevenSucProp_check (beta:=beta) b radix precision p) : Id Unit)
    ⦃⇓_ => ⌜(Fodd (beta:=beta) p →
    Feven (beta:=beta) (FNSucc (beta:=beta) b radix precision p)) ∧
            (Feven (beta:=beta) p →
              Fodd (beta:=beta) (FNSucc (beta:=beta) b radix precision p))⌝⦄ := by
  sorry

-- Parity corollaries for successor (Coq: FoddSuc / FevenSuc)
noncomputable def FoddSuc_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FoddSuc` — if a float is odd, its successor is even. -/
theorem FoddSuc {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fodd (beta:=beta) p⌝⦄
    (pure (FoddSuc_check (beta:=beta) b radix precision p) : Id Unit)
    ⦃⇓_ => ⌜Feven (beta:=beta) (FNSucc (beta:=beta) b radix precision p)⌝⦄ := by
  sorry

noncomputable def FevenSuc_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FevenSuc` — if a float is even, its successor is odd. -/
theorem FevenSuc {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Feven (beta:=beta) p⌝⦄
    (pure (FevenSuc_check (beta:=beta) b radix precision p) : Id Unit)
    ⦃⇓_ => ⌜Fodd (beta:=beta) (FNSucc (beta:=beta) b radix precision p)⌝⦄ := by
  sorry

-- EvenClosest: closest rounding with tie-breaking toward even (or uniqueness)
def EvenClosest {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (r : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Prop :=
  Closest (beta:=beta) b radix r p ∧
  (FNeven (beta:=beta) b radix precision p ∨
    (∀ q : FloatSpec.Core.Defs.FlocqFloat beta,
      Closest (beta:=beta) b radix r q → q = p))

-- ---------------------------------------------------------------------------
-- Rounding operators (RND_*) and canonicity (skeletons to mirror Coq Pff.v)

-- Minimal placeholder: canonicity predicate used by RND_* theorems
def Fcanonic {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (f : FloatSpec.Core.Defs.FlocqFloat beta) : Prop := True

noncomputable def FcanonicBound_check {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FcanonicBound` — canonical floats are bounded. -/
theorem FcanonicBound {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fcanonic (beta:=beta) radix b p⌝⦄
    (pure (FcanonicBound_check (beta:=beta) radix b p) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b p⌝⦄ := by
  sorry

noncomputable def FcanonicFopp_check {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FcanonicFopp` — canonicity preserved under float negation. -/
theorem FcanonicFopp {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fcanonic (beta:=beta) radix b p⌝⦄
    (pure (FcanonicFopp_check (beta:=beta) radix b p) : Id Unit)
    ⦃⇓_ => ⌜Fcanonic (beta:=beta) radix b (Fopp p)⌝⦄ := by
  sorry

noncomputable def FcanonicFabs_check {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FcanonicFabs` — canonicity preserved under float absolute value. -/
theorem FcanonicFabs {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fcanonic (beta:=beta) radix b p⌝⦄
    (pure (FcanonicFabs_check (beta:=beta) radix b p) : Id Unit)
    ⦃⇓_ => ⌜Fcanonic (beta:=beta) radix b (Fabs p)⌝⦄ := by
  sorry

-- Relative ordering of canonical floats (Coq: `FcanonicLtPos`)
noncomputable def FcanonicLtPos_check {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FcanonicLtPos` — for canonical floats `p` and `q`, if
`0 ≤ F2R p < F2R q`, then either the exponent of `p` is strictly
smaller than that of `q`, or the exponents match and the mantissa of `p`
is strictly smaller. -/
theorem FcanonicLtPos {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fcanonic (beta:=beta) radix b p ∧
        Fcanonic (beta:=beta) radix b q ∧
        0 ≤ _root_.F2R (beta:=beta) p ∧
        _root_.F2R (beta:=beta) p < _root_.F2R (beta:=beta) q⌝⦄
    (pure (FcanonicLtPos_check (beta:=beta) radix b p q) : Id Unit)
    ⦃⇓_ => ⌜p.Fexp < q.Fexp ∨
            (p.Fexp = q.Fexp ∧ p.Fnum < q.Fnum)⌝⦄ := by
  sorry

noncomputable def Fcanonic_Rle_Zle_check {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `Fcanonic_Rle_Zle` — canonical floats ordered by absolute value have
    nondecreasing exponents. -/
theorem Fcanonic_Rle_Zle {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fcanonic (beta:=beta) radix b x ∧
        Fcanonic (beta:=beta) radix b y ∧
        |_root_.F2R (beta:=beta) x|
          ≤ |_root_.F2R (beta:=beta) y|⌝⦄
    (pure (Fcanonic_Rle_Zle_check (beta:=beta) radix b x y) : Id Unit)
    ⦃⇓_ => ⌜x.Fexp ≤ y.Fexp⌝⦄ := by
  sorry

noncomputable def FcanonicLtNeg_check {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FcanonicLtNeg` — for canonical floats `p` and `q`, if
`_root_.F2R q ≤ 0` and `_root_.F2R p < _root_.F2R q`, then either the exponent
of `q` is strictly smaller than the exponent of `p`, or the exponents match and
the mantissa of `p` is strictly smaller. -/
theorem FcanonicLtNeg {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fcanonic (beta:=beta) radix b p ∧
        Fcanonic (beta:=beta) radix b q ∧
        _root_.F2R (beta:=beta) q ≤ 0 ∧
        _root_.F2R (beta:=beta) p < _root_.F2R (beta:=beta) q⌝⦄
    (pure (FcanonicLtNeg_check (beta:=beta) radix b p q) : Id Unit)
    ⦃⇓_ => ⌜q.Fexp < p.Fexp ∨
            (p.Fexp = q.Fexp ∧ p.Fnum < q.Fnum)⌝⦄ := by
  sorry

-- Placeholders for rounding operators on nonnegative reals and their variants
def RND_Min_Pos {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int)
    (r : ℝ) : FloatSpec.Core.Defs.FlocqFloat beta :=
  -- Skeleton: return an arbitrary float; semantics deferred
  ⟨0, 0⟩

-- ---------------------------------------------------------------------------
-- Normalization helper (Coq: Fnormalize) and its basic properties

/-- Placeholder for the Coq `Fnormalize` operator. The Lean port keeps the
structure abstract by simply returning the input float; detailed behavior will
be filled in when the full normalization pipeline is migrated. -/
noncomputable def Fnormalize {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    FloatSpec.Core.Defs.FlocqFloat beta :=
  p

noncomputable def FnormalizeCorrect_check {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FnormalizeCorrect` — the normalized float represents the same real
value as the original. -/
theorem FnormalizeCorrect {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (FnormalizeCorrect_check (beta:=beta) radix b precision p) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (beta:=beta)
            (Fnormalize (beta:=beta) radix b precision p) =
            _root_.F2R (beta:=beta) p⌝⦄ := by
  intro _
  unfold Fnormalize
  rfl

noncomputable def FnormalizeBounded_check {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FnormalizeBounded` — normalization preserves boundedness. -/
theorem FnormalizeBounded {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b p⌝⦄
    (pure (FnormalizeBounded_check (beta:=beta) radix b precision p) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b
            (Fnormalize (beta:=beta) radix b precision p)⌝⦄ := by
  intro hb
  unfold Fnormalize
  simpa using hb

noncomputable def FnormalizeCanonic_check {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FnormalizeCanonic` — normalization yields a canonical float. -/
theorem FnormalizeCanonic {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b p⌝⦄
    (pure (FnormalizeCanonic_check (beta:=beta) radix b precision p) : Id Unit)
    ⦃⇓_ => ⌜Fcanonic (beta:=beta) radix b
            (Fnormalize (beta:=beta) radix b precision p)⌝⦄ := by
  intro _
  simp [ FnormalizeCanonic_check, Fcanonic, Fnormalize]

noncomputable def FcanonicFnormalizeEq_check {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FcanonicFnormalizeEq` — canonical floats are fixed points of
`Fnormalize`. -/
theorem FcanonicFnormalizeEq {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fcanonic (beta:=beta) radix b p⌝⦄
    (pure (FcanonicFnormalizeEq_check (beta:=beta) radix b precision p) : Id Unit)
    ⦃⇓_ => ⌜Fnormalize (beta:=beta) radix b precision p = p⌝⦄ := by
  intro _
  unfold Fnormalize
  rfl

noncomputable def FcanonicPosFexpRlt_check {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FcanonicPosFexpRlt` — among nonnegative canonical floats, a strictly
smaller exponent yields a strictly smaller value. -/
theorem FcanonicPosFexpRlt {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fcanonic (beta:=beta) radix b x ∧
        Fcanonic (beta:=beta) radix b y ∧
        0 ≤ _root_.F2R (beta:=beta) x ∧
        0 ≤ _root_.F2R (beta:=beta) y ∧
        x.Fexp < y.Fexp⌝⦄
    (pure (FcanonicPosFexpRlt_check (beta:=beta) radix b x y) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (beta:=beta) x < _root_.F2R (beta:=beta) y⌝⦄ := by
  sorry

noncomputable def FcanonicNegFexpRlt_check {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FcanonicNegFexpRlt` — among nonpositive canonical floats, a strictly
larger exponent forces a strictly smaller real value. -/
theorem FcanonicNegFexpRlt {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fcanonic (beta:=beta) radix b x ∧
        Fcanonic (beta:=beta) radix b y ∧
        _root_.F2R (beta:=beta) x ≤ 0 ∧
        _root_.F2R (beta:=beta) y ≤ 0 ∧
        x.Fexp < y.Fexp⌝⦄
    (pure (FcanonicNegFexpRlt_check (beta:=beta) radix b x y) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (beta:=beta) y < _root_.F2R (beta:=beta) x⌝⦄ := by
  sorry

noncomputable def NormalAndSubNormalNotEq_check {beta : Int}
    (radix : ℝ) (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `NormalAndSubNormalNotEq` — a normal float and a subnormal float
represent different real numbers. -/
theorem NormalAndSubNormalNotEq {beta : Int}
    (radix : ℝ) (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fnormal (beta:=beta) radix b p ∧
        Fsubnormal (beta:=beta) radix b q⌝⦄
    (pure (NormalAndSubNormalNotEq_check (beta:=beta) radix b p q) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (beta:=beta) p ≠ _root_.F2R (beta:=beta) q⌝⦄ := by
  sorry

noncomputable def FcanonicUnique_check {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FcanonicUnique` — canonical floats that represent the same real
number are equal as floats. -/
theorem FcanonicUnique {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fcanonic (beta:=beta) radix b p ∧
        Fcanonic (beta:=beta) radix b q ∧
        _root_.F2R (beta:=beta) p = _root_.F2R (beta:=beta) q⌝⦄
    (pure (FcanonicUnique_check (beta:=beta) radix b p q) : Id Unit)
    ⦃⇓_ => ⌜p = q⌝⦄ := by
  sorry

noncomputable def FcanonicLeastExp_check {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FcanonicLeastExp` — a canonical float with the same value as a
bounded float has exponent no larger than the bounded one. -/
theorem FcanonicLeastExp {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜_root_.F2R (beta:=beta) x = _root_.F2R (beta:=beta) y ∧
        Fbounded (beta:=beta) b x ∧
        Fcanonic (beta:=beta) radix b y⌝⦄
    (pure (FcanonicLeastExp_check (beta:=beta) radix b x y) : Id Unit)
    ⦃⇓_ => ⌜y.Fexp ≤ x.Fexp⌝⦄ := by
  sorry

-- Auxiliary boundedness of `RND_Min_Pos` on nonnegative reals (Coq: RND_Min_Pos_bounded_aux)
noncomputable def RND_Min_Pos_bounded_aux_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) : Unit :=
  ()

/-- Coq: `RND_Min_Pos_bounded_aux` — for nonnegative `r`, the value of
    `RND_Min_Pos r` is bounded according to the bound structure `b`. -/
theorem RND_Min_Pos_bounded_aux {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) :
    ⦃⌜0 ≤ r⌝⦄
    (pure (RND_Min_Pos_bounded_aux_check (beta:=beta) b radix p r) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b (RND_Min_Pos (beta:=beta) b radix p r)⌝⦄ := by
  sorry

noncomputable def RND_Min_Pos_canonic_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) : Unit :=
  ()

/-- Coq: `RND_Min_Pos_canonic` — for nonnegative `r`, `RND_Min_Pos r` is canonical.
    Stated using project Hoare-triple syntax; proof deferred. -/
theorem RND_Min_Pos_canonic {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) :
    ⦃⌜0 ≤ r⌝⦄
    (pure (RND_Min_Pos_canonic_check (beta:=beta) b radix p r) : Id Unit)
    ⦃⇓_ => ⌜Fcanonic (beta:=beta) radix b (RND_Min_Pos (beta:=beta) b radix p r)⌝⦄ := by
  sorry

-- Lower rounding on nonnegative reals is ≤ the input (Coq: RND_Min_Pos_Rle)
noncomputable def RND_Min_Pos_Rle_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) : Unit :=
  ()

/-- Coq: `RND_Min_Pos_Rle` — for nonnegative `r`, the value of
    `RND_Min_Pos r` (interpreted in ℝ) is less than or equal to `r`. -/
theorem RND_Min_Pos_Rle {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) :
    ⦃⌜0 ≤ r⌝⦄
    (pure (RND_Min_Pos_Rle_check (beta:=beta) b radix p r) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (RND_Min_Pos (beta:=beta) b radix p r) ≤ r⌝⦄ := by
  sorry

-- Monotonicity of `RND_Min_Pos` w.r.t. the real input (Coq: RND_Min_Pos_monotone)
noncomputable def RND_Min_Pos_monotone_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r₁ r₂ : ℝ) : Unit :=
  ()

/-- Coq: `RND_Min_Pos_monotone` — for nonnegative `r₁ ≤ r₂`, the lower rounding
    on nonnegative reals is monotone in the sense that the real value of
    `RND_Min_Pos r₁` is less than or equal to that of `RND_Min_Pos r₂`.
    We mirror the statement using the hoare-triple style and defer the proof. -/
theorem RND_Min_Pos_monotone {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r₁ r₂ : ℝ) :
    ⦃⌜0 ≤ r₁ ∧ r₁ ≤ r₂⌝⦄
    (pure (RND_Min_Pos_monotone_check (beta:=beta) b radix p r₁ r₂) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (RND_Min_Pos (beta:=beta) b radix p r₁)
            ≤ _root_.F2R (RND_Min_Pos (beta:=beta) b radix p r₂)⌝⦄ := by
  sorry

-- Projector property for `RND_Min_Pos` on canonical inputs (Coq: RND_Min_Pos_projector)
noncomputable def RND_Min_Pos_projector_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int)
    (f : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `RND_Min_Pos_projector` — for a canonical nonnegative float `f`,
    rounding the real value of `f` with `RND_Min_Pos` projects back to `f`.
    We state this equality at the real level via `F2R` and leave the proof sorry. -/
theorem RND_Min_Pos_projector {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int)
    (f : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜0 ≤ _root_.F2R f ∧ Fcanonic (beta:=beta) radix b f⌝⦄
    (pure (RND_Min_Pos_projector_check (beta:=beta) b radix p f) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (RND_Min_Pos (beta:=beta) b radix p (_root_.F2R f))
            = _root_.F2R f⌝⦄ := by
  sorry

-- Roundings of any real (Coq-style top-level RND operators)
def RND_Min {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int)
    (r : ℝ) : FloatSpec.Core.Defs.FlocqFloat beta :=
  -- Skeleton: delegate to the nonnegative operator (sign handling deferred).
  RND_Min_Pos (beta:=beta) b radix p r

noncomputable def RND_Min_canonic_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) : Unit :=
  ()

/-- Coq: `RND_Min_canonic` — canonicity of the lower rounding `RND_Min`.
    We mirror the statement using the project Hoare-triple style. -/
theorem RND_Min_canonic {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) :
    ⦃⌜True⌝⦄
    (pure (RND_Min_canonic_check (beta:=beta) b radix p r) : Id Unit)
    ⦃⇓_ => ⌜Fcanonic (beta:=beta) radix b (RND_Min (beta:=beta) b radix p r)⌝⦄ := by
  sorry

-- Upper rounding operators (mirroring Coq RND_Max_*)

def RND_Max_Pos {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int)
    (r : ℝ) : FloatSpec.Core.Defs.FlocqFloat beta :=
  -- Skeleton: return an arbitrary float; semantics deferred
  ⟨0, 0⟩

noncomputable def RND_Max_Pos_canonic_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) : Unit :=
  ()

/-- Coq: `RND_Max_Pos_canonic` — for nonnegative `r`, `RND_Max_Pos r` is canonical.
    Stated using project Hoare-triple syntax; proof deferred. -/
theorem RND_Max_Pos_canonic {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) :
    ⦃⌜0 ≤ r⌝⦄
    (pure (RND_Max_Pos_canonic_check (beta:=beta) b radix p r) : Id Unit)
    ⦃⇓_ => ⌜Fcanonic (beta:=beta) radix b (RND_Max_Pos (beta:=beta) b radix p r)⌝⦄ := by
  sorry

-- Lower rounding correctness on nonnegative reals (Coq: RND_Min_Pos_correct)
noncomputable def RND_Min_Pos_correct_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) : Unit :=
  ()

/-- Coq: `RND_Min_Pos_correct` — for nonnegative `r`, `RND_Min_Pos r` is
    an extremal lower witness captured by `isMin`. -/
theorem RND_Min_Pos_correct {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) :
    ⦃⌜0 ≤ r⌝⦄
    (pure (RND_Min_Pos_correct_check (beta:=beta) b radix p r) : Id Unit)
    ⦃⇓_ => ⌜isMin (α:=FloatSpec.Core.Defs.FlocqFloat beta) b radix r
              (RND_Min_Pos (beta:=beta) b radix p r)⌝⦄ := by
  sorry

-- Upper rounding is ≥ the input on nonnegative reals (Coq: RND_Max_Pos_Rle)
noncomputable def RND_Max_Pos_Rle_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) : Unit :=
  ()

/-- Coq: `RND_Max_Pos_Rle` — for nonnegative `r`, the value of
    `RND_Max_Pos r` (interpreted in ℝ) is greater than or equal to `r`. -/
theorem RND_Max_Pos_Rle {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) :
    ⦃⌜0 ≤ r⌝⦄
    (pure (RND_Max_Pos_Rle_check (beta:=beta) b radix p r) : Id Unit)
    ⦃⇓_ => ⌜r ≤ _root_.F2R (RND_Max_Pos (beta:=beta) b radix p r)⌝⦄ := by
  sorry

-- Upper rounding correctness on nonnegative reals (Coq: RND_Max_Pos_correct)
noncomputable def RND_Max_Pos_correct_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) : Unit :=
  ()

/-- Coq: `RND_Max_Pos_correct` — for nonnegative `r`, `RND_Max_Pos r` is
    an extremal upper witness captured by `isMax`. -/
theorem RND_Max_Pos_correct {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) :
    ⦃⌜0 ≤ r⌝⦄
    (pure (RND_Max_Pos_correct_check (beta:=beta) b radix p r) : Id Unit)
    ⦃⇓_ => ⌜isMax (α:=FloatSpec.Core.Defs.FlocqFloat beta) b radix r
              (RND_Max_Pos (beta:=beta) b radix p r)⌝⦄ := by
  sorry

-- Roundings of any real (upper rounding)
def RND_Max {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int)
    (r : ℝ) : FloatSpec.Core.Defs.FlocqFloat beta :=
  -- Skeleton: delegate to the nonnegative operator (sign handling deferred).
  RND_Max_Pos (beta:=beta) b radix p r

noncomputable def RND_Max_canonic_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) : Unit :=
  ()

/-- Coq: `RND_Max_canonic` — canonicity of the upper rounding `RND_Max`.
    Mirrored with the same Hoare-triple style as other RND theorems. -/
theorem RND_Max_canonic {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) :
    ⦃⌜True⌝⦄
    (pure (RND_Max_canonic_check (beta:=beta) b radix p r) : Id Unit)
    ⦃⇓_ => ⌜Fcanonic (beta:=beta) radix b (RND_Max (beta:=beta) b radix p r)⌝⦄ := by
  sorry

-- Correctness of lower rounding (Coq: RND_Min_correct)
noncomputable def RND_Min_correct_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int)
    (r : ℝ) : Unit :=
  ()

/-- Coq: `RND_Min_correct` — `RND_Min` produces a lower extremal value. -/
theorem RND_Min_correct {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) :
    ⦃⌜True⌝⦄
    (pure (RND_Min_correct_check (beta:=beta) b radix p r) : Id Unit)
    ⦃⇓_ => ⌜isMin (α:=FloatSpec.Core.Defs.FlocqFloat beta) b radix r (RND_Min (beta:=beta) b radix p r)⌝⦄ := by
  sorry

-- Correctness of upper rounding (Coq: RND_Max_correct)
noncomputable def RND_Max_correct_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int)
    (r : ℝ) : Unit :=
  ()

/-- Coq: `RND_Max_correct` — `RND_Max` produces an upper extremal value. -/
theorem RND_Max_correct {beta : Int}
    (b : Fbound_skel) (radix : Int) (p : Int) (r : ℝ) :
    ⦃⌜True⌝⦄
    (pure (RND_Max_correct_check (beta:=beta) b radix p r) : Id Unit)
    ⦃⇓_ => ⌜isMax (α:=FloatSpec.Core.Defs.FlocqFloat beta) b radix r (RND_Max (beta:=beta) b radix p r)⌝⦄ := by
  sorry

-- Even-closest rounding: canonicity (Coq: RND_EvenClosest_canonic)
noncomputable def RND_EvenClosest_canonic_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (precision : Nat)
    (r : ℝ) : Unit :=
  ()

/-- Coq: `RND_EvenClosest_canonic` — even-tie closest rounding is canonic. -/
theorem RND_EvenClosest_canonic {beta : Int}
    (b : Fbound_skel) (radix : Int) (precision : Nat)
    (r : ℝ) :
    ⦃⌜True⌝⦄
    (pure (RND_EvenClosest_canonic_check (beta:=beta) b radix precision r) : Id Unit)
    ⦃⇓_ => ⌜Fcanonic (beta:=beta) radix b (RND_Min (beta:=beta) b radix (Int.ofNat precision) r)⌝⦄ := by
  sorry

-- Even-closest rounding: correctness (Coq: RND_EvenClosest_correct)
noncomputable def RND_EvenClosest_correct_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (precision : Nat)
    (r : ℝ) : Unit :=
  ()

/-- Coq: `RND_EvenClosest_correct` — correctness of even-tie closest rounding. -/
theorem RND_EvenClosest_correct {beta : Int}
    (b : Fbound_skel) (radix : Int) (precision : Nat)
    (r : ℝ) :
    ⦃⌜True⌝⦄
    (pure (RND_EvenClosest_correct_check (beta:=beta) b radix precision r) : Id Unit)
    ⦃⇓_ => ⌜True⌝⦄ := by
  sorry

-- Totality of EvenClosest
noncomputable def EvenClosestTotal_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat) (r : ℝ) : Unit :=
  ()

/-- Coq: `EvenClosestTotal` — `EvenClosest` is total. -/
theorem EvenClosestTotal {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat) (r : ℝ) :
    ⦃⌜True⌝⦄
    (pure (EvenClosestTotal_check (beta:=beta) b radix precision r) : Id Unit)
    ⦃⇓_ => ⌜∃ p : FloatSpec.Core.Defs.FlocqFloat beta,
            EvenClosest (beta:=beta) b radix precision r p⌝⦄ := by
  sorry

-- Parity under negation (Coq: FevenFop)
noncomputable def FevenFop_check {beta : Int}
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FevenFop` — if a float is even, its negation is even. -/
theorem FevenFop {beta : Int}
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Feven (beta:=beta) p⌝⦄
    (pure (FevenFop_check (beta:=beta) p) : Id Unit)
    ⦃⇓_ => ⌜Feven (beta:=beta) (FloatSpec.Calc.Operations.Fopp (beta:=beta) p)⌝⦄ := by
  sorry

-- Normalized-odd is preserved under equal real value (Coq: FNoddEq)
noncomputable def FNoddEq_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (f1 f2 : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FNoddEq` — if `f1` and `f2` are bounded, have equal real value,
    and `f1` is FNodd, then `f2` is FNodd. -/
theorem FNoddEq {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (f1 f2 : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b f1 ∧ Fbounded (beta:=beta) b f2 ∧
        _root_.F2R f1 = _root_.F2R f2 ∧ FNodd (beta:=beta) b radix precision f1⌝⦄
    (pure (FNoddEq_check (beta:=beta) b radix precision f1 f2) : Id Unit)
    ⦃⇓_ => ⌜FNodd (beta:=beta) b radix precision f2⌝⦄ := by
  sorry

-- Normalized-even is preserved under equal real value (Coq: FNevenEq)
noncomputable def FNevenEq_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (f1 f2 : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FNevenEq` — if `f1` and `f2` are bounded, have equal real value,
    and `f1` is FNeven, then `f2` is FNeven. -/
theorem FNevenEq {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (f1 f2 : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b f1 ∧ Fbounded (beta:=beta) b f2 ∧
        _root_.F2R f1 = _root_.F2R f2 ∧ FNeven (beta:=beta) b radix precision f1⌝⦄
    (pure (FNevenEq_check (beta:=beta) b radix precision f1 f2) : Id Unit)
    ⦃⇓_ => ⌜FNeven (beta:=beta) b radix precision f2⌝⦄ := by
  sorry

-- Normalized-even under negation (Coq: FNevenFop)
noncomputable def FNevenFop_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FNevenFop` — if a float is normalized-even, its negation is normalized-even. -/
theorem FNevenFop {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜FNeven (beta:=beta) b radix precision p⌝⦄
    (pure (FNevenFop_check (beta:=beta) b radix precision p) : Id Unit)
    ⦃⇓_ => ⌜FNeven (beta:=beta) b radix precision (FloatSpec.Calc.Operations.Fopp (beta:=beta) p)⌝⦄ := by
  sorry

-- Successor parity for normalized predicates (Coq: FNoddSuc / FNevenSuc)
noncomputable def FNoddSuc_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FNoddSuc` — for bounded `p`, normalized-odd implies successor is normalized-even. -/
theorem FNoddSuc {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b p ∧ FNodd (beta:=beta) b radix precision p⌝⦄
    (pure (FNoddSuc_check (beta:=beta) b radix precision p) : Id Unit)
    ⦃⇓_ => ⌜FNeven (beta:=beta) b radix precision (FNSucc (beta:=beta) b radix precision p)⌝⦄ := by
  sorry

noncomputable def FNevenSuc_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FNevenSuc` — for bounded `p`, normalized-even implies successor is normalized-odd. -/
theorem FNevenSuc {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b p ∧ FNeven (beta:=beta) b radix precision p⌝⦄
    (pure (FNevenSuc_check (beta:=beta) b radix precision p) : Id Unit)
    ⦃⇓_ => ⌜FNodd (beta:=beta) b radix precision (FNSucc (beta:=beta) b radix precision p)⌝⦄ := by
  sorry

-- Disjunction for normalized parity (Coq: FNevenOrFNodd)
noncomputable def FNevenOrFNodd_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem FNevenOrFNodd {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (FNevenOrFNodd_check (beta:=beta) b radix precision p) : Id Unit)
    ⦃⇓_ => ⌜FNeven (beta:=beta) b radix precision p ∨ FNodd (beta:=beta) b radix precision p⌝⦄ := by
  sorry

-- Incompatibility of normalized odd and even (Coq: FnOddNEven)
noncomputable def FnOddNEven_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (n : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem FnOddNEven {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (n : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜FNodd (beta:=beta) b radix precision n⌝⦄
    (pure (FnOddNEven_check (beta:=beta) b radix precision n) : Id Unit)
    ⦃⇓_ => ⌜¬ FNeven (beta:=beta) b radix precision n⌝⦄ := by
  sorry

-- Existence of a closest representation (Coq: `ClosestTotal`)
noncomputable def ClosestTotal_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ) (r : ℝ) : Unit :=
  ()

/-- Coq: `ClosestTotal` — for any real `r`, there exists a float `f`
    that is a closest representation according to `Closest`.
    We use the Hoare-triple style and defer the proof. -/
theorem ClosestTotal {beta : Int}
    (bo : Fbound_skel) (radix : ℝ) (r : ℝ) :
    ⦃⌜True⌝⦄
    (pure (ClosestTotal_check (beta:=beta) bo radix r) : Id Unit)
    ⦃⇓_ => ⌜∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
            Closest (beta:=beta) bo radix r f⌝⦄ := by
  sorry

-- Compatibility of `Closest` w.r.t. equalities (Coq: `ClosestCompatible`)
noncomputable def ClosestCompatible_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ) : Unit :=
  ()

/-- Coq: `ClosestCompatible` — the `Closest` relation is compatible
    with equality of reals and representations. -/
theorem ClosestCompatible {beta : Int}
    (bo : Fbound_skel) (radix : ℝ) :
    ⦃⌜True⌝⦄
    (pure (ClosestCompatible_check (beta:=beta) bo radix) : Id Unit)
    ⦃⇓_ => ⌜CompatibleP (Closest (beta:=beta) bo radix)⌝⦄ := by
  sorry

-- Minimal conditions imply `Closest r min` (Coq: `ClosestMin`)
noncomputable def ClosestMin_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (r : ℝ)
    (min max : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `ClosestMin` — if `min` and `max` bracket `r` appropriately and are
    extremal for `isMin/isMax`, then `min` is a closest representation. -/
theorem ClosestMin {beta : Int}
    (bo : Fbound_skel) (radixZ : Int) (radixR : ℝ)
    (r : ℝ)
    (min max : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜isMin (α:=FloatSpec.Core.Defs.FlocqFloat beta) bo radixZ r min ∧
        isMax (α:=FloatSpec.Core.Defs.FlocqFloat beta) bo radixZ r max ∧
        2 * r ≤ _root_.F2R min + _root_.F2R max⌝⦄
    (pure (ClosestMin_check (beta:=beta) bo radixR r min max) : Id Unit)
    ⦃⇓_ => ⌜Closest (beta:=beta) bo radixR r min⌝⦄ := by
  sorry

-- Maximal conditions imply `Closest r max` (Coq: `ClosestMax`)
noncomputable def ClosestMax_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (r : ℝ)
    (min max : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `ClosestMax` — if `min` and `max` bracket `r` appropriately and are
    extremal for `isMin/isMax`, then `max` is a closest representation. -/
theorem ClosestMax {beta : Int}
    (bo : Fbound_skel) (radixZ : Int) (radixR : ℝ)
    (r : ℝ)
    (min max : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜isMin (α:=FloatSpec.Core.Defs.FlocqFloat beta) bo radixZ r min ∧
        isMax (α:=FloatSpec.Core.Defs.FlocqFloat beta) bo radixZ r max ∧
        _root_.F2R min + _root_.F2R max ≤ 2 * r⌝⦄
    (pure (ClosestMax_check (beta:=beta) bo radixR r min max) : Id Unit)
    ⦃⇓_ => ⌜Closest (beta:=beta) bo radixR r max⌝⦄ := by
  sorry

-- Disjunction: any candidate is either a min or a max (Coq: `ClosestMinOrMax`)
noncomputable def ClosestMinOrMax_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ) : Unit :=
  ()

/-- Coq: `ClosestMinOrMax` — any closest candidate is either a min-side or
    a max-side witness of closeness. -/
theorem ClosestMinOrMax {beta : Int}
    (bo : Fbound_skel) (radixZ : Int) (radixR : ℝ) :
    ⦃⌜True⌝⦄
    (pure (ClosestMinOrMax_check (beta:=beta) bo radixR) : Id Unit)
    ⦃⇓_ => ⌜MinOrMaxP (Closest (beta:=beta) bo radixR)⌝⦄ := by
  sorry

-- Zero case for Closest rounding (Coq: `ClosestZero`)
noncomputable def ClosestZero_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ) (r : ℝ)
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `ClosestZero` — if `x` is a closest rounding of `r` and `r = 0`,
    then the real value of `x` is `0`. We phrase this using the project
    `Closest` predicate and `F2R` interpretation. -/
theorem ClosestZero {beta : Int}
    (bo : Fbound_skel) (radix : ℝ) (r : ℝ)
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Closest (beta:=beta) bo radix r x ∧ r = 0⌝⦄
    (pure (ClosestZero_check (beta:=beta) bo radix r x) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R x = 0⌝⦄ := by
  sorry

-- ---------------------------------------------------------------------------
-- Min/Max existence over finite lists (from Coq Pff.v)

/-
Coq: `FboundedMboundPos`

Construct a bounded float whose real value equals `m * radix^z` when the
mantissa/exponent bounds hold. The real radix is obtained from the integer
radix via coercion so that `powerRZ` can be reused verbatim.
-/
noncomputable def FboundedMboundPos_check {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (z m : Int) : Unit :=
  ()

theorem FboundedMboundPos {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (precision : Nat)
    (z m : Int) :
    ⦃⌜0 ≤ m ∧
        m ≤ Zpower_nat_int radix precision ∧
        - b.dExp ≤ z⌝⦄
    (pure (FboundedMboundPos_check (beta:=beta) b radix z m) : Id Unit)
    ⦃⇓_ => ⌜∃ c : FloatSpec.Core.Defs.FlocqFloat beta,
        Fbounded b c ∧
        _root_.F2R c = (m : ℝ) * (radix : ℝ) ^ z⌝⦄ := by
  sorry

/-- Coq: `FboundedMbound` — extends `FboundedMboundPos` by allowing
negative mantissas via symmetry. -/
noncomputable def FboundedMbound_check {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (z m : Int) : Unit :=
  ()

theorem FboundedMbound {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (precision : Nat)
    (z m : Int) :
    ⦃⌜|m| ≤ Zpower_nat_int radix precision ∧
        - b.dExp ≤ z⌝⦄
    (pure (FboundedMbound_check (beta:=beta) b radix z m) : Id Unit)
    ⦃⇓_ => ⌜∃ c : FloatSpec.Core.Defs.FlocqFloat beta,
        Fbounded b c ∧
        _root_.F2R c = (m : ℝ) * (radix : ℝ) ^ z⌝⦄ := by
  sorry

/-!
Coq: `MinExList`

For any real `r` and finite list `L` of floats, either every element of `L`
has value strictly greater than `r`, or there exists an element `min ∈ L`
such that `F2R min ≤ r` and it is minimal among those at most `r`.

We state this property over the project float representation and leave the
proof as `sorry`, following the hoare-triple pattern used across this file.
-/
noncomputable def MinExList_check {beta : Int}
    (r : ℝ) (L : List (FloatSpec.Core.Defs.FlocqFloat beta)) : Unit :=
  ()

theorem MinExList {beta : Int}
    (r : ℝ) (L : List (FloatSpec.Core.Defs.FlocqFloat beta)) :
    ⦃⌜True⌝⦄
    (pure (MinExList_check (beta:=beta) r L) : Id Unit)
    ⦃⇓_ => ⌜(∀ f, f ∈ L → r < _root_.F2R f) ∨
            (∃ min, min ∈ L ∧ _root_.F2R min ≤ r ∧
              ∀ f, f ∈ L → _root_.F2R f ≤ r → _root_.F2R f ≤ _root_.F2R min)⌝⦄ := by
  sorry

/-!
Coq: `MinEx`

For any real `r`, there exists a float `min` that is a lower extremal witness
for `r` (captured here by the abstract predicate `isMin`). We keep the
statement abstract with respect to the bound structure and radix since this
file provides only skeletons; the concrete Coq proof uses project-specific
constructions such as `mBFloat` and `boundR`.
-/
noncomputable def MinEx_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (r : ℝ) : Unit :=
  ()

theorem MinEx {beta : Int}
    (b : Fbound_skel) (radix : Int) (r : ℝ) :
    ⦃⌜True⌝⦄
    (pure (MinEx_check (beta:=beta) b radix r) : Id Unit)
    ⦃⇓_ => ⌜∃ min : FloatSpec.Core.Defs.FlocqFloat beta,
              isMin (α:=FloatSpec.Core.Defs.FlocqFloat beta) b radix r min⌝⦄ := by
  sorry

/-!
Coq: `MaxEx`

Dual existence result for an upper extremal witness `max` w.r.t. `isMax`.
-/
noncomputable def MaxEx_check {beta : Int}
    (b : Fbound_skel) (radix : Int) (r : ℝ) : Unit :=
  ()

theorem MaxEx {beta : Int}
    (b : Fbound_skel) (radix : Int) (r : ℝ) :
    ⦃⌜True⌝⦄
    (pure (MaxEx_check (beta:=beta) b radix r) : Id Unit)
    ⦃⇓_ => ⌜∃ max : FloatSpec.Core.Defs.FlocqFloat beta,
              isMax (α:=FloatSpec.Core.Defs.FlocqFloat beta) b radix r max⌝⦄ := by
  sorry

-- Equality under strict-leaning midpoint toward min (Coq: `ClosestMinEq`)
noncomputable def ClosestMinEq_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (r : ℝ)
    (min max p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `ClosestMinEq` — if `(2 * r) < (min + max)` and `p` is closest,
    then the closest equals `min` at the real level. -/
theorem ClosestMinEq {beta : Int}
    (bo : Fbound_skel) (radixZ : Int) (radixR : ℝ)
    (r : ℝ)
    (min max p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜isMin (α:=FloatSpec.Core.Defs.FlocqFloat beta) bo radixZ r min ∧
        isMax (α:=FloatSpec.Core.Defs.FlocqFloat beta) bo radixZ r max ∧
        2 * r < _root_.F2R min + _root_.F2R max ∧
        Closest (beta:=beta) bo radixR r p⌝⦄
    (pure (ClosestMinEq_check (beta:=beta) bo radixR r min max p) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R p = _root_.F2R min⌝⦄ := by
  sorry

-- Equality under strict-leaning midpoint toward max (Coq: `ClosestMaxEq`)
noncomputable def ClosestMaxEq_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (r : ℝ)
    (min max p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `ClosestMaxEq` — if `(min + max) < (2 * r)` and `p` is closest,
    then the closest equals `max` at the real level. -/
theorem ClosestMaxEq {beta : Int}
    (bo : Fbound_skel) (radixZ : Int) (radixR : ℝ)
    (r : ℝ)
    (min max p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜isMin (α:=FloatSpec.Core.Defs.FlocqFloat beta) bo radixZ r min ∧
        isMax (α:=FloatSpec.Core.Defs.FlocqFloat beta) bo radixZ r max ∧
        _root_.F2R min + _root_.F2R max < 2 * r ∧
        Closest (beta:=beta) bo radixR r p⌝⦄
    (pure (ClosestMaxEq_check (beta:=beta) bo radixR r min max p) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R p = _root_.F2R max⌝⦄ := by
  sorry

-- Monotonicity of the Closest relation (Coq: `ClosestMonotone`)
noncomputable def ClosestMonotone_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ) : Unit :=
  ()

/-- Coq: `ClosestMonotone` — the `Closest` relation is monotone
    in the sense captured by `MonotoneP` placeholder. -/
theorem ClosestMonotone {beta : Int}
    (bo : Fbound_skel) (radix : ℝ) :
    ⦃⌜True⌝⦄
    (pure (ClosestMonotone_check (beta:=beta) bo radix) : Id Unit)
    ⦃⇓_ => ⌜MonotoneP (Closest (beta:=beta) bo radix)⌝⦄ := by
  sorry

-- Rounded-mode packaging for `Closest` (Coq: `ClosestRoundedModeP`)
noncomputable def ClosestRoundedModeP_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ) : Unit :=
  ()

/-- Coq: `ClosestRoundedModeP` — the `Closest` relation forms a `RoundedModeP`.
    This gathers totality, compatibility, min-or-max disjunction and monotonicity
    into the `RoundedModeP` bundle for `Closest`. -/
theorem ClosestRoundedModeP {beta : Int}
    (bo : Fbound_skel) (radix : ℝ) :
    ⦃⌜True⌝⦄
    (pure (ClosestRoundedModeP_check (beta:=beta) bo radix) : Id Unit)
    ⦃⇓_ => ⌜RoundedModeP (Closest (beta:=beta) bo radix)⌝⦄ := by
  sorry

-- Symmetry under negation on the real side (Coq: `ClosestOpp`)
noncomputable def ClosestOpp_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) (r : ℝ) : Unit :=
  ()

/-- Coq: `ClosestOpp` — if `p` is a closest representation of `r`, then
    `Fopp p` is a closest representation of `-r`. -/
theorem ClosestOpp {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) (r : ℝ) :
    ⦃⌜Closest (beta:=beta) bo radix r p⌝⦄
    (pure (ClosestOpp_check (beta:=beta) bo radix p r) : Id Unit)
    ⦃⇓_ => ⌜Closest (beta:=beta) bo radix (-r) (Fopp p)⌝⦄ := by
  sorry

-- Absolute-value symmetry on the real side (Coq: `ClosestFabs`)
noncomputable def ClosestFabs_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) (r : ℝ) : Unit :=
  ()

/-- Coq: `ClosestFabs` — if `p` is a closest representation of `r`, then
    `Fabs p` is a closest representation of `|r|`. -/
theorem ClosestFabs {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) (r : ℝ) :
    ⦃⌜Closest (beta:=beta) bo radix r p⌝⦄
    (pure (ClosestFabs_check (beta:=beta) bo radix p r) : Id Unit)
    ⦃⇓_ => ⌜Closest (beta:=beta) bo radix (|r|) (Fabs p)⌝⦄ := by
  sorry

-- Ulp inequality for closest rounding (Coq: `ClosestUlp`)
noncomputable def ClosestUlp_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (p : ℝ) (q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `ClosestUlp` — if `q` is a closest representation of `p`, then
    `2 * |p - F2R q| ≤ ulp radix (FLT_exp ...) (F2R q)`. We keep the skeleton
    form referencing the Compat.lean `ulp` bridge. -/
theorem ClosestUlp {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (p : ℝ) (q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Closest (beta:=beta) bo radix p q⌝⦄
    (pure (ClosestUlp_check (beta:=beta) bo radix p q) : Id Unit)
    ⦃⇓_ => ⌜True⌝⦄ := by
  sorry

-- Exponent inequality from closest error (Coq: `ClosestExp`)
noncomputable def ClosestExp_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (p : Int) (x : ℝ) (q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `ClosestExp` — a strict bound on `(2 * |x - F2R q|)` implies
    `powerRZ radix p ≤ powerRZ radix (Fexp q)`. Skeleton only. -/
theorem ClosestExp {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (p : Int) (x : ℝ) (q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Closest (beta:=beta) bo radix x q ∧ (2 * |x - _root_.F2R q| : ℝ) ≤ (beta : ℝ) ^ p⌝⦄
    (pure (ClosestExp_check (beta:=beta) bo radix p x q) : Id Unit)
    ⦃⇓_ => ⌜(beta : ℝ) ^ p ≤ (beta : ℝ) ^ (q.Fexp)⌝⦄ := by
  sorry

-- Strict error-exp implication (Coq: `ClosestErrorExpStrict`)
noncomputable def ClosestErrorExpStrict_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) (x : ℝ) : Unit :=
  ()

theorem ClosestErrorExpStrict {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) (x : ℝ) :
    ⦃⌜Fbounded (beta:=beta) bo p ∧ Fbounded (beta:=beta) bo q ∧
        Closest (beta:=beta) bo radix x p ∧ _root_.F2R q = x - _root_.F2R p ∧
        _root_.F2R q ≠ 0⌝⦄
    (pure (ClosestErrorExpStrict_check (beta:=beta) bo radix p q x) : Id Unit)
    ⦃⇓_ => ⌜q.Fexp < p.Fexp⌝⦄ := by
  sorry

-- Idempotence property for Closest (Coq: `ClosestIdem`)
noncomputable def ClosestIdem_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem ClosestIdem {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) bo p ∧ Closest (beta:=beta) bo radix (_root_.F2R p) q⌝⦄
    (pure (ClosestIdem_check (beta:=beta) bo radix p q) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R p = _root_.F2R q⌝⦄ := by
  sorry

-- Error bound for closest rounding (Coq: `ClosestErrorBound`)
noncomputable def ClosestErrorBound_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) (x : ℝ) : Unit :=
  ()

/-- Coq: `ClosestErrorBound` — if `p` is a closest representation of `x` and
    `q` represents the error `x - F2R p`, then the magnitude of `q` is bounded by
    `Float 1 (Fexp p) / 2`. We phrase this using the Hoare-triple style and keep
    the proof as a placeholder. -/
theorem ClosestErrorBound {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) (x : ℝ) :
    ⦃⌜Fbounded (beta:=beta) bo p ∧ Closest (beta:=beta) bo radix x p ∧
        _root_.F2R q = x - _root_.F2R p⌝⦄
    (pure (ClosestErrorBound_check (beta:=beta) bo radix p q x) : Id Unit)
    ⦃⇓_ => ⌜|_root_.F2R q| ≤
            _root_.F2R (FloatSpec.Core.Defs.FlocqFloat.mk (beta:=beta) 1 p.Fexp) * (1 / 2 : ℝ)⌝⦄ := by
  sorry

-- Inequality lifting for scaling by radix halves (Coq: `FmultRadixInv`)
noncomputable def FmultRadixInv_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (x z : FloatSpec.Core.Defs.FlocqFloat beta) (y : ℝ) : Unit :=
  ()

theorem FmultRadixInv {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (x z : FloatSpec.Core.Defs.FlocqFloat beta) (y : ℝ) :
    ⦃⌜Fbounded (beta:=beta) bo x ∧ Closest (beta:=beta) bo radix y z ∧ (1/2 : ℝ) * _root_.F2R x < y⌝⦄
    (pure (FmultRadixInv_check (beta:=beta) bo radix x z y) : Id Unit)
    ⦃⇓_ => ⌜(1/2 : ℝ) * _root_.F2R x ≤ _root_.F2R z⌝⦄ := by
  sorry

-- Symmetric property of Closest (Coq: `ClosestSymmetric`)
noncomputable def ClosestSymmetric_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ) : Unit :=
  ()

/-- Auxiliary predicate: symmetry for rounding relations on floats. -/
def SymmetricP {beta : Int}
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop) : Prop :=
  ∀ r (p : FloatSpec.Core.Defs.FlocqFloat beta), P r p → P (-r) (Fopp p)

/-- Coq: `ClosestSymmetric` — the `Closest` relation is symmetric under
    real negation accompanied by float negation. -/
theorem ClosestSymmetric {beta : Int}
    (bo : Fbound_skel) (radix : ℝ) :
    ⦃⌜True⌝⦄
    (pure (ClosestSymmetric_check (beta:=beta) bo radix) : Id Unit)
    ⦃⇓_ => ⌜SymmetricP (Closest (beta:=beta) bo radix)⌝⦄ := by
  sorry

-- Coq: `ClosestZero1` — if `Closest r f`, `F2R f = 0`, `r = F2R g`, and
-- `-dExp bo ≤ Fexp g`, then `r = 0`.
noncomputable def ClosestZero1_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (r : ℝ)
    (f g : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `ClosestZero1` — under the stated conditions, the rounded value `r`
    must be zero. We mirror the statement using the project Hoare-triple style
    and leave the proof as a placeholder. -/
theorem ClosestZero1 {beta : Int}
    (bo : Fbound_skel) (radix : ℝ)
    (r : ℝ)
    (f g : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Closest (beta:=beta) bo radix r f ∧
        _root_.F2R f = 0 ∧
        r = _root_.F2R g ∧
        (-bo.dExp : Int) ≤ g.Fexp⌝⦄
    (pure (ClosestZero1_check (beta:=beta) bo radix r f g) : Id Unit)
    ⦃⇓_ => ⌜r = 0⌝⦄ := by
  sorry

/-!
Div-by-2 midpoint characterizations (ported from Coq Pff.v)

We introduce the Hoare-style statements for `div2IsBetweenPos` and
`div2IsBetween`. Proofs are deferred (`sorry`) per the import process.
-/

-- Coq: `div2IsBetweenPos` — if 0 ≤ p and min/max are the rounded bounds of p/2,
-- then F2R p = F2R min + F2R max
noncomputable def div2IsBetweenPos_check {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (p min max : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem div2IsBetweenPos {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (p min max : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜0 ≤ _root_.F2R p ∧
        Fbounded (beta:=beta) b p ∧
        isMin (α:=FloatSpec.Core.Defs.FlocqFloat beta) b radix ((1/2 : ℝ) * _root_.F2R p) min ∧
        isMax (α:=FloatSpec.Core.Defs.FlocqFloat beta) b radix ((1/2 : ℝ) * _root_.F2R p) max⌝⦄
    (pure (div2IsBetweenPos_check (beta:=beta) b radix p min max) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R p = _root_.F2R min + _root_.F2R max⌝⦄ := by
  sorry

-- Coq: `div2IsBetween` — same as above without the nonnegativity side-condition
noncomputable def div2IsBetween_check {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (p min max : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem div2IsBetween {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (p min max : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b p ∧
        isMin (α:=FloatSpec.Core.Defs.FlocqFloat beta) b radix ((1/2 : ℝ) * _root_.F2R p) min ∧
        isMax (α:=FloatSpec.Core.Defs.FlocqFloat beta) b radix ((1/2 : ℝ) * _root_.F2R p) max⌝⦄
    (pure (div2IsBetween_check (beta:=beta) b radix p min max) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R p = _root_.F2R min + _root_.F2R max⌝⦄ := by
  sorry

-- Compatibility of `EvenClosest` (Coq: `EvenClosestCompatible`)
noncomputable def EvenClosestCompatible_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat) : Unit :=
  ()

/-- Coq: `EvenClosestCompatible` — `EvenClosest` respects equality compat. -/
theorem EvenClosestCompatible {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat) :
    ⦃⌜True⌝⦄
    (pure (EvenClosestCompatible_check (beta:=beta) b radix precision) : Id Unit)
    ⦃⇓_ => ⌜CompatibleP (EvenClosest (beta:=beta) b radix precision)⌝⦄ := by
  sorry

-- Min-or-max disjunction for `EvenClosest` (Coq: `EvenClosestMinOrMax`)
noncomputable def EvenClosestMinOrMax_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat) : Unit :=
  ()

theorem EvenClosestMinOrMax {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat) :
    ⦃⌜True⌝⦄
    (pure (EvenClosestMinOrMax_check (beta:=beta) b radix precision) : Id Unit)
    ⦃⇓_ => ⌜MinOrMaxP (EvenClosest (beta:=beta) b radix precision)⌝⦄ := by
  sorry

-- Monotonicity for `EvenClosest` (Coq: `EvenClosestMonotone`)
noncomputable def EvenClosestMonotone_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat) : Unit :=
  ()

theorem EvenClosestMonotone {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat) :
    ⦃⌜True⌝⦄
    (pure (EvenClosestMonotone_check (beta:=beta) b radix precision) : Id Unit)
    ⦃⇓_ => ⌜MonotoneP (EvenClosest (beta:=beta) b radix precision)⌝⦄ := by
  sorry

noncomputable def EvenClosestMonotone2_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (p q : ℝ)
    (p' q' : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem EvenClosestMonotone2 {beta : Int}
    (b : Fbound_skel) (radixZ : Int) (radixR : ℝ) (precision : Nat)
    (p q : ℝ)
    (p' q' : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜p ≤ q ∧
        EvenClosest (beta:=beta) b radixR precision p p' ∧
        EvenClosest (beta:=beta) b radixR precision q q'⌝⦄
    (pure (EvenClosestMonotone2_check (beta:=beta) b radixR precision p q p' q') : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (beta:=beta) p' ≤ _root_.F2R (beta:=beta) q'⌝⦄ := by
  sorry

-- Symmetric property of EvenClosest (Coq: `EvenClosestSymmetric`)
noncomputable def EvenClosestSymmetric_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat) : Unit :=
  ()

/-- Coq: `EvenClosestSymmetric` — the `EvenClosest` relation is symmetric under
    real negation accompanied by float negation. -/
theorem EvenClosestSymmetric {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat) :
    ⦃⌜True⌝⦄
    (pure (EvenClosestSymmetric_check (beta:=beta) b radix precision) : Id Unit)
    ⦃⇓_ => ⌜SymmetricP (EvenClosest (beta:=beta) b radix precision)⌝⦄ := by
  sorry

-- Rounded-mode packaging for `EvenClosest` (Coq: `EvenClosestRoundedModeP`)
noncomputable def EvenClosestRoundedModeP_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat) : Unit :=
  ()

theorem EvenClosestRoundedModeP {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat) :
    ⦃⌜True⌝⦄
    (pure (EvenClosestRoundedModeP_check (beta:=beta) b radix precision) : Id Unit)
    ⦃⇓_ => ⌜RoundedModeP (EvenClosest (beta:=beta) b radix precision)⌝⦄ := by
  sorry

-- Uniqueness for `EvenClosest` (Coq: `EvenClosestUniqueP`)
noncomputable def EvenClosestUniqueP_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat) : Unit :=
  ()

theorem EvenClosestUniqueP {beta : Int}
    (b : Fbound_skel) (radix : ℝ) (precision : Nat) :
    ⦃⌜True⌝⦄
    (pure (EvenClosestUniqueP_check (beta:=beta) b radix precision) : Id Unit)
    ⦃⇓_ => ⌜UniqueP (EvenClosest (beta:=beta) b radix precision)⌝⦄ := by
  sorry

-- ---------------------------------------------------------------------------
-- Underflow/Exponent growth lemmas (ported skeletons)

-- Coq: `FexpGeUnderf` — from boundedness and a magnitude lower bound on |F2R f|
-- derive a lower bound on the exponent Fexp f. We keep the statement in terms of
-- integers and real powers, mirroring the Coq intent. Proof deferred.
noncomputable def FexpGeUnderf_check {beta : Int}
    (bo : Fbound_skel) (precision e : Int)
    (f : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem FexpGeUnderf {beta : Int}
    (bo : Fbound_skel) (precision e : Int)
    (f : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) bo f ∧ (beta : ℝ) ^ e ≤ |_root_.F2R f|⌝⦄
    (pure (FexpGeUnderf_check (beta:=beta) bo precision e f) : Id Unit)
    ⦃⇓_ => ⌜e - precision + 1 ≤ f.Fexp⌝⦄ := by
  sorry

-- Coq: `AddExpGeUnderf` — if `g` is a closest rounding of `f1+f2` and both `f1`
-- and `f2` are sufficiently large in magnitude, then `g` is either zero or has
-- magnitude at least `β^(e-precision+1)`.
noncomputable def AddExpGeUnderf_check {beta : Int}
    (bo : Fbound_skel) (precision e : Int) (radix : ℝ)
    (f1 f2 g : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem AddExpGeUnderf {beta : Int}
    (bo : Fbound_skel) (precision e : Int) (radix : ℝ)
    (f1 f2 g : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Closest (beta:=beta) bo radix (_root_.F2R f1 + _root_.F2R f2) g ∧
        Fbounded (beta:=beta) bo f1 ∧ Fbounded (beta:=beta) bo f2 ∧
        (beta : ℝ) ^ e ≤ |_root_.F2R f1| ∧ (beta : ℝ) ^ e ≤ |_root_.F2R f2|⌝⦄
    (pure (AddExpGeUnderf_check (beta:=beta) bo precision e radix f1 f2 g) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R g = 0 ∨ (beta : ℝ) ^ (e - precision + 1) ≤ |_root_.F2R g|⌝⦄ := by
  sorry

-- First projection: RoundedModeP -> CompatibleP
noncomputable def RoundedModeP_inv2_check {α : Type}
    (P : ℝ → α → Prop) : Unit :=
  ()

theorem RoundedModeP_inv2 {α : Type} (P : ℝ → α → Prop) :
    ⦃⌜RoundedModeP P⌝⦄
    (pure (RoundedModeP_inv2_check P) : Id Unit)
    ⦃⇓_ => ⌜CompatibleP P⌝⦄ := by
  sorry

-- Fourth projection: RoundedModeP -> MonotoneP
noncomputable def RoundedModeP_inv4_check {α : Type}
    (P : ℝ → α → Prop) : Unit :=
  ()

theorem RoundedModeP_inv4 {α : Type} (P : ℝ → α → Prop) :
    ⦃⌜RoundedModeP P⌝⦄
    (pure (RoundedModeP_inv4_check P) : Id Unit)
    ⦃⇓_ => ⌜MonotoneP P⌝⦄ := by
  sorry

-- Projection to a projector property (placeholder)
noncomputable def RoundedProjector_check {α : Type}
    (P : ℝ → α → Prop) : Unit :=
  ()

theorem RoundedProjector {α : Type} (P : ℝ → α → Prop) :
    ⦃⌜RoundedModeP P⌝⦄
    (pure (RoundedProjector_check P) : Id Unit)
    ⦃⇓_ => ⌜ProjectorP P⌝⦄ := by
  sorry

-- Coq: `RoundedModeProjectorIdem` — under RoundedModeP, P p p for bounded p
noncomputable def RoundedModeProjectorIdem_check {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem RoundedModeProjectorIdem {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜RoundedModeP P ∧ Fbounded (beta:=beta) b p⌝⦄
    (pure (RoundedModeProjectorIdem_check (beta:=beta) b radix P p) : Id Unit)
    ⦃⇓_ => ⌜P (_root_.F2R p) p⌝⦄ := by
  sorry

-- Coq: `RoundedModeBounded` — from P r q under RoundedModeP, q is bounded
noncomputable def RoundedModeBounded_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (r : ℝ) (q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem RoundedModeBounded {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (r : ℝ) (q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜RoundedModeP P ∧ P r q⌝⦄
    (pure (RoundedModeBounded_check (beta:=beta) b radix P r q) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b q⌝⦄ := by
  sorry


-- ---------------------------------------------------------------------------
-- Coq: `PminPos` — existence of bounded complement to the min rounding

noncomputable def PminPos_check {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (p min : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `PminPos` — if `0 ≤ F2R p`, `Fbounded b p` and `isMin b radix ((1/2) * F2R p) min`,
    then there exists a bounded float `c` such that `F2R c = F2R p - F2R min`.
    We keep the statement in Hoare-triple style and defer the proof. -/
theorem PminPos {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (p min : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜0 ≤ _root_.F2R p ∧
        Fbounded (beta:=beta) b p ∧
        isMin (α:=FloatSpec.Core.Defs.FlocqFloat beta) b radix ((1 / 2 : ℝ) * _root_.F2R p) min⌝⦄
    (pure (PminPos_check (beta:=beta) b radix p min) : Id Unit)
    ⦃⇓_ => ⌜∃ c : FloatSpec.Core.Defs.FlocqFloat beta,
            Fbounded (beta:=beta) b c ∧
            _root_.F2R c = _root_.F2R p - _root_.F2R min⌝⦄ := by
  sorry

-- Coq: `RoundedModeProjectorIdemEq` — equality on reals under RoundedModeP
noncomputable def RoundedModeProjectorIdemEq_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem RoundedModeProjectorIdemEq {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜RoundedModeP P ∧ Fbounded (beta:=beta) b p ∧ P (_root_.F2R p) q⌝⦄
    (pure (RoundedModeProjectorIdemEq_check (beta:=beta) b radix P p q) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R p = _root_.F2R q⌝⦄ := by
  sorry

-- Coq: `RoundedModeUlp` — under a rounded mode P and P p q, |p - q| < Fulp q
noncomputable def RoundedModeUlp_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (p : ℝ) (q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem RoundedModeUlp {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (p : ℝ) (q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜RoundedModeP P ∧ P p q⌝⦄
    (pure (RoundedModeUlp_check (beta:=beta) b radix P p q) : Id Unit)
    ⦃⇓_ => ⌜|p - _root_.F2R q| < Fulp (beta:=beta) q⌝⦄ := by
  sorry

-- Coq: `RoundedModeMult` — monotonicity wrt scaling by radix
noncomputable def RoundedModeMult_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (r : ℝ) (q q' : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem RoundedModeMult {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (r : ℝ) (q q' : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜RoundedModeP P ∧ P r q ∧ Fbounded (beta:=beta) b q' ∧ r ≤ radix * _root_.F2R q'⌝⦄
    (pure (RoundedModeMult_check (beta:=beta) b radix P r q q') : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R q ≤ radix * _root_.F2R q'⌝⦄ := by
  sorry

-- Coq: `RoundedModeMultLess` — dual inequality for scaling by radix
noncomputable def RoundedModeMultLess_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (r : ℝ) (q q' : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem RoundedModeMultLess {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (r : ℝ) (q q' : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜RoundedModeP P ∧ P r q ∧ Fbounded (beta:=beta) b q' ∧ radix * _root_.F2R q' ≤ r⌝⦄
    (pure (RoundedModeMultLess_check (beta:=beta) b radix P r q q') : Id Unit)
    ⦃⇓_ => ⌜radix * _root_.F2R q' ≤ _root_.F2R q⌝⦄ := by
  sorry

-- Coq: `FnormalBounded` — normal floats are bounded
noncomputable def FnormalBounded_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FnormalBounded` — if a float is normal with respect to `b` and `radix`,
    then it is bounded by `b`. Placeholder statement aligned with Coq; proof deferred. -/
theorem FnormalBounded {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fnormal (beta:=beta) radix b p⌝⦄
    (pure (FnormalBounded_check (beta:=beta) b radix p) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b p⌝⦄ := by
  sorry

-- Coq: `FnormalNotZero` — normal floats are not the zero float
noncomputable def FnormalNotZero_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FnormalNotZero` — if `p` is normal w.r.t. `b` and `radix`, then `p` is
    not the zero float. We mirror the Coq statement using the Hoare-triple
    specification style adopted across this file and leave the proof as `sorry`. -/
theorem FnormalNotZero {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fnormal (beta:=beta) radix b p⌝⦄
    (pure (FnormalNotZero_check (beta:=beta) b radix p) : Id Unit)
    ⦃⇓_ => ⌜¬ is_Fzero p⌝⦄ := by
  sorry

-- Coq: `FnormalFop` — normality is preserved by float negation
noncomputable def FnormalFop_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FnormalFop` — if a float is normal, then its negation is also normal. -/
theorem FnormalFop {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fnormal (beta:=beta) radix b p⌝⦄
    (pure (FnormalFop_check (beta:=beta) b radix p) : Id Unit)
    ⦃⇓_ => ⌜Fnormal (beta:=beta) radix b (FloatSpec.Calc.Operations.Fopp (beta:=beta) p)⌝⦄ := by
  sorry

-- Coq: `FnormalFabs` — normality is preserved by float absolute value
noncomputable def FnormalFabs_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FnormalFabs` — taking the absolute value of a normal float keeps it normal. -/
theorem FnormalFabs {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fnormal (beta:=beta) radix b p⌝⦄
    (pure (FnormalFabs_check (beta:=beta) b radix p) : Id Unit)
    ⦃⇓_ => ⌜Fnormal (beta:=beta) radix b (Fabs (beta:=beta) p)⌝⦄ := by
  sorry

-- Coq: `FsubnormalFbounded` — subnormal floats are bounded
noncomputable def FsubnormalFbounded_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FsubnormalFbounded` — if a float is subnormal with respect to `b` and
    `radix`, then it is bounded by `b`. Statement mirrors Coq; proof deferred. -/
theorem FsubnormalFbounded {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fsubnormal (beta:=beta) radix b p⌝⦄
    (pure (FsubnormalFbounded_check (beta:=beta) b radix p) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b p⌝⦄ := by
  sorry

-- Coq: `FsubnormalFexp` — exponent of a subnormal float is fixed
noncomputable def FsubnormalFexp_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FsubnormalFexp` — subnormal floats all share the minimal exponent
    `-b.dExp`. Placeholder statement matching the Coq lemma. -/
theorem FsubnormalFexp {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fsubnormal (beta:=beta) radix b p⌝⦄
    (pure (FsubnormalFexp_check (beta:=beta) b radix p) : Id Unit)
    ⦃⇓_ => ⌜p.Fexp = -b.dExp⌝⦄ := by
  sorry

-- Coq: `FsubnormFopp` — subnormality preserved by float negation
noncomputable def FsubnormFopp_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FsubnormFopp` — if `p` is subnormal, then so is `Fopp p`. -/
theorem FsubnormFopp {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fsubnormal (beta:=beta) radix b p⌝⦄
    (pure (FsubnormFopp_check (beta:=beta) b radix p) : Id Unit)
    ⦃⇓_ => ⌜Fsubnormal (beta:=beta) radix b
            (FloatSpec.Calc.Operations.Fopp (beta:=beta) p)⌝⦄ := by
  sorry

-- Coq: `FsubnormFabs` — subnormality preserved by float absolute value
noncomputable def FsubnormFabs_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FsubnormFabs` — if `p` is subnormal, then so is `Fabs p`. -/
theorem FsubnormFabs {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fsubnormal (beta:=beta) radix b p⌝⦄
    (pure (FsubnormFabs_check (beta:=beta) b radix p) : Id Unit)
    ⦃⇓_ => ⌜Fsubnormal (beta:=beta) radix b
            (FloatSpec.Calc.Operations.Fabs (beta:=beta) p)⌝⦄ := by
  sorry

-- Coq: `FsubnormalUnique` — subnormal floats equal as reals coincide syntactically
noncomputable def FsubnormalUnique_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FsubnormalUnique` — if two subnormal floats have identical real
    values, they are equal. Mirrors the Coq statement with Hoare triple syntax. -/
theorem FsubnormalUnique {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fsubnormal (beta:=beta) radix b p ∧
        Fsubnormal (beta:=beta) radix b q ∧
        _root_.F2R (beta:=beta) p = _root_.F2R (beta:=beta) q⌝⦄
    (pure (FsubnormalUnique_check (beta:=beta) b radix p q) : Id Unit)
    ⦃⇓_ => ⌜p = q⌝⦄ := by
  sorry

-- Coq: `FsubnormalLt` — ordering subnormal mantissas mirrors real order
noncomputable def FsubnormalLt_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FsubnormalLt` — if two floats are subnormal and their real values
    satisfy `p < q`, then their mantissas follow the same strict order. -/
theorem FsubnormalLt {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fsubnormal (beta:=beta) radix b p ∧
        Fsubnormal (beta:=beta) radix b q ∧
        _root_.F2R (beta:=beta) p < _root_.F2R (beta:=beta) q⌝⦄
    (pure (FsubnormalLt_check (beta:=beta) b radix p q) : Id Unit)
    ⦃⇓_ => ⌜p.Fnum < q.Fnum⌝⦄ := by
  sorry

-- ---------------------------------------------------------------------------
-- RleRoundedAbs (Coq: Pff.v) — lower bound on |r| from rounding to nearest

noncomputable def RleRoundedAbs_check {beta : Int}
    (bo : Fbound_skel) (radix : ℝ) (p : Int)
    (f : FloatSpec.Core.Defs.FlocqFloat beta) (r : ℝ) : Unit :=
  ()

/-- Coq: `RleRoundedAbs` — if `Closest bo radix r f`, `Fnormal radix bo f` and
    `-(dExp bo) < Fexp f`, then
    `((radix ^ (p - 1) + - (1 / (2 * radix))) * radix ^ (Fexp f) ≤ |r|)`.
    We mirror the structure and leave proof deferred. -/
theorem RleRoundedAbs {beta : Int}
    (bo : Fbound_skel) (radix : ℝ) (p : Int)
    (f : FloatSpec.Core.Defs.FlocqFloat beta) (r : ℝ) :
    ⦃⌜Closest (beta:=beta) bo radix r f ∧ Fnormal (beta:=beta) radix bo f ∧ (-bo.dExp < f.Fexp)⌝⦄
    (pure (RleRoundedAbs_check (beta:=beta) bo radix p f r) : Id Unit)
    ⦃⇓_ => ⌜((radix ^ (p - 1) + - (1 / (2 * radix))) * (radix ^ (f.Fexp)) ≤ |r|)⌝⦄ := by
  sorry

-- Coq: `RoundedModeMultAbs` — absolute-value scaling under RoundedModeP

noncomputable def RoundedModeMultAbs_check {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (r : ℝ) (q q' : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `RoundedModeMultAbs` — under a rounded mode `P`, if `P r q`, `q'` is
    bounded by `b`, and `|r| ≤ radix * F2R q'`, then `|F2R q| ≤ radix * F2R q'`.
    Proof deferred. -/
theorem RoundedModeMultAbs {beta : Int}
    (b : Fbound_skel) (radix : ℝ)
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (r : ℝ) (q q' : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜RoundedModeP P ∧ P r q ∧ Fbounded (beta:=beta) b q' ∧ |r| ≤ radix * _root_.F2R q'⌝⦄
    (pure (RoundedModeMultAbs_check (beta:=beta) b radix P r q q') : Id Unit)
    ⦃⇓_ => ⌜|_root_.F2R q| ≤ radix * _root_.F2R q'⌝⦄ := by
  sorry

-- Coq: `MinCompatible` — CompatibleP (isMin b radix)
noncomputable def MinCompatible_check {α : Type}
    (b : Fbound_skel) (radix : Int) : Unit :=
  ()

theorem MinCompatible {α : Type} (b : Fbound_skel) (radix : Int) :
    ⦃⌜True⌝⦄
    (pure (MinCompatible_check (α:=α) b radix) : Id Unit)
    ⦃⇓_ => ⌜CompatibleP (isMin (α:=α) b radix)⌝⦄ := by
  sorry

-- Coq: `MinRoundedModeP` — RoundedModeP (isMin b radix)
noncomputable def MinRoundedModeP_check {α : Type}
    (b : Fbound_skel) (radix : Int) : Unit :=
  ()

theorem MinRoundedModeP {α : Type} (b : Fbound_skel) (radix : Int) :
    ⦃⌜True⌝⦄
    (pure (MinRoundedModeP_check (α:=α) b radix) : Id Unit)
    ⦃⇓_ => ⌜RoundedModeP (isMin (α:=α) b radix)⌝⦄ := by
  sorry

-- Coq: `MaxCompatible` — CompatibleP (isMax b radix)
noncomputable def MaxCompatible_check {α : Type}
    (b : Fbound_skel) (radix : Int) : Unit :=
  ()

theorem MaxCompatible {α : Type} (b : Fbound_skel) (radix : Int) :
    ⦃⌜True⌝⦄
    (pure (MaxCompatible_check (α:=α) b radix) : Id Unit)
    ⦃⇓_ => ⌜CompatibleP (isMax (α:=α) b radix)⌝⦄ := by
  sorry

-- Coq: `MaxRoundedModeP` — RoundedModeP (isMax b radix)
noncomputable def MaxRoundedModeP_check {α : Type}
    (b : Fbound_skel) (radix : Int) : Unit :=
  ()

theorem MaxRoundedModeP {α : Type} (b : Fbound_skel) (radix : Int) :
    ⦃⌜True⌝⦄
    (pure (MaxRoundedModeP_check (α:=α) b radix) : Id Unit)
    ⦃⇓_ => ⌜RoundedModeP (isMax (α:=α) b radix)⌝⦄ := by
  sorry

-- Coq: `RleMinR0` — if 0 ≤ r and `isMin b radix r min` then 0 ≤ F2R min
noncomputable def RleMinR0_check {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (r : ℝ) (min : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem RleMinR0 {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (r : ℝ) (min : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜0 ≤ r ∧ isMin (α:=FloatSpec.Core.Defs.FlocqFloat beta) b radix r min⌝⦄
    (pure (RleMinR0_check (beta:=beta) b radix r min) : Id Unit)
    ⦃⇓_ => ⌜0 ≤ _root_.F2R min⌝⦄ := by
  sorry

-- Coq: `RleRoundedR0` — under RoundedModeP P, if P r p and 0 ≤ r then 0 ≤ F2R p
noncomputable def RleRoundedR0_check {beta : Int}
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) (r : ℝ) : Unit :=
  ()

theorem RleRoundedR0 {beta : Int}
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) (r : ℝ) :
    ⦃⌜RoundedModeP P ∧ P r p ∧ 0 ≤ r⌝⦄
    (pure (RleRoundedR0_check (beta:=beta) P p r) : Id Unit)
    ⦃⇓_ => ⌜0 ≤ _root_.F2R p⌝⦄ := by
  sorry

-- Coq: `RleMaxR0` — if r ≤ 0 and `isMax b radix r max` then F2R max ≤ 0
noncomputable def RleMaxR0_check {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (r : ℝ) (max : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem RleMaxR0 {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (r : ℝ) (max : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜r ≤ 0 ∧ isMax (α:=FloatSpec.Core.Defs.FlocqFloat beta) b radix r max⌝⦄
    (pure (RleMaxR0_check (beta:=beta) b radix r max) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R max ≤ 0⌝⦄ := by
  sorry

-- Coq: `RleRoundedLessR0` — under RoundedModeP P, if P r p and r ≤ 0 then F2R p ≤ 0
noncomputable def RleRoundedLessR0_check {beta : Int}
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) (r : ℝ) : Unit :=
  ()

theorem RleRoundedLessR0 {beta : Int}
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) (r : ℝ) :
    ⦃⌜RoundedModeP P ∧ P r p ∧ r ≤ 0⌝⦄
    (pure (RleRoundedLessR0_check (beta:=beta) P p r) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R p ≤ 0⌝⦄ := by
  sorry

-- Coq: `MinUniqueP` — uniqueness for isMin
noncomputable def MinUniqueP_check {α : Type}
    (b : Fbound_skel) (radix : Int) : Unit :=
  ()

theorem MinUniqueP {α : Type} (b : Fbound_skel) (radix : Int) :
    ⦃⌜True⌝⦄
    (pure (MinUniqueP_check (α:=α) b radix) : Id Unit)
    ⦃⇓_ => ⌜UniqueP (isMin (α:=α) b radix)⌝⦄ := by
  sorry

-- Coq: `MaxUniqueP` — uniqueness for isMax
noncomputable def MaxUniqueP_check {α : Type}
    (b : Fbound_skel) (radix : Int) : Unit :=
  ()

theorem MaxUniqueP {α : Type} (b : Fbound_skel) (radix : Int) :
    ⦃⌜True⌝⦄
    (pure (MaxUniqueP_check (α:=α) b radix) : Id Unit)
    ⦃⇓_ => ⌜UniqueP (isMax (α:=α) b radix)⌝⦄ := by
  sorry

-- (Next missing theorems will be added one-by-one after validation.)

-- Coq: `MinOrMaxRep` — representation form for Min/Max predicates
noncomputable def MinOrMaxRep_check {beta : Int}
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop) : Unit :=
  ()

theorem MinOrMaxRep {beta : Int}
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop) :
    ⦃⌜MinOrMaxP P⌝⦄
    (pure (MinOrMaxRep_check (beta:=beta) P) : Id Unit)
    ⦃⇓_ => ⌜∀ r (p q : FloatSpec.Core.Defs.FlocqFloat beta),
            P r q → ∃ m : Int, q = ⟨m, p.Fexp⟩⌝⦄ := by
  sorry

-- ---------------------------------------------------------------------------
-- Max-bound comparison lemmas (around Coq: maxFbounded, maxMax, maxMaxBis)
-- Coq: `MaxFloat` — bounded floats stay below the canonical bound at their exponent
noncomputable def MaxFloat_check {beta : Int}
    (b : Fbound_skel) (p : FloatSpec.Core.Defs.FlocqFloat beta) (z : Int) : Unit :=
  ()

/-- Coq: `MaxFloat` — if a float `p` is bounded by `b` and `p.Fexp ≤ z`, then
`|F2R p|` remains below the canonical representative `⟨1, z⟩`. We approximate
Coq's exact bound `Float (Zpos (vNum b)) (Fexp p)` via the skeleton float
`⟨(1 : Int), z⟩`. Proof deferred per import policy. -/
theorem MaxFloat {beta : Int}
    (b : Fbound_skel) (p : FloatSpec.Core.Defs.FlocqFloat beta) (z : Int) :
    ⦃⌜Fbounded (beta:=beta) b p ∧ p.Fexp ≤ z⌝⦄
    (pure (MaxFloat_check (beta:=beta) b p z) : Id Unit)
    ⦃⇓_ => ⌜|_root_.F2R (beta:=beta) p| <
            _root_.F2R (beta:=beta) ⟨(1 : Int), z⟩⌝⦄ := by
  sorry



-- We port `maxMax` first. In Coq, it states that if `p` is bounded by `b` and
-- `Fexp p ≤ z`, then `Fabs p < Float (Zpos (vNum b)) z`. Our bound skeleton
-- does not carry `vNum`; we state the result against the canonical unit
-- mantissa at exponent `z`, consistent with other places using `⟨1, z⟩`.
noncomputable def maxMax_check {beta : Int}
    (b : Fbound_skel) (p : FloatSpec.Core.Defs.FlocqFloat beta) (z : Int) : Unit :=
  ()

/-- Coq: `maxMax` — if `p` is bounded and `p.Fexp ≤ z`, then
`F2R (Fabs p) < F2R ⟨1, z⟩` (skeleton version).
This mirrors the Coq intent with our simplified bound structure. -/
theorem maxMax {beta : Int}
    (b : Fbound_skel) (p : FloatSpec.Core.Defs.FlocqFloat beta) (z : Int) :
    ⦃⌜Fbounded (beta:=beta) b p ∧ p.Fexp ≤ z⌝⦄
    (pure (maxMax_check (beta:=beta) b p z) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (beta:=beta) (Fabs (beta:=beta) p) <
            _root_.F2R (beta:=beta) ⟨(1 : Int), z⟩⌝⦄ := by
  sorry

/-- Helper computation for `maxMax1`. Mirrors the Hoare-style pipeline used in
`maxMax` but records the weaker (non-strict) inequality variant from Coq. -/
noncomputable def maxMax1_check {beta : Int}
    (b : Fbound_skel) (p : FloatSpec.Core.Defs.FlocqFloat beta) (z : Int) : Unit :=
  ()

/-- Coq: `maxMax1` — bounded floats whose exponent is at most `z` stay below the
canonical representative at exponent `z`. We phrase the Lean version using the
same simplified bound skeleton as `maxMax`, replacing Coq's `Float (pPred (vNum b)) z`
with the canonical unit mantissa `⟨1, z⟩`. Proof deferred per import policy. -/
theorem maxMax1 {beta : Int}
    (b : Fbound_skel) (p : FloatSpec.Core.Defs.FlocqFloat beta) (z : Int) :
    ⦃⌜Fbounded (beta:=beta) b p ∧ p.Fexp ≤ z⌝⦄
    (pure (maxMax1_check (beta:=beta) b p z) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (beta:=beta) (Fabs (beta:=beta) p) ≤
            _root_.F2R (beta:=beta) ⟨(1 : Int), z⟩⌝⦄ := by
  sorry

/-- Coq: `maxMaxBis` — bounded floats with exponent strictly below `z` stay
below the canonical representative `⟨1, z⟩`. Mirrors the Coq semantics using
the simplified bound skeleton employed throughout this section. -/
theorem maxMaxBis {beta : Int}
    (b : Fbound_skel) (p : FloatSpec.Core.Defs.FlocqFloat beta) (z : Int) :
    ⦃⌜Fbounded (beta:=beta) b p ∧ p.Fexp < z⌝⦄
    (pure (maxMax1_check (beta:=beta) b p z) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (beta:=beta) (Fabs (beta:=beta) p) <
            _root_.F2R (beta:=beta) ⟨(1 : Int), z⟩⌝⦄ := by
  sorry

-- ---------------------------------------------------------------------------
-- Exponent comparison helper lemmas (around Coq: eqExpLess, FboundedShiftLess...)

-- Coq: `eqExpLess` — if `p` is bounded and `F2R p = F2R q`,
-- then there exists a bounded `r` with the same real value as `q`
-- and exponent at least that of `q`.
noncomputable def eqExpLess_check {beta : Int}
    (b : Fbound_skel) (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem eqExpLess {beta : Int}
    (b : Fbound_skel) (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b p ∧ _root_.F2R p = _root_.F2R q⌝⦄
    (pure (eqExpLess_check (beta:=beta) b p q) : Id Unit)
    ⦃⇓_ => ⌜∃ r : FloatSpec.Core.Defs.FlocqFloat beta,
              Fbounded (beta:=beta) b r ∧
              _root_.F2R r = _root_.F2R q ∧
              q.Fexp ≤ r.Fexp⌝⦄ := by
  sorry

-- Shift operation on floats (placeholder, no-op). We place it early so that
-- subsequent lemmas can reference it.
noncomputable def Fshift {beta : Int}
    (radix : Int) (n : Nat) (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    FloatSpec.Core.Defs.FlocqFloat beta := x

-- Coq: `FboundedShiftLess` — if `m ≤ n` and `Fshift radix n f` is bounded,
-- then `Fshift radix m f` is also bounded.
noncomputable def FboundedShiftLess_check {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (f : FloatSpec.Core.Defs.FlocqFloat beta) (n m : Nat) : Unit :=
  ()

theorem FboundedShiftLess {beta : Int}
    (b : Fbound_skel) (radix : Int)
    (f : FloatSpec.Core.Defs.FlocqFloat beta) (n m : Nat) :
    ⦃⌜m ≤ n ∧ Fbounded (beta:=beta) b (Fshift (beta:=beta) radix n f)⌝⦄
    (pure (FboundedShiftLess_check (beta:=beta) b radix f n m) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b (Fshift (beta:=beta) radix m f)⌝⦄ := by
  sorry

-- Coq: `eqExpMax` — if `p` and `q` are bounded and |F2R p| ≤ F2R q,
-- then there exists a bounded `r` with F2R r = F2R p and Fexp r ≤ Fexp q.
noncomputable def eqExpMax_check {beta : Int}
    (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem eqExpMax {beta : Int}
    (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b p ∧ Fbounded (beta:=beta) b q ∧
        |_root_.F2R p| ≤ _root_.F2R q⌝⦄
    (pure (eqExpMax_check (beta:=beta) b p q) : Id Unit)
    ⦃⇓_ => ⌜∃ r : FloatSpec.Core.Defs.FlocqFloat beta,
              Fbounded (beta:=beta) b r ∧
              _root_.F2R r = _root_.F2R p ∧
              r.Fexp ≤ q.Fexp⌝⦄ := by
  sorry

-- Coq: `RoundedModeRep` — representation form for rounded modes
noncomputable def RoundedModeRep_check {beta : Int}
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop) : Unit :=
  ()

theorem RoundedModeRep {beta : Int}
    (P : ℝ → FloatSpec.Core.Defs.FlocqFloat beta → Prop) :
    ⦃⌜RoundedModeP P⌝⦄
    (pure (RoundedModeRep_check (beta:=beta) P) : Id Unit)
    ⦃⇓_ => ⌜∀ r (p q : FloatSpec.Core.Defs.FlocqFloat beta),
            P r q → ∃ m : Int, q = ⟨m, p.Fexp⟩⌝⦄ := by
  sorry

-- Coq: `pow_NR0` — if e ≠ 0 then e^n ≠ 0
noncomputable def pow_NR0_check (e : ℝ) (n : Nat) : Unit :=
  ()

theorem pow_NR0 (e : ℝ) (n : Nat) :
    ⦃⌜e ≠ 0⌝⦄
    (pure (pow_NR0_check e n) : Id Unit)
    ⦃⇓_ => ⌜e ^ n ≠ 0⌝⦄ := by
  sorry

-- Coq: `pow_add` — e^(n+m) = e^n * e^m
noncomputable def pow_add_compat_check (e : ℝ) (n m : Nat) : Unit :=
  ()

-- Renamed to avoid clashing with Mathlib's `pow_add`
theorem pow_add_compat (e : ℝ) (n m : Nat) :
    ⦃⌜True⌝⦄
    (pure (pow_add_compat_check e n m) : Id Unit)
    ⦃⇓_ => ⌜e ^ (n + m) = e ^ n * e ^ m⌝⦄ := by
  sorry

-- Coq: `pow_RN_plus` — e ≠ 0 → e^n = e^(n+m) * (e^m)⁻¹
noncomputable def pow_RN_plus_check (e : ℝ) (n m : Nat) : Unit :=
  ()

theorem pow_RN_plus (e : ℝ) (n m : Nat) :
    ⦃⌜e ≠ 0⌝⦄
    (pure (pow_RN_plus_check e n m) : Id Unit)
    ⦃⇓_ => ⌜e ^ n = e ^ (n + m) * (e ^ m)⁻¹⌝⦄ := by
  sorry

-- Coq: `pow_lt` — 0 < e → 0 < e^n
noncomputable def pow_lt_check (e : ℝ) (n : Nat) : Unit :=
  ()

theorem pow_lt (e : ℝ) (n : Nat) :
    ⦃⌜0 < e⌝⦄
    (pure (pow_lt_check e n) : Id Unit)
    ⦃⇓_ => ⌜0 < e ^ n⌝⦄ := by
  sorry

-- Coq: `Rlt_pow_R1` — 1 < e → 0 < n → 1 < e^n
noncomputable def Rlt_pow_R1_check (e : ℝ) (n : Nat) : Unit :=
  ()

theorem Rlt_pow_R1 (e : ℝ) (n : Nat) :
    ⦃⌜1 < e ∧ 0 < n⌝⦄
    (pure (Rlt_pow_R1_check e n) : Id Unit)
    ⦃⇓_ => ⌜1 < e ^ n⌝⦄ := by
  sorry

-- Coq: `Rlt_pow` — 1 < e → n < m → e^n < e^m
noncomputable def Rlt_pow_check (e : ℝ) (n m : Nat) : Unit :=
  ()

theorem Rlt_pow (e : ℝ) (n m : Nat) :
    ⦃⌜1 < e ∧ n < m⌝⦄
    (pure (Rlt_pow_check e n m) : Id Unit)
    ⦃⇓_ => ⌜e ^ n < e ^ m⌝⦄ := by
  sorry

-- Coq: `pow_R1` — r^n = 1 → |r| = 1 ∨ n = 0
noncomputable def pow_R1_check (r : ℝ) (n : Nat) : Unit :=
  ()

theorem pow_R1 (r : ℝ) (n : Nat) :
    ⦃⌜r ^ n = 1⌝⦄
    (pure (pow_R1_check r n) : Id Unit)
    ⦃⇓_ => ⌜|r| = 1 ∨ n = 0⌝⦄ := by
  sorry

-- Coq: `Rle_Fexp_eq_Zle` — if x ≤ y and Fexp x = Fexp y then Fnum x ≤ Fnum y
noncomputable def Rle_Fexp_eq_Zle_check {beta : Int}
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem Rle_Fexp_eq_Zle {beta : Int}
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜_root_.F2R x ≤ _root_.F2R y ∧ x.Fexp = y.Fexp⌝⦄
    (pure (Rle_Fexp_eq_Zle_check (beta:=beta) x y) : Id Unit)
    ⦃⇓_ => ⌜x.Fnum ≤ y.Fnum⌝⦄ := by
  sorry

-- Coq: `powerRZ_O` — e^0 = 1 (integer exponent)
noncomputable def powerRZ_O_check (e : ℝ) : Unit :=
  ()

theorem powerRZ_O (e : ℝ) :
    ⦃⌜True⌝⦄
    (pure (powerRZ_O_check e) : Id Unit)
    ⦃⇓_ => ⌜e ^ (0 : Int) = (1 : ℝ)⌝⦄ := by
  sorry

-- Coq: `Zpower_NR0` — 0 ≤ e → 0 ≤ e^n (as integer power on Int)
noncomputable def Zpower_NR0_check (e : Int) (n : Nat) : Unit :=
  ()

theorem Zpower_NR0 (e : Int) (n : Nat) :
    ⦃⌜0 ≤ e⌝⦄
    (pure (Zpower_NR0_check e n) : Id Unit)
    ⦃⇓_ => ⌜0 ≤ (e : Int) ^ n⌝⦄ := by
  sorry

-- Coq: `Zpower_NR1` — 1 ≤ e → 1 ≤ e^n (as integer power on Int)
noncomputable def Zpower_NR1_check (e : Int) (n : Nat) : Unit :=
  ()

theorem Zpower_NR1 (e : Int) (n : Nat) :
    ⦃⌜1 ≤ e⌝⦄
    (pure (Zpower_NR1_check e n) : Id Unit)
    ⦃⇓_ => ⌜1 ≤ (e : Int) ^ n⌝⦄ := by
  sorry

-- Coq: `powerRZ_1` — e^1 = e (integer exponent)
noncomputable def powerRZ_1_check (e : ℝ) : Unit :=
  ()

theorem powerRZ_1 (e : ℝ) :
    ⦃⌜True⌝⦄
    (pure (powerRZ_1_check e) : Id Unit)
    ⦃⇓_ => ⌜e ^ (1 : Int) = e⌝⦄ := by
  sorry

-- Coq: `powerRZ_R1` — 1^n = 1 (integer exponent)
noncomputable def powerRZ_R1_check (n : Int) : Unit :=
  ()

theorem powerRZ_R1 (n : Int) :
    ⦃⌜True⌝⦄
    (pure (powerRZ_R1_check n) : Id Unit)
    ⦃⇓_ => ⌜(1 : ℝ) ^ n = (1 : ℝ)⌝⦄ := by
  sorry

-- Coq: `powerRZ_add` — e^(m+n) = e^m * e^n (integer exponent)
noncomputable def powerRZ_add_check (e : ℝ) (m n : Int) : Unit :=
  ()

theorem powerRZ_add (e : ℝ) (m n : Int) :
    ⦃⌜True⌝⦄
    (pure (powerRZ_add_check e m n) : Id Unit)
    ⦃⇓_ => ⌜e ^ (m + n) = e ^ m * e ^ n⌝⦄ := by
  sorry

-- Coq: `powerRZ_Zopp` — e^(-z) = (e^z)⁻¹ for nonzero base
noncomputable def powerRZ_Zopp_check (e : ℝ) (z : Int) : Unit :=
  ()

theorem powerRZ_Zopp (e : ℝ) (z : Int) :
    ⦃⌜e ≠ 0⌝⦄
    (pure (powerRZ_Zopp_check e z) : Id Unit)
    ⦃⇓_ => ⌜e ^ (-z) = (e ^ z)⁻¹⌝⦄ := by
  sorry

-- Coq: `powerRZ_Zs` — e^(Z.succ n) = e * e^n for nonzero base
noncomputable def powerRZ_Zs_check (e : ℝ) (n : Int) : Unit :=
  ()

theorem powerRZ_Zs (e : ℝ) (n : Int) :
    ⦃⌜e ≠ 0⌝⦄
    (pure (powerRZ_Zs_check e n) : Id Unit)
    ⦃⇓_ => ⌜e ^ (Int.succ n) = e * e ^ n⌝⦄ := by
  sorry

-- Coq: `Zpower_nat_Z_powerRZ` — bridge between integer and real powers
-- Alias for Coq's Zpower_nat on integers (placed early for downstream uses)
noncomputable def Zpower_nat (n : Int) (q : Nat) : Int := n ^ q

noncomputable def Zpower_nat_Z_powerRZ_check (n : Int) (m : Nat) : Unit :=
  ()

theorem Zpower_nat_Z_powerRZ (n : Int) (m : Nat) :
    ⦃⌜True⌝⦄
    (pure (Zpower_nat_Z_powerRZ_check n m) : Id Unit)
    ⦃⇓_ => ⌜(Zpower_nat n m : ℝ) = ( (n : ℝ) ^ (m : Int) )⌝⦄ := by
  sorry

-- Coq: `powerRZ_lt` — if 0 < e then 0 < e^z (integer exponent)
noncomputable def powerRZ_lt_check (e : ℝ) (z : Int) : Unit :=
  ()

theorem powerRZ_lt (e : ℝ) (z : Int) :
    ⦃⌜0 < e⌝⦄
    (pure (powerRZ_lt_check e z) : Id Unit)
    ⦃⇓_ => ⌜0 < e ^ z⌝⦄ := by
  sorry

-- Coq: `powerRZ_le` — 0 < e → 0 ≤ e^z (integer exponent)
noncomputable def powerRZ_le_check (e : ℝ) (z : Int) : Unit :=
  ()

theorem powerRZ_le (e : ℝ) (z : Int) :
    ⦃⌜0 < e⌝⦄
    (pure (powerRZ_le_check e z) : Id Unit)
    ⦃⇓_ => ⌜0 ≤ e ^ z⌝⦄ := by
  sorry

-- Coq: `Rlt_powerRZ` — 1 < e → n < m → e^n < e^m
noncomputable def Rlt_powerRZ_check (e : ℝ) (n m : Int) : Unit :=
  ()

theorem Rlt_powerRZ (e : ℝ) (n m : Int) :
    ⦃⌜1 < e ∧ n < m⌝⦄
    (pure (Rlt_powerRZ_check e n m) : Id Unit)
    ⦃⇓_ => ⌜e ^ n < e ^ m⌝⦄ := by
  sorry

-- Coq: `Zpower_nat_powerRZ_absolu` — IZR (Zpower_nat n (Z.abs_nat m)) = powerRZ (IZR n) m for m ≥ 0
noncomputable def Zpower_nat_powerRZ_absolu_check (n m : Int) : Unit :=
  ()

theorem Zpower_nat_powerRZ_absolu (n m : Int) :
    ⦃⌜0 ≤ m⌝⦄
    (pure (Zpower_nat_powerRZ_absolu_check n m) : Id Unit)
    ⦃⇓_ => ⌜(Zpower_nat n (Int.toNat (Int.natAbs m)) : ℝ) = (n : ℝ) ^ m⌝⦄ := by
  sorry

-- Coq: `Rle_powerRZ` — 1 ≤ e → n ≤ m → e^n ≤ e^m
noncomputable def Rle_powerRZ_check (e : ℝ) (n m : Int) : Unit :=
  ()

theorem Rle_powerRZ (e : ℝ) (n m : Int) :
    ⦃⌜1 ≤ e ∧ n ≤ m⌝⦄
    (pure (Rle_powerRZ_check e n m) : Id Unit)
    ⦃⇓_ => ⌜e ^ n ≤ e ^ m⌝⦄ := by
  sorry

-- Coq: `Zlt_powerRZ` — 1 ≤ e → e^n < e^m → n < m
noncomputable def Zlt_powerRZ_check (e : ℝ) (n m : Int) : Unit :=
  ()

theorem Zlt_powerRZ (e : ℝ) (n m : Int) :
    ⦃⌜1 ≤ e ∧ e ^ n < e ^ m⌝⦄
    (pure (Zlt_powerRZ_check e n m) : Id Unit)
    ⦃⇓_ => ⌜n < m⌝⦄ := by
  sorry

-- Coq: `Rlt_monotony_exp` — multiply preserves < with positive factor (power)
noncomputable def Rlt_monotony_exp_check (radix : ℝ) (x y : ℝ) (z : Int) : Unit :=
  ()

theorem Rlt_monotony_exp (radix : ℝ) (x y : ℝ) (z : Int) :
    ⦃⌜x < y⌝⦄
    (pure (Rlt_monotony_exp_check radix x y z) : Id Unit)
    ⦃⇓_ => ⌜x * radix ^ z < y * radix ^ z⌝⦄ := by
  sorry

-- Coq: `Rle_monotone_exp` — multiply preserves ≤ with positive factor (power)
noncomputable def Rle_monotone_exp_check (radix : ℝ) (x y : ℝ) (z : Int) : Unit :=
  ()

theorem Rle_monotone_exp (radix : ℝ) (x y : ℝ) (z : Int) :
    ⦃⌜x ≤ y⌝⦄
    (pure (Rle_monotone_exp_check radix x y z) : Id Unit)
    ⦃⇓_ => ⌜x * radix ^ z ≤ y * radix ^ z⌝⦄ := by
  sorry

-- Coq: `Rlt_monotony_contra_exp` — cancel positive power factor from <
noncomputable def Rlt_monotony_contra_exp_check (radix : ℝ) (x y : ℝ) (z : Int) : Unit :=
  ()

theorem Rlt_monotony_contra_exp (radix : ℝ) (x y : ℝ) (z : Int) :
    ⦃⌜x * radix ^ z < y * radix ^ z⌝⦄
    (pure (Rlt_monotony_contra_exp_check radix x y z) : Id Unit)
    ⦃⇓_ => ⌜x < y⌝⦄ := by
  sorry

-- Coq: `Rle_monotony_contra_exp` — cancel positive power factor from ≤
noncomputable def Rle_monotony_contra_exp_check (radix : ℝ) (x y : ℝ) (z : Int) : Unit :=
  ()

theorem Rle_monotony_contra_exp (radix : ℝ) (x y : ℝ) (z : Int) :
    ⦃⌜x * radix ^ z ≤ y * radix ^ z⌝⦄
    (pure (Rle_monotony_contra_exp_check radix x y z) : Id Unit)
    ⦃⇓_ => ⌜x ≤ y⌝⦄ := by
  sorry

-- Coq: `FtoREqInv2` — equality by equal real value and same exponent
noncomputable def FtoREqInv2_check {beta : Int}
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem FtoREqInv2 {beta : Int}
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜_root_.F2R p = _root_.F2R q ∧ p.Fexp = q.Fexp⌝⦄
    (pure (FtoREqInv2_check (beta:=beta) p q) : Id Unit)
    ⦃⇓_ => ⌜p = q⌝⦄ := by
  sorry

-- Coq: `sameExpEq` — if two floats have equal real value and same exponent, they are equal
noncomputable def sameExpEq_check {beta : Int}
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem sameExpEq {beta : Int}
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜_root_.F2R p = _root_.F2R q ∧ p.Fexp = q.Fexp⌝⦄
    (pure (sameExpEq_check (beta:=beta) p q) : Id Unit)
    ⦃⇓_ => ⌜p = q⌝⦄ := by
  -- Mirrors Coq `sameExpEq`; see also `FtoREqInv2`.
  sorry

-- Coq: `Rlt_Float_Zlt` — compare mantissas when exponents equal
noncomputable def Rlt_Float_Zlt_check {beta : Int} (p q r : Int) : Unit :=
  ()

theorem Rlt_Float_Zlt {beta : Int} (p q r : Int) :
    ⦃⌜_root_.F2R (⟨p, r⟩ : FloatSpec.Core.Defs.FlocqFloat beta) <
         _root_.F2R (⟨q, r⟩ : FloatSpec.Core.Defs.FlocqFloat beta)⌝⦄
    (pure (Rlt_Float_Zlt_check (beta:=beta) p q r) : Id Unit)
    ⦃⇓_ => ⌜p < q⌝⦄ := by
  sorry

-- Coq: `oneExp_le` — with mantissa 1, exponent order preserves real ≤
noncomputable def oneExp_le_check {beta : Int} (x y : Int) : Unit :=
  ()

theorem oneExp_le {beta : Int} (x y : Int) :
    ⦃⌜x ≤ y⌝⦄
    (pure (oneExp_le_check (beta:=beta) x y) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (⟨1, x⟩ : FloatSpec.Core.Defs.FlocqFloat beta)
            ≤ _root_.F2R (⟨1, y⟩ : FloatSpec.Core.Defs.FlocqFloat beta)⌝⦄ := by
  sorry

-- Coq: `oneExp_Zlt` — with mantissa 1, real < implies exponent <
noncomputable def oneExp_Zlt_check {beta : Int} (x y : Int) : Unit :=
  ()

theorem oneExp_Zlt {beta : Int} (x y : Int) :
    ⦃⌜_root_.F2R (⟨1, x⟩ : FloatSpec.Core.Defs.FlocqFloat beta) <
         _root_.F2R (⟨1, y⟩ : FloatSpec.Core.Defs.FlocqFloat beta)⌝⦄
    (pure (oneExp_Zlt_check (beta:=beta) x y) : Id Unit)
    ⦃⇓_ => ⌜x < y⌝⦄ := by
  sorry

-- Coq: `Zle_powerRZ` — 1 < e → e^n ≤ e^m → n ≤ m
noncomputable def Zle_powerRZ_check (e : ℝ) (n m : Int) : Unit :=
  ()

theorem Zle_powerRZ (e : ℝ) (n m : Int) :
    ⦃⌜1 < e ∧ e ^ n ≤ e ^ m⌝⦄
    (pure (Zle_powerRZ_check e n m) : Id Unit)
    ⦃⇓_ => ⌜n ≤ m⌝⦄ := by
  sorry

-- Coq: `Rinv_powerRZ` — (/ (e^n)) = e^(-n) for nonzero base (integer exponent)
noncomputable def Rinv_powerRZ_check (e : ℝ) (n : Int) : Unit :=
  ()

theorem Rinv_powerRZ (e : ℝ) (n : Int) :
    ⦃⌜e ≠ 0⌝⦄
    (pure (Rinv_powerRZ_check e n) : Id Unit)
    ⦃⇓_ => ⌜(e ^ n)⁻¹ = e ^ (-n)⌝⦄ := by
  sorry

-- Coq: `Rledouble` — if 0 ≤ r then r ≤ 2r
noncomputable def Rledouble_check (r : ℝ) : Unit :=
  ()

theorem Rledouble (r : ℝ) :
    ⦃⌜0 ≤ r⌝⦄
    (pure (Rledouble_check r) : Id Unit)
    ⦃⇓_ => ⌜r ≤ 2 * r⌝⦄ := by
  sorry

-- Coq: `Rltdouble` — if 0 < r then r < 2r
noncomputable def Rltdouble_check (r : ℝ) : Unit :=
  ()

theorem Rltdouble (r : ℝ) :
    ⦃⌜0 < r⌝⦄
    (pure (Rltdouble_check r) : Id Unit)
    ⦃⇓_ => ⌜r < 2 * r⌝⦄ := by
  sorry

-- Coq: `powerRZ_NOR` — e^n ≠ 0 when e ≠ 0 (integer exponent)
noncomputable def powerRZ_NOR_check (e : ℝ) (n : Int) : Unit :=
  ()

theorem powerRZ_NOR (e : ℝ) (n : Int) :
    ⦃⌜e ≠ 0⌝⦄
    (pure (powerRZ_NOR_check e n) : Id Unit)
    ⦃⇓_ => ⌜e ^ n ≠ 0⌝⦄ := by
  sorry

-- Coq: `Rle_Rinv` — monotonicity of inverse on (0, ∞)
noncomputable def Rle_Rinv_check (x y : ℝ) : Unit :=
  ()

theorem Rle_Rinv (x y : ℝ) :
    ⦃⌜0 < x ∧ x ≤ y⌝⦄
    (pure (Rle_Rinv_check x y) : Id Unit)
    ⦃⇓_ => ⌜y⁻¹ ≤ x⁻¹⌝⦄ := by
  sorry

-- Hoare-style wrapper for `min_or`
noncomputable def min_or_check (n m : Nat) : Unit :=
  ()

theorem min_or (n m : Nat) :
    ⦃⌜True⌝⦄
    (pure (min_or_check n m) : Id Unit)
    ⦃⇓_ => ⌜(Nat.min n m = n ∧ n ≤ m) ∨ (Nat.min n m = m ∧ m < n)⌝⦄ := by
  sorry

-- Coq: `ZmaxSym` — symmetry of integer max
noncomputable def ZmaxSym_check (a b : Int) : Unit :=
  ()

theorem ZmaxSym (a b : Int) :
    ⦃⌜True⌝⦄
    (pure (ZmaxSym_check a b) : Id Unit)
    ⦃⇓_ => ⌜max a b = max b a⌝⦄ := by
  sorry

-- Coq: `ZmaxLe1` — left argument ≤ max
noncomputable def ZmaxLe1_check (a b : Int) : Unit :=
  ()

theorem ZmaxLe1 (a b : Int) :
    ⦃⌜True⌝⦄
    (pure (ZmaxLe1_check a b) : Id Unit)
    ⦃⇓_ => ⌜a ≤ max a b⌝⦄ := by
  sorry

-- Coq: `ZmaxLe2` — right argument ≤ max
noncomputable def ZmaxLe2_check (a b : Int) : Unit :=
  ()

theorem ZmaxLe2 (a b : Int) :
    ⦃⌜True⌝⦄
    (pure (ZmaxLe2_check a b) : Id Unit)
    ⦃⇓_ => ⌜b ≤ max a b⌝⦄ := by
  sorry

noncomputable def ZleLe_check (x y : Nat) : Unit :=
  ()

theorem ZleLe (x y : Nat) :
    ⦃⌜(Int.ofNat x ≤ Int.ofNat y)⌝⦄
    (pure (ZleLe_check x y) : Id Unit)
    ⦃⇓_ => ⌜x ≤ y⌝⦄ := by
  sorry

-- Coq: `Zlt_Zopp` — negate flips strict inequality
noncomputable def Zlt_Zopp_check (x y : Int) : Unit :=
  ()

theorem Zlt_Zopp (x y : Int) :
    ⦃⌜x < y⌝⦄
    (pure (Zlt_Zopp_check x y) : Id Unit)
    ⦃⇓_ => ⌜-y < -x⌝⦄ := by
  sorry

-- Coq: `Zle_Zopp` — negate flips non-strict inequality
noncomputable def Zle_Zopp_check (x y : Int) : Unit :=
  ()

theorem Zle_Zopp (x y : Int) :
    ⦃⌜x ≤ y⌝⦄
    (pure (Zle_Zopp_check x y) : Id Unit)
    ⦃⇓_ => ⌜-y ≤ -x⌝⦄ := by
  sorry

-- Coq: `Zabs_absolu` — absolute value equals natAbs cast
noncomputable def Zabs_absolu_check (z : Int) : Unit :=
  ()

theorem Zabs_absolu (z : Int) :
    ⦃⌜True⌝⦄
    (pure (Zabs_absolu_check z) : Id Unit)
    ⦃⇓_ => ⌜|z| = Int.ofNat (Int.natAbs z)⌝⦄ := by
  sorry

-- Coq: `Zpower_nat_O` — any base to 0 is 1
noncomputable def Zpower_nat_O_check (z : Int) : Unit :=
  ()

theorem Zpower_nat_O (z : Int) :
    ⦃⌜True⌝⦄
    (pure (Zpower_nat_O_check z) : Id Unit)
    ⦃⇓_ => ⌜z^0 = (1 : Int)⌝⦄ := by
  sorry

-- Coq: `Zpower_nat_1` — any base to 1 is itself
noncomputable def Zpower_nat_1_check (z : Int) : Unit :=
  ()

theorem Zpower_nat_1 (z : Int) :
    ⦃⌜True⌝⦄
    (pure (Zpower_nat_1_check z) : Id Unit)
    ⦃⇓_ => ⌜z^1 = z⌝⦄ := by
  sorry

-- Coq: `Zmin_Zmax` — min is always ≤ max
noncomputable def Zmin_Zmax_check (z1 z2 : Int) : Unit :=
  ()

theorem Zmin_Zmax (z1 z2 : Int) :
    ⦃⌜True⌝⦄
    (pure (Zmin_Zmax_check z1 z2) : Id Unit)
    ⦃⇓_ => ⌜min z1 z2 ≤ max z1 z2⌝⦄ := by
  sorry

-- Coq: `Zeq_Zs` — if p ≤ q < succ p, then p = q
noncomputable def Zeq_Zs_check (p q : Int) : Unit :=
  ()

theorem Zeq_Zs (p q : Int) :
    ⦃⌜p ≤ q ∧ q < Int.succ p⌝⦄
    (pure (Zeq_Zs_check p q) : Id Unit)
    ⦃⇓_ => ⌜p = q⌝⦄ := by
  sorry

-- Coq: `Zopp_Zpred_Zs` — negation distributes over predecessor/successor
noncomputable def Zopp_Zpred_Zs_check (z : Int) : Unit :=
  ()

theorem Zopp_Zpred_Zs (z : Int) :
    ⦃⌜True⌝⦄
    (pure (Zopp_Zpred_Zs_check z) : Id Unit)
    ⦃⇓_ => ⌜-(Int.pred z) = Int.succ (-z)⌝⦄ := by
  sorry

-- Coq: `Zmin_Zle` — lower bound is ≤ minimum of two bounds
noncomputable def Zmin_Zle_check (z1 z2 z3 : Int) : Unit :=
  ()

theorem Zmin_Zle (z1 z2 z3 : Int) :
    ⦃⌜z1 ≤ z2 ∧ z1 ≤ z3⌝⦄
    (pure (Zmin_Zle_check z1 z2 z3) : Id Unit)
    ⦃⇓_ => ⌜z1 ≤ min z2 z3⌝⦄ := by
  sorry

-- Coq: `Zmin_Zlt` — if z1 < z2 and z1 < z3 then z1 < min z2 z3
noncomputable def Zmin_Zlt_check (z1 z2 z3 : Int) : Unit :=
  ()

theorem Zmin_Zlt (z1 z2 z3 : Int) :
    ⦃⌜z1 < z2 ∧ z1 < z3⌝⦄
    (pure (Zmin_Zlt_check z1 z2 z3) : Id Unit)
    ⦃⇓_ => ⌜z1 < min z2 z3⌝⦄ := by
  sorry

-- Coq: `Zpred_Zopp_Zs` — predecessor of negation equals negation of successor
noncomputable def Zpred_Zopp_Zs_check (z : Int) : Unit :=
  ()

theorem Zpred_Zopp_Zs (z : Int) :
    ⦃⌜True⌝⦄
    (pure (Zpred_Zopp_Zs_check z) : Id Unit)
    ⦃⇓_ => ⌜Int.pred (-z) = -(Int.succ z)⌝⦄ := by
  sorry

-- Coq: `Zle_Zmult_comp_r` — multiply on the right preserves ≤ for nonnegative multiplier
noncomputable def Zle_Zmult_comp_r_check (x y z : Int) : Unit :=
  ()

theorem Zle_Zmult_comp_r (x y z : Int) :
    ⦃⌜0 ≤ z ∧ x ≤ y⌝⦄
    (pure (Zle_Zmult_comp_r_check x y z) : Id Unit)
    ⦃⇓_ => ⌜x * z ≤ y * z⌝⦄ := by
  sorry

-- Coq: `Zle_Zmult_comp_l` — multiply on the left preserves ≤ for nonnegative multiplier
noncomputable def Zle_Zmult_comp_l_check (x y z : Int) : Unit :=
  ()

theorem Zle_Zmult_comp_l (x y z : Int) :
    ⦃⌜0 ≤ z ∧ x ≤ y⌝⦄
    (pure (Zle_Zmult_comp_l_check x y z) : Id Unit)
    ⦃⇓_ => ⌜z * x ≤ z * y⌝⦄ := by
  sorry

-- Coq: `absolu_Zs` — natAbs of succ increments under nonnegativity
noncomputable def absolu_Zs_check (z : Int) : Unit :=
  ()

theorem absolu_Zs (z : Int) :
    ⦃⌜0 ≤ z⌝⦄
    (pure (absolu_Zs_check z) : Id Unit)
    ⦃⇓_ => ⌜Int.natAbs (Int.succ z) = Nat.succ (Int.natAbs z)⌝⦄ := by
  sorry

-- Coq: `Zlt_next` — either m = succ n or succ n < m when n < m
noncomputable def Zlt_next_check (n m : Int) : Unit :=
  ()

theorem Zlt_next (n m : Int) :
    ⦃⌜n < m⌝⦄
    (pure (Zlt_next_check n m) : Id Unit)
    ⦃⇓_ => ⌜m = Int.succ n ∨ Int.succ n < m⌝⦄ := by
  sorry

-- Coq: `Zle_next` — either m = n or succ n ≤ m when n ≤ m
noncomputable def Zle_next_check (n m : Int) : Unit :=
  ()

theorem Zle_next (n m : Int) :
    ⦃⌜n ≤ m⌝⦄
    (pure (Zle_next_check n m) : Id Unit)
    ⦃⇓_ => ⌜m = n ∨ Int.succ n ≤ m⌝⦄ := by
  sorry

-- Coq: `inj_pred` — Z_of_nat (pred n) = Z.pred (Z_of_nat n) for n ≠ 0
noncomputable def inj_pred_check (n : Nat) : Unit :=
  ()

theorem inj_pred (n : Nat) :
    ⦃⌜n ≠ 0⌝⦄
    (pure (inj_pred_check n) : Id Unit)
    ⦃⇓_ => ⌜Int.ofNat (Nat.pred n) = Int.pred (Int.ofNat n)⌝⦄ := by
  sorry

-- Coq: `Zle_abs` — p ≤ Z_of_nat (Z.abs_nat p)
noncomputable def Zle_abs_check (p : Int) : Unit :=
  ()

theorem Zle_abs (p : Int) :
    ⦃⌜True⌝⦄
    (pure (Zle_abs_check p) : Id Unit)
    ⦃⇓_ => ⌜p ≤ Int.ofNat (Int.natAbs p)⌝⦄ := by
  sorry

-- Coq: `inj_abs` — if 0 ≤ x then Z_of_nat (Z.abs_nat x) = x
noncomputable def inj_abs_check (x : Int) : Unit :=
  ()

theorem inj_abs (x : Int) :
    ⦃⌜0 ≤ x⌝⦄
    (pure (inj_abs_check x) : Id Unit)
    ⦃⇓_ => ⌜Int.ofNat (Int.natAbs x) = x⌝⦄ := by
  sorry

-- Coq `positive` compatibility and `nat_of_P`
structure Positive where
  val : Nat

noncomputable def nat_of_P (p : Positive) : Nat :=
  p.val.succ

-- ---------------------------------------------------------------------------
-- Coq: Pdiv and its correctness properties over positive numbers

-- Optional-positive to Nat (Coq oZ)
noncomputable def oZ (h : Option Positive) : Nat :=
  match h with
  | none => 0
  | some p => nat_of_P p

-- Coq: Pdiv — division with remainder on positives, returning quotient/remainder
-- We only need the interface here; implementation is deferred.
noncomputable def Pdiv (p q : Positive) : Option Positive × Option Positive :=
  (none, none)

-- Correctness of Pdiv (quotient-remainder form and remainder bound)
noncomputable def Pdiv_correct_check (p q : Positive) : Unit :=
  ()

theorem Pdiv_correct (p q : Positive) :
    ⦃⌜True⌝⦄
    (pure (Pdiv_correct_check p q) : Id Unit)
    ⦃⇓_ => ⌜nat_of_P p = oZ (Prod.fst (Pdiv p q)) * nat_of_P q + oZ (Prod.snd (Pdiv p q)) ∧
            oZ (Prod.snd (Pdiv p q)) < nat_of_P q⌝⦄ := by
  sorry

-- Bridge Option Positive to Int (Coq oZ1)
noncomputable def oZ1 (h : Option Positive) : Int :=
  match h with
  | none => 0
  | some p => Int.ofNat (nat_of_P p)

-- Coq: inj_oZ1 — Int/nat bridge for oZ/oZ1
noncomputable def inj_oZ1_check (z : Option Positive) : Unit :=
  ()

theorem inj_oZ1 (z : Option Positive) :
    ⦃⌜True⌝⦄
    (pure (inj_oZ1_check z) : Id Unit)
    ⦃⇓_ => ⌜oZ1 z = Int.ofNat (oZ z)⌝⦄ := by
  sorry

-- Coq: Zquotient — integer quotient using positive division on magnitudes
-- We mirror the Coq shape but keep a lightweight placeholder body for now.
noncomputable def Zquotient (m n : Int) : Int := 0

-- Coq: `ZquotientProp` — decomposition m = (Zquotient m n) * n + r with bounds
noncomputable def ZquotientProp_check (m n : Int) : Unit :=
  ()

theorem ZquotientProp (m n : Int) :
    ⦃⌜n ≠ 0⌝⦄
    (pure (ZquotientProp_check m n) : Id Unit)
    ⦃⇓_ => ⌜∃ r : Int,
            m = Zquotient m n * n + r ∧
            |Zquotient m n * n| ≤ |m| ∧
            |r| < |n|⌝⦄ := by
  sorry

-- Coq: Zdivides — m divides n means n = m * q (note Coq's argument order)
noncomputable def Zdivides (n m : Int) : Prop := ∃ q : Int, n = m * q

-- Coq: `ZdividesZquotient` — if m divides n and m ≠ 0 then
-- n = (Zquotient n m) * m
noncomputable def ZdividesZquotient_check (n m : Int) : Unit :=
  ()

theorem ZdividesZquotient (n m : Int) :
    ⦃⌜m ≠ 0 ∧ Zdivides n m⌝⦄
    (pure (ZdividesZquotient_check n m) : Id Unit)
    ⦃⇓_ => ⌜n = Zquotient n m * m⌝⦄ := by
  sorry

-- Coq: `ZdividesZquotientInv` — from decomposition n = (Zquotient n m) * m, deduce divisibility
noncomputable def ZdividesZquotientInv_check (n m : Int) : Unit :=
  ()

theorem ZdividesZquotientInv (n m : Int) :
    ⦃⌜n = Zquotient n m * m⌝⦄
    (pure (ZdividesZquotientInv_check n m) : Id Unit)
    ⦃⇓_ => ⌜Zdivides n m⌝⦄ := by
  sorry

-- Coq: `ZdividesMult` — if m divides n then p*m divides p*n
noncomputable def ZdividesMult_check (n m p : Int) : Unit :=
  ()

theorem ZdividesMult (n m p : Int) :
    ⦃⌜Zdivides n m⌝⦄
    (pure (ZdividesMult_check n m p) : Id Unit)
    ⦃⇓_ => ⌜Zdivides (p * n) (p * m)⌝⦄ := by
  sorry

-- Coq: `Zeq_mult_simpl` — cancel a nonzero multiplier on both sides of equality
noncomputable def Zeq_mult_simpl_check (a b c : Int) : Unit :=
  ()

theorem Zeq_mult_simpl (a b c : Int) :
    ⦃⌜c ≠ 0 ∧ a * c = b * c⌝⦄
    (pure (Zeq_mult_simpl_check a b c) : Id Unit)
    ⦃⇓_ => ⌜a = b⌝⦄ := by
  sorry

-- Coq: `ZdividesDiv` — if p ≠ 0 and p*m divides p*n, then m divides n
noncomputable def ZdividesDiv_check (n m p : Int) : Unit :=
  ()

theorem ZdividesDiv (n m p : Int) :
    ⦃⌜p ≠ 0 ∧ Zdivides (p * n) (p * m)⌝⦄
    (pure (ZdividesDiv_check n m p) : Id Unit)
    ⦃⇓_ => ⌜Zdivides n m⌝⦄ := by
  sorry

-- Coq: `Zdivides1` — every integer divides 1
noncomputable def Zdivides1_check (m : Int) : Unit :=
  ()

theorem Zdivides1 (m : Int) :
    ⦃⌜True⌝⦄
    (pure (Zdivides1_check m) : Id Unit)
    ⦃⇓_ => ⌜Zdivides m 1⌝⦄ := by
  sorry

-- Coq: `ZDividesLe` — if n ≠ 0 and n divides m then |m| ≤ |n|
noncomputable def ZDividesLe_check (n m : Int) : Unit :=
  ()

/-- Coq: `ZDividesLe` — divisibility bounds the absolute value. -/
theorem ZDividesLe (n m : Int) :
    ⦃⌜n ≠ 0 ∧ Zdivides n m⌝⦄
    (pure (ZDividesLe_check n m) : Id Unit)
    ⦃⇓_ => ⌜|m| ≤ |n|⌝⦄ := by
  sorry

-- Define a minimal placeholder for `digit` before its first use.
noncomputable def digit (n : Int) (q : Int) : Nat := 0

-- Context-specific helper for digit/precision lemmas translated from Coq.
noncomputable def digitPredVNumiSPrecision_check
    (radix : Int) (b : Fbound_skel) (precision : Nat) : Unit :=
  ()

/-- Coq: `digitPredVNumiSPrecision` — the digit of `pred (vNum b)` equals the precision
    when the bound's mantissa matches `radix^precision`. -/
theorem digitPredVNumiSPrecision
    (radix : Int) (b : Fbound_skel) (precision : Nat) :
    ⦃⌜precision ≠ 0 ∧ b.vNum = Zpower_nat radix precision⌝⦄
    (pure (digitPredVNumiSPrecision_check radix b precision) : Id Unit)
    ⦃⇓_ => ⌜digit radix (Int.pred b.vNum) = precision⌝⦄ := by
  intro _
  -- Statement imported from Coq; proof pending
  sorry

noncomputable def digitVNumiSPrecision_check
    (radix : Int) (b : Fbound_skel) (precision : Nat) : Unit :=
  ()

/-- Coq: `digitVNumiSPrecision` — the digit of `vNum b` is `precision + 1`
    under the standard bound relationship. -/
theorem digitVNumiSPrecision
    (radix : Int) (b : Fbound_skel) (precision : Nat) :
    ⦃⌜precision ≠ 0 ∧ b.vNum = Zpower_nat radix precision⌝⦄
    (pure (digitVNumiSPrecision_check radix b precision) : Id Unit)
    ⦃⇓_ => ⌜digit radix b.vNum = Nat.succ precision⌝⦄ := by
  intro _
  -- Statement imported from Coq; proof pending
  sorry

noncomputable def pGivesDigit_check {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `pGivesDigit` — bounded floats have digit ≤ precision. -/
theorem pGivesDigit {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b p⌝⦄
    (pure (pGivesDigit_check (beta:=beta) radix b precision p) : Id Unit)
    ⦃⇓_ => ⌜Fdigit (beta:=beta) radix p ≤ precision⌝⦄ := by
  intro _
  -- Placeholder for Coq proof port
  sorry

noncomputable def digitGivesBoundedNum_check {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `digitGivesBoundedNum` — digit bound implies vNum bound. -/
theorem digitGivesBoundedNum {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fdigit (beta:=beta) radix p ≤ precision⌝⦄
    (pure (digitGivesBoundedNum_check (beta:=beta) radix b precision p) : Id Unit)
    ⦃⇓_ => ⌜|p.Fnum| < b.vNum⌝⦄ := by
  intro _
  -- Placeholder for Coq proof port
  sorry

noncomputable def FnormalPrecision_check {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FnormalPrecision` — a normal float always has digit `precision`. -/
theorem FnormalPrecision {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fnormal (beta:=beta) radix b p⌝⦄
    (pure (FnormalPrecision_check (beta:=beta) radix b precision p) : Id Unit)
    ⦃⇓_ => ⌜Fdigit (beta:=beta) radix p = precision⌝⦄ := by
  intro _
  -- Imported statement; proof pending porting from Coq
  sorry

-- ---------------------------------------------------------------------------
-- Minimal normal mantissa (`nNormMin`) and related Coq lemmas

-- NOTE: `nNormMin` is defined earlier in this file (near firstNormalPos)

noncomputable def nNormPos_check (radix : Int) (precision : Nat) : Unit :=
  ()

/-- Coq: `nNormPos` — minimal normal mantissa is strictly positive. -/
theorem nNormPos (radix : Int) (precision : Nat) :
    ⦃⌜True⌝⦄
    (pure (nNormPos_check radix precision) : Id Unit)
    ⦃⇓_ => ⌜0 < nNormMin radix precision⌝⦄ := by
  intro _
  -- Proof port pending from Coq
  sorry

noncomputable def digitnNormMin_check (radix : Int) (precision : Nat) : Unit :=
  ()

/-- Coq: `digitnNormMin` — `digit radix nNormMin = precision`. -/
theorem digitnNormMin (radix : Int) (precision : Nat) :
    ⦃⌜True⌝⦄
    (pure (digitnNormMin_check radix precision) : Id Unit)
    ⦃⇓_ => ⌜digit radix (nNormMin radix precision) = precision⌝⦄ := by
  intro _
  -- Proof port pending from Coq
  sorry

noncomputable def vNumbMoreThanOne_check (b : Fbound_skel) (radix : Int) (precision : Nat) : Unit :=
  ()

/-- Coq: `vNumbMoreThanOne` — when `b.vNum = radix^precision` with positive `radix`
and nonzero `precision`, the bound exceeds 1. -/
theorem vNumbMoreThanOne
    (b : Fbound_skel) (radix : Int) (precision : Nat) :
    ⦃⌜precision ≠ 0 ∧ 1 < radix ∧ b.vNum = Zpower_nat radix precision⌝⦄
    (pure (vNumbMoreThanOne_check b radix precision) : Id Unit)
    ⦃⇓_ => ⌜(1 : Int) < b.vNum⌝⦄ := by
  intro h
  rcases h with ⟨hp, hr, hv⟩
  have hpow : (1 : Int) < Zpower_nat radix precision := by
    -- placeholder proof to be completed later
    sorry
  simpa [hv]

noncomputable def nNrMMimLevNum_check
    (radix : Int) (b : Fbound_skel) (precision : Nat) : Unit :=
  ()

/-- Coq: `nNrMMimLevNum` — minimal mantissa bounded by `vNum` under standard relation. -/
theorem nNrMMimLevNum (radix : Int) (b : Fbound_skel) (precision : Nat) :
    ⦃⌜b.vNum = Zpower_nat radix precision⌝⦄
    (pure (nNrMMimLevNum_check radix b precision) : Id Unit)
    ⦃⇓_ => ⌜nNormMin radix precision ≤ b.vNum⌝⦄ := by
  sorry

-- NOTE: `firstNormalPos` is defined earlier in this file (near nNormMin)

noncomputable def firstNormalPosNormal_check
    {beta : Int} (radix : Int) (b : Fbound_skel) (precision : Nat) : Unit :=
  ()

/-- Coq: `firstNormalPosNormal` — `firstNormalPos` is normal. -/
theorem firstNormalPosNormal {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat) :
    ⦃⌜True⌝⦄
    (pure (firstNormalPosNormal_check (beta:=beta) radix b precision) : Id Unit)
    ⦃⇓_ => ⌜Fnormal (beta:=beta) radix b (firstNormalPos (beta:=beta) radix b precision)⌝⦄ := by
  intro _
  -- Proof port pending from Coq
  sorry

noncomputable def pNormal_absolu_min_check {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `pNormal_absolu_min` — normal mantissas dominate `nNormMin`. -/
theorem pNormal_absolu_min {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fnormal (beta:=beta) radix b p⌝⦄
    (pure (pNormal_absolu_min_check (beta:=beta) radix b precision p) : Id Unit)
    ⦃⇓_ => ⌜nNormMin radix precision ≤ |p.Fnum|⌝⦄ := by
  intro _
  -- Proof port pending from Coq
  sorry

noncomputable def FnormalLtFirstNormalPos_check {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FnormalLtFirstNormalPos` — normal nonnegative floats dominate
the first normal positive value. -/
theorem FnormalLtFirstNormalPos {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fnormal (beta:=beta) radix b p ∧ 0 ≤ _root_.F2R (beta:=beta) p⌝⦄
    (pure (FnormalLtFirstNormalPos_check (beta:=beta) radix b precision p) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (beta:=beta)
            (firstNormalPos (beta:=beta) radix b precision)
            ≤ _root_.F2R (beta:=beta) p⌝⦄ := by
  intro _
  -- Proof port pending from Coq
  sorry

noncomputable def FsubnormalDigit_check {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FsubnormalDigit` — a subnormal float has digit strictly below
`precision`. Mirrors the original statement with Hoare triple syntax. -/
theorem FsubnormalDigit {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fsubnormal (beta:=beta) radix b p⌝⦄
    (pure (FsubnormalDigit_check (beta:=beta) radix b precision p) : Id Unit)
    ⦃⇓_ => ⌜Fdigit (beta:=beta) radix p < precision⌝⦄ := by
  intro _
  -- Imported from Coq; proof to be filled when the arithmetic lemmas land
  sorry

-- Coq: `pSubnormal_absolu_min` — subnormal mantissas lie below `nNormMin`.
noncomputable def pSubnormal_absolu_min_check {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `pSubnormal_absolu_min` — the absolute mantissa of a subnormal is
bounded by `nNormMin`. -/
theorem pSubnormal_absolu_min {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fsubnormal (beta:=beta) radix b p⌝⦄
    (pure (pSubnormal_absolu_min_check (beta:=beta) radix b precision p) : Id Unit)
    ⦃⇓_ => ⌜|p.Fnum| < nNormMin radix precision⌝⦄ := by
  intro _
  -- Proof deferred to a future ported development step
  sorry

noncomputable def FsubnormalLtFirstNormalPos_check {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FsubnormalLtFirstNormalPos` — a nonnegative subnormal float lies
strictly below the first positive normal float. -/
theorem FsubnormalLtFirstNormalPos {beta : Int}
    (radix : Int) (b : Fbound_skel) (precision : Nat)
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fsubnormal (beta:=beta) radix b p ∧
        0 ≤ _root_.F2R (beta:=beta) p⌝⦄
    (pure (FsubnormalLtFirstNormalPos_check (beta:=beta) radix b precision p) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (beta:=beta) p <
            _root_.F2R (beta:=beta)
              (firstNormalPos (beta:=beta) radix b precision)⌝⦄ := by
  intro _
  -- Proof deferred; follows Coq's `FsubnormalLtFirstNormalPos` argument
  sorry

noncomputable def FsubnormalnormalLtPos_check {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FsubnormalnormalLtPos` — a nonnegative subnormal float is strictly
below any nonnegative normal float. -/
theorem FsubnormalnormalLtPos {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fsubnormal (beta:=beta) radix b p ∧
        Fnormal (beta:=beta) radix b q ∧
        0 ≤ _root_.F2R (beta:=beta) p ∧
        0 ≤ _root_.F2R (beta:=beta) q⌝⦄
    (pure (FsubnormalnormalLtPos_check (beta:=beta) radix b p q) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (beta:=beta) p <
            _root_.F2R (beta:=beta) q⌝⦄ := by
  intro _
  -- Direct port of Coq's `FsubnormalnormalLtPos`; proof deferred
  sorry

noncomputable def FsubnormalnormalLtNeg_check {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FsubnormalnormalLtNeg` — a nonpositive subnormal float is strictly
above any nonpositive normal float. -/
theorem FsubnormalnormalLtNeg {beta : Int}
    (radix : Int) (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fsubnormal (beta:=beta) radix b p ∧
        Fnormal (beta:=beta) radix b q ∧
        _root_.F2R (beta:=beta) p ≤ 0 ∧
        _root_.F2R (beta:=beta) q ≤ 0⌝⦄
    (pure (FsubnormalnormalLtNeg_check (beta:=beta) radix b p q) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (beta:=beta) q <
            _root_.F2R (beta:=beta) p⌝⦄ := by
  intro _
  -- Direct port of Coq's `FsubnormalnormalLtNeg`; proof deferred
  sorry

noncomputable def FnormalUnique_check {beta : Int}
    (radix : ℝ) (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FnormalUnique` — normal floats that agree as reals are equal. -/
theorem FnormalUnique {beta : Int}
    (radix : ℝ) (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fnormal (beta:=beta) radix b p ∧
        Fnormal (beta:=beta) radix b q ∧
        _root_.F2R (beta:=beta) p = _root_.F2R (beta:=beta) q⌝⦄
    (pure (FnormalUnique_check (beta:=beta) radix b p q) : Id Unit)
    ⦃⇓_ => ⌜p = q⌝⦄ :=
  sorry

-- Coq: `FnormalLtPos` — ordered normal floats compare via exponent then mantissa.
noncomputable def FnormalLtPos_check {beta : Int}
    (radix : ℝ) (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FnormalLtPos` — if `p` and `q` are normal, `0 ≤ F2R p`, and
    `_root_.F2R p < _root_.F2R q`, then either `p.Fexp < q.Fexp` or their
    exponents coincide while `p.Fnum < q.Fnum`. -/
theorem FnormalLtPos {beta : Int}
    (radix : ℝ) (b : Fbound_skel)
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fnormal (beta:=beta) radix b p ∧
        Fnormal (beta:=beta) radix b q ∧
        0 ≤ _root_.F2R (beta:=beta) p ∧
        _root_.F2R (beta:=beta) p < _root_.F2R (beta:=beta) q⌝⦄
    (pure (FnormalLtPos_check (beta:=beta) radix b p q) : Id Unit)
    ⦃⇓_ => ⌜p.Fexp < q.Fexp ∨
            (p.Fexp = q.Fexp ∧ p.Fnum < q.Fnum)⌝⦄ :=
  sorry


noncomputable def vNumPrecision_check
    (b : Fbound_skel) (radix : Int) (precision : Nat) (n : Int) : Unit :=
  ()

/-- Coq: `vNumPrecision` — if `digit radix n ≤ precision` then
`|n| < b.vNum`. -/
theorem vNumPrecision
    (b : Fbound_skel) (radix : Int) (precision : Nat) (n : Int) :
    ⦃⌜digit radix n ≤ precision⌝⦄
    (pure (vNumPrecision_check b radix precision n) : Id Unit)
    ⦃⇓_ => ⌜|n| < b.vNum⌝⦄ := by
  sorry

-- Coq: `NotDividesDigit` — if 1 < r and v ≠ 0 then v does not divide r^(digit r v)
noncomputable def NotDividesDigit_check (r v : Int) : Unit :=
  ()

/-- Coq: `NotDividesDigit` — no divisibility at the digit boundary. -/
theorem NotDividesDigit (r v : Int) :
    ⦃⌜1 < r ∧ v ≠ 0⌝⦄
    (pure (NotDividesDigit_check r v) : Id Unit)
    ⦃⇓_ => ⌜¬ Zdivides v (Zpower_nat r (digit r v))⌝⦄ := by
  sorry

-- Coq: `ZquotientPos` — if z1 ≥ 0 and z2 ≥ 0 then Zquotient z1 z2 ≥ 0
noncomputable def ZquotientPos_check (z1 z2 : Int) : Unit :=
  ()

/-- Coq: `ZquotientPos` — positivity of quotient under nonnegativity hypotheses. -/
theorem ZquotientPos (z1 z2 : Int) :
    ⦃⌜0 ≤ z1 ∧ 0 ≤ z2⌝⦄
    (pure (ZquotientPos_check z1 z2) : Id Unit)
    ⦃⇓_ => ⌜0 ≤ Zquotient z1 z2⌝⦄ := by
  sorry

-- Coq: `inject_nat_convert` — if p = Zpos q then Z_of_nat (nat_of_P q) = p
noncomputable def inject_nat_convert_check (p : Int) (q : Positive) : Unit :=
  ()

theorem inject_nat_convert (p : Int) (q : Positive) :
    ⦃⌜p = Int.ofNat (nat_of_P q)⌝⦄
    (pure (inject_nat_convert_check p q) : Id Unit)
    ⦃⇓_ => ⌜Int.ofNat (nat_of_P q) = p⌝⦄ := by
  -- Trivial restatement in Lean; Coq version states for Zpos q.
  sorry

-- Coq: `Zabs_eq_opp` — if x ≤ 0 then |x| = -x
noncomputable def Zabs_eq_opp_check (x : Int) : Unit :=
  ()

theorem Zabs_eq_opp (x : Int) :
    ⦃⌜x ≤ 0⌝⦄
    (pure (Zabs_eq_opp_check x) : Id Unit)
    ⦃⇓_ => ⌜|x| = -x⌝⦄ := by
  sorry

-- Coq: `Zabs_Zs` — |succ z| ≤ succ |z|
noncomputable def Zabs_Zs_check (z : Int) : Unit :=
  ()

theorem Zabs_Zs (z : Int) :
    ⦃⌜True⌝⦄
    (pure (Zabs_Zs_check z) : Id Unit)
    ⦃⇓_ => ⌜|Int.succ z| ≤ Int.succ |z|⌝⦄ := by
  sorry

-- Coq: `lt_Zlt_inv` — if Z_of_nat n < Z_of_nat m then n < m
noncomputable def lt_Zlt_inv_check (n m : Nat) : Unit :=
  ()

theorem lt_Zlt_inv (n m : Nat) :
    ⦃⌜Int.ofNat n < Int.ofNat m⌝⦄
    (pure (lt_Zlt_inv_check n m) : Id Unit)
    ⦃⇓_ => ⌜n < m⌝⦄ := by
  sorry

-- Coq: `Zle_Zpred` — if x < y then x ≤ pred y
noncomputable def Zle_Zpred_check (x y : Int) : Unit :=
  ()

theorem Zle_Zpred (x y : Int) :
    ⦃⌜x < y⌝⦄
    (pure (Zle_Zpred_check x y) : Id Unit)
    ⦃⇓_ => ⌜x ≤ Int.pred y⌝⦄ := by
  sorry

-- Coq: `NconvertO` — nat_of_P p <> 0 for positive p
noncomputable def NconvertO_check (p : Positive) : Unit :=
  ()

theorem NconvertO (p : Positive) :
    ⦃⌜True⌝⦄
    (pure (NconvertO_check p) : Id Unit)
    ⦃⇓_ => ⌜nat_of_P p ≠ 0⌝⦄ := by
  sorry

-- Coq: `convert_not_O` — nat_of_P p <> 0 for positive p (alias of NconvertO)
noncomputable def convert_not_O_check (p : Positive) : Unit :=
  ()

theorem convert_not_O (p : Positive) :
    ⦃⌜True⌝⦄
    (pure (convert_not_O_check p) : Id Unit)
    ⦃⇓_ => ⌜nat_of_P p ≠ 0⌝⦄ := by
  -- Mirrors `NconvertO`; proof deferred per import task.
  sorry

-- Coq: `Zle_Zabs` — z ≤ |z|
noncomputable def Zle_Zabs_check (z : Int) : Unit :=
  ()

theorem Zle_Zabs (z : Int) :
    ⦃⌜True⌝⦄
    (pure (Zle_Zabs_check z) : Id Unit)
    ⦃⇓_ => ⌜z ≤ |z|⌝⦄ := by
  sorry

-- We declare the `_check` and theorem later after `pff_to_flocq` is defined.

-- Coq: `absolu_lt_nz` — if z ≠ 0 then 0 < Z.abs_nat z
noncomputable def absolu_lt_nz_check (z : Int) : Unit :=
  ()

theorem absolu_lt_nz (z : Int) :
    ⦃⌜z ≠ 0⌝⦄
    (pure (absolu_lt_nz_check z) : Id Unit)
    ⦃⇓_ => ⌜0 < Int.natAbs z⌝⦄ := by
  sorry

-- List operations used in Pff
def list_sum (l : List ℝ) : ℝ :=
  l.foldr (· + ·) 0

def list_prod (l : List ℝ) : ℝ :=
  l.foldr (· * ·) 1

-- Enumerating consecutive integers (Coq: mZlist and friends)
def mZlist_aux (p : Int) (n : Nat) : List Int :=
  match n with
  | 0 => [p]
  | Nat.succ n' => p :: mZlist_aux (p + 1) n'

noncomputable def mZlist_aux_correct_check (n : Nat) (p q : Int) : Unit :=
  ()

/-- Coq: `mZlist_aux_correct` — if `p ≤ q ≤ p + Z_of_nat n` then `q ∈ mZlist_aux p n`.
We mirror the statement using the project's hoare-triple style; proof deferred. -/
theorem mZlist_aux_correct (n : Nat) (p q : Int) :
    ⦃⌜p ≤ q ∧ q ≤ p + Int.ofNat n⌝⦄
    (pure (mZlist_aux_correct_check n p q) : Id Unit)
    ⦃⇓_ => ⌜List.Mem q (mZlist_aux p n)⌝⦄ := by
  sorry

noncomputable def mZlist_aux_correct_rev1_check (n : Nat) (p q : Int) : Unit :=
  ()

/-- Coq: `mZlist_aux_correct_rev1` — if `q ∈ mZlist_aux p n` then `p ≤ q`.
Hoare-triple wrapper; proof deferred. -/
theorem mZlist_aux_correct_rev1 (n : Nat) (p q : Int) :
    ⦃⌜List.Mem q (mZlist_aux p n)⌝⦄
    (pure (mZlist_aux_correct_rev1_check n p q) : Id Unit)
    ⦃⇓_ => ⌜p ≤ q⌝⦄ := by
  sorry

noncomputable def mZlist_aux_correct_rev2_check (n : Nat) (p q : Int) : Unit :=
  ()

/-- Coq: `mZlist_aux_correct_rev2` — membership implies upper bound by `p + n`.
Hoare-triple wrapper; proof deferred. -/
theorem mZlist_aux_correct_rev2 (n : Nat) (p q : Int) :
    ⦃⌜List.Mem q (mZlist_aux p n)⌝⦄
    (pure (mZlist_aux_correct_rev2_check n p q) : Id Unit)
    ⦃⇓_ => ⌜q ≤ p + Int.ofNat n⌝⦄ := by
  sorry

def mZlist (p q : Int) : List Int :=
  let d := q - p
  if h0 : d = 0 then
    [p]
  else if hpos : d > 0 then
    mZlist_aux p (Int.toNat d)
  else
    []

noncomputable def mZlist_correct_check (p q r : Int) : Unit :=
  ()

/-- Coq: `mZlist_correct` — if `p ≤ r ≤ q` then `r ∈ mZlist p q`.
Hoare-triple wrapper; proof deferred. -/
theorem mZlist_correct (p q r : Int) :
    ⦃⌜p ≤ r ∧ r ≤ q⌝⦄
    (pure (mZlist_correct_check p q r) : Id Unit)
    ⦃⇓_ => ⌜List.Mem r (mZlist p q)⌝⦄ := by
  sorry

noncomputable def mZlist_correct_rev1_check (p q r : Int) : Unit :=
  ()

/-- Coq: `mZlist_correct_rev1` — membership implies lower bound `p ≤ r`. -/
theorem mZlist_correct_rev1 (p q r : Int) :
    ⦃⌜List.Mem r (mZlist p q)⌝⦄
    (pure (mZlist_correct_rev1_check p q r) : Id Unit)
    ⦃⇓_ => ⌜p ≤ r⌝⦄ := by
  sorry

noncomputable def mZlist_correct_rev2_check (p q r : Int) : Unit :=
  ()

/-- Coq: `mZlist_correct_rev2` — membership implies upper bound `r ≤ q`. -/
theorem mZlist_correct_rev2 (p q r : Int) :
    ⦃⌜List.Mem r (mZlist p q)⌝⦄
    (pure (mZlist_correct_rev2_check p q r) : Id Unit)
    ⦃⇓_ => ⌜r ≤ q⌝⦄ := by
  sorry

-- Cartesian product list (Coq: mProd)
def mProd {A B : Type} (l1 : List A) (l2 : List B) : List (A × B) :=
  match l2 with
  | [] => []
  | b :: l2' => (l1.map (fun a => (a, b))) ++ mProd l1 l2'

noncomputable def mProd_correct_check {A B : Type}
    (l1 : List A) (l2 : List B) (a : A) (b : B) : Unit :=
  ()

/-- Coq: `mProd_correct` — if `a ∈ l1` and `b ∈ l2` then `(a,b) ∈ mProd l1 l2`. -/
theorem mProd_correct {A B : Type}
    (l1 : List A) (l2 : List B) (a : A) (b : B) :
    ⦃⌜List.Mem a l1 ∧ List.Mem b l2⌝⦄
    (pure (mProd_correct_check l1 l2 a b) : Id Unit)
    ⦃⇓_ => ⌜List.Mem (a, b) (mProd l1 l2)⌝⦄ := by
  sorry

noncomputable def mProd_correct_rev1_check {A B : Type}
    (l1 : List A) (l2 : List B) (a : A) (b : B) : Unit :=
  ()

/-- Coq: `mProd_correct_rev1` — if `(a,b) ∈ mProd l1 l2` then `a ∈ l1`. -/
theorem mProd_correct_rev1 {A B : Type}
    (l1 : List A) (l2 : List B) (a : A) (b : B) :
    ⦃⌜List.Mem (a, b) (mProd l1 l2)⌝⦄
    (pure (mProd_correct_rev1_check l1 l2 a b) : Id Unit)
    ⦃⇓_ => ⌜List.Mem a l1⌝⦄ := by
  sorry

noncomputable def mProd_correct_rev2_check {A B : Type}
    (l1 : List A) (l2 : List B) (a : A) (b : B) : Unit :=
  ()

/-- Coq: `mProd_correct_rev2` — if `(a,b) ∈ mProd l1 l2` then `b ∈ l2`. -/
theorem mProd_correct_rev2 {A B : Type}
    (l1 : List A) (l2 : List B) (a : A) (b : B) :
    ⦃⌜List.Mem (a, b) (mProd l1 l2)⌝⦄
    (pure (mProd_correct_rev2_check l1 l2 a b) : Id Unit)
    ⦃⇓_ => ⌜List.Mem b l2⌝⦄ := by
  sorry

noncomputable def in_map_inv_check {A B : Type}
    (f : A → B) (l : List A) (x : A) : Unit :=
  ()

/-- Coq: `in_map_inv` — if `f` is injective and `f x ∈ map f l` then `x ∈ l`. -/
theorem in_map_inv {A B : Type}
    (f : A → B) (l : List A) (x : A) :
    ⦃⌜(∀ a b, f a = f b → a = b) ∧ List.Mem (f x) (l.map f)⌝⦄
    (pure (in_map_inv_check f l x) : Id Unit)
    ⦃⇓_ => ⌜List.Mem x l⌝⦄ := by
  sorry

-- Legacy floating-point format compatibility
structure PffFloat where
  mantissa : Int
  exponent : Int
  sign : Bool

-- Equality of Flocq-style floats by components (Coq: `floatEq`)
-- We mirror Coq's record equality lemma for the Flocq float record
-- (with fields `Fnum` and `Fexp`).
noncomputable def floatEq_check {beta : Int}
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem floatEq {beta : Int}
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜p.Fnum = q.Fnum ∧ p.Fexp = q.Fexp⌝⦄
    (pure (floatEq_check p q) : Id Unit)
    ⦃⇓_ => ⌜p = q⌝⦄ := by
  sorry

-- Decidability of equality for Core floats (Coq: `floatDec`)
noncomputable def floatDec_check {beta : Int}
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem floatDec {beta : Int}
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (floatDec_check x y) : Id Unit)
    ⦃⇓_ => ⌜x = y ∨ x ≠ y⌝⦄ := by
  sorry

-- Conversion between Pff and Flocq formats
def pff_to_flocq (beta : Int) (f : PffFloat) : FloatSpec.Core.Defs.FlocqFloat beta :=
  FloatSpec.Core.Defs.FlocqFloat.mk (if f.sign then -f.mantissa else f.mantissa) f.exponent

def flocq_to_pff {beta : Int} (f : FloatSpec.Core.Defs.FlocqFloat beta) : PffFloat :=
  { mantissa := Int.natAbs f.Fnum,
    exponent := f.Fexp,
    sign := f.Fnum < 0 }


-- Zero float at exponent z (Coq: `Fzero`)
def Fzero (beta : Int) (z : Int) : FloatSpec.Core.Defs.FlocqFloat beta :=
  FloatSpec.Core.Defs.FlocqFloat.mk 0 z

-- Coq: `FzeroisReallyZero` — real value of zero float is 0
noncomputable def FzeroisReallyZero_check {beta : Int} (z : Int) : Unit :=
  ()

theorem FzeroisReallyZero {beta : Int} (z : Int) :
    ⦃⌜True⌝⦄
    (pure (FzeroisReallyZero_check (beta:=beta) z) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (Fzero beta z) = 0⌝⦄ := by
  sorry

-- Coq: `FzeroisZero` — specialized form using a bound's exponent
noncomputable def FzeroisZero_check {beta : Int}
    (b : Fbound_skel) : Unit :=
  ()

theorem FzeroisZero {beta : Int}
    (b : Fbound_skel) :
    ⦃⌜True⌝⦄
    (pure (FzeroisZero_check (beta:=beta) b) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (Fzero beta (- b.dExp)) = 0⌝⦄ := by
  sorry

-- Coq: `FboundedFzero` — the zero float is bounded for any bound descriptor
noncomputable def FboundedFzero_check {beta : Int}
    (b : Fbound_skel) : Unit :=
  ()

theorem FboundedFzero {beta : Int}
    (b : Fbound_skel) :
    ⦃⌜True⌝⦄
    (pure (FboundedFzero_check (beta:=beta) b) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b (Fzero beta (- b.dExp))⌝⦄ := by
  sorry

-- Coq: `FboundedZeroSameExp` — boundedness preserved when replacing mantissa by zero at same exponent
noncomputable def FboundedZeroSameExp_check {beta : Int}
    (b : Fbound_skel) (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem FboundedZeroSameExp {beta : Int}
    (b : Fbound_skel) (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b p⌝⦄
    (pure (FboundedZeroSameExp_check (beta:=beta) b p) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b (Fzero beta (p.Fexp))⌝⦄ := by
  sorry

-- Coq: `FBoundedScale` — scaling exponent by natural n preserves boundedness
noncomputable def FBoundedScale_check {beta : Int}
    (b : Fbound_skel) (p : FloatSpec.Core.Defs.FlocqFloat beta) (n : Nat) : Unit :=
  ()

theorem FBoundedScale {beta : Int}
    (b : Fbound_skel) (p : FloatSpec.Core.Defs.FlocqFloat beta) (n : Nat) :
    ⦃⌜Fbounded (beta:=beta) b p⌝⦄
    (pure (FBoundedScale_check (beta:=beta) b p n) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b ⟨p.Fnum, p.Fexp + (Int.ofNat n)⟩⌝⦄ := by
  sorry

-- Coq: `FvalScale` — value after scaling exponent equals multiplication by powerRZ
noncomputable def FvalScale_check {beta : Int}
    (b : Fbound_skel) (p : FloatSpec.Core.Defs.FlocqFloat beta) (n : Nat) : Unit :=
  ()

theorem FvalScale (beta : Int)
    (b : Fbound_skel) (p : FloatSpec.Core.Defs.FlocqFloat beta) (n : Nat) :
    ⦃⌜True⌝⦄
    (pure (FvalScale_check (beta:=beta) b p n) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (beta:=beta) ⟨p.Fnum, p.Fexp + (Int.ofNat n)⟩ =
            ((beta : ℝ) ^ (Int.ofNat n)) * _root_.F2R (beta:=beta) p⌝⦄ := by
  sorry

-- Coq: `maxFbounded` — the maximal mantissa at exponent z is bounded
-- In this Lean port, we use a canonical representative with mantissa 1
-- due to the simplified bound skeleton (no vNum field). This preserves
-- the intent that there exists a bounded float at any exponent z above
-- the minimal exponent bound.
noncomputable def maxFbounded_check {beta : Int}
    (b : Fbound_skel) (z : Int) : Unit :=
  ()

theorem maxFbounded {beta : Int}
    (b : Fbound_skel) (z : Int) :
    ⦃⌜- b.dExp ≤ z⌝⦄
    (pure (maxFbounded_check (beta:=beta) b z) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b (FloatSpec.Core.Defs.FlocqFloat.mk (beta:=beta) 1 z)⌝⦄ := by
  sorry

-- Coq: `oppBounded` — boundedness preserved under negation
noncomputable def oppBounded_check {beta : Int}
    (b : Fbound_skel) (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem oppBounded {beta : Int}
    (b : Fbound_skel) (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b x⌝⦄
    (pure (oppBounded_check (beta:=beta) b x) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b (Fopp x)⌝⦄ := by
  sorry

-- Coq: `oppBoundedInv` — boundedness inversion under negation
noncomputable def oppBoundedInv_check {beta : Int}
    (b : Fbound_skel) (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `oppBoundedInv` — if `Fopp x` is bounded then `x` is bounded.
    Hoare-triple style statement mirroring Pff.v; proof deferred. -/
theorem oppBoundedInv {beta : Int}
    (b : Fbound_skel) (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b (Fopp x)⌝⦄
    (pure (oppBoundedInv_check (beta:=beta) b x) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b x⌝⦄ := by
  sorry

-- Coq: `absFBounded` — boundedness preserved under absolute value
noncomputable def absFBounded_check {beta : Int}
    (b : Fbound_skel) (f : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `absFBounded` — if `f` is bounded then `Fabs f` is also bounded.
    Hoare-triple style statement; proof deferred. -/
theorem absFBounded {beta : Int}
    (b : Fbound_skel) (f : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b f⌝⦄
    (pure (absFBounded_check (beta:=beta) b f) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b (Fabs f)⌝⦄ := by
  sorry

-- Coq: `FboundedEqExp` — transfer boundedness along equal value and exp inequality
noncomputable def FboundedEqExp_check {beta : Int}
    (b : Fbound_skel) (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `FboundedEqExp` — if `p` is bounded, `F2R p = F2R q`, and `p.Fexp ≤ q.Fexp`,
    then `q` is bounded. Statement mirrors Pff.v; proof deferred. -/
theorem FboundedEqExp {beta : Int}
    (b : Fbound_skel) (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b p ∧ _root_.F2R p = _root_.F2R q ∧ p.Fexp ≤ q.Fexp⌝⦄
    (pure (FboundedEqExp_check (beta:=beta) b p q) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b q⌝⦄ := by
  sorry

-- Coq: `is_Fzero_rep1` — zero mantissa implies zero real value
noncomputable def is_Fzero_rep1_check {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem is_Fzero_rep1 {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜is_Fzero x⌝⦄
    (pure (is_Fzero_rep1_check x) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R x = 0⌝⦄ := by
  sorry

-- Coq: `is_Fzero_rep2` — zero real value implies zero mantissa
noncomputable def is_Fzero_rep2_check {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem is_Fzero_rep2 {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜_root_.F2R x = 0⌝⦄
    (pure (is_Fzero_rep2_check x) : Id Unit)
    ⦃⇓_ => ⌜is_Fzero x⌝⦄ := by
  sorry

-- Coq: `NisFzeroComp` — if x is not zero and F2R x = F2R y then y is not zero
noncomputable def NisFzeroComp_check {beta : Int}
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem NisFzeroComp {beta : Int}
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜¬ is_Fzero x ∧ _root_.F2R x = _root_.F2R y⌝⦄
    (pure (NisFzeroComp_check x y) : Id Unit)
    ⦃⇓_ => ⌜¬ is_Fzero y⌝⦄ := by
  sorry

-- Coq: `Fle_Zle` — compare two floats of same exponent by their mantissas
-- We mirror the Coq statement Fle_Zle: n1 ≤ n2 → Fle (Float n1 d) (Float n2 d)
-- Our Pff compatibility struct `PffFloat` uses fields (mantissa, exponent, sign).
-- We state an analogous lemma at the level of reals via `F2R ∘ pff_to_flocq`.
noncomputable def Fle_Zle_check (beta : Int) (n1 n2 d : Int) : Unit :=
  ()

theorem Fle_Zle (beta : Int) (n1 n2 d : Int) :
    ⦃⌜n1 ≤ n2⌝⦄
    (pure (Fle_Zle_check beta n1 n2 d) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (pff_to_flocq beta { mantissa := n1, exponent := d, sign := false })
            ≤ _root_.F2R (pff_to_flocq beta { mantissa := n2, exponent := d, sign := false })⌝⦄ := by
  sorry

-- Coq: `Rlt_Fexp_eq_Zlt` — if x < y and Fexp x = Fexp y then Fnum x < Fnum y
noncomputable def Rlt_Fexp_eq_Zlt_check {beta : Int}
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem Rlt_Fexp_eq_Zlt {beta : Int}
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜_root_.F2R x < _root_.F2R y ∧ x.Fexp = y.Fexp⌝⦄
    (pure (Rlt_Fexp_eq_Zlt_check (beta:=beta) x y) : Id Unit)
    ⦃⇓_ => ⌜x.Fnum < y.Fnum⌝⦄ := by
  sorry

-- Coq: `Fopp_correct` — float negation corresponds to real negation
noncomputable def Fopp_correct_check {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem Fopp_correct {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (Fopp_correct_check (beta:=beta) x) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (FloatSpec.Calc.Operations.Fopp (beta:=beta) x) = - _root_.F2R x⌝⦄ := by
  sorry

-- Coq: `Fplus_correct` — float addition corresponds to real addition
noncomputable def Fplus_correct_check {beta : Int}
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem Fplus_correct {beta : Int}
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (Fplus_correct_check (beta:=beta) x y) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (Fplus (beta:=beta) x y) = _root_.F2R x + _root_.F2R y⌝⦄ := by
  sorry

-- Coq: `Fminus_correct` — float subtraction corresponds to real subtraction
noncomputable def Fminus_correct_check {beta : Int}
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem Fminus_correct {beta : Int}
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (Fminus_correct_check (beta:=beta) x y) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (FloatSpec.Calc.Operations.Fminus (beta:=beta) x y) =
            _root_.F2R x - _root_.F2R y⌝⦄ := by
  sorry

-- Coq: `Fopp_Fopp` — involutive property of float negation
noncomputable def Fopp_Fopp_check {beta : Int}
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem Fopp_Fopp {beta : Int}
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (Fopp_Fopp_check (beta:=beta) p) : Id Unit)
    ⦃⇓_ => ⌜Fopp (beta:=beta) (Fopp (beta:=beta) p) = p⌝⦄ := by
  sorry

-- Coq: `Fopp_Fminus` — negation of a subtraction swaps the operands
noncomputable def Fopp_Fminus_check {beta : Int}
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem Fopp_Fminus {beta : Int}
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (Fopp_Fminus_check (beta:=beta) p q) : Id Unit)
    ⦃⇓_ => ⌜Fopp (beta:=beta)
              (FloatSpec.Calc.Operations.Fminus (beta:=beta) p q) =
            FloatSpec.Calc.Operations.Fminus (beta:=beta) q p⌝⦄ := by
  sorry

-- Coq: `Fdigit_opp` — digit invariant under negation
noncomputable def Fdigit_opp_check {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem Fdigit_opp {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (Fdigit_opp_check (beta:=beta) radix x) : Id Unit)
    ⦃⇓_ => ⌜Fdigit (beta:=beta) radix (Fopp x) = Fdigit (beta:=beta) radix x⌝⦄ := by
  sorry

-- Coq: `Fopp_Fminus_dist` — negation distributes over subtraction
noncomputable def Fopp_Fminus_dist_check {beta : Int}
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem Fopp_Fminus_dist {beta : Int}
    (p q : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (Fopp_Fminus_dist_check (beta:=beta) p q) : Id Unit)
    ⦃⇓_ => ⌜Fopp (beta:=beta)
              (FloatSpec.Calc.Operations.Fminus (beta:=beta) p q) =
            FloatSpec.Calc.Operations.Fminus (beta:=beta)
              (Fopp (beta:=beta) p) (Fopp (beta:=beta) q)⌝⦄ := by
  sorry

/-!
Sterbenz lemmas (missing from Coq Pff.v)

We introduce Coq's `SterbenzAux` in the project's Hoare‑triple style. It uses
the placeholders `Fbounded` and the operation `Fminus` available in this file.
Proof is deferred as per the import instructions.
-/

noncomputable def SterbenzAux_check {beta : Int}
    (b : Fbound_skel)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `SterbenzAux` — if `x` and `y` are bounded in the same bound `b` and
    satisfy `F2R y ≤ F2R x ≤ 2 * F2R y`, then `Fminus x y` is bounded in `b`. -/
theorem SterbenzAux {beta : Int}
    (b : Fbound_skel)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b x ∧
        Fbounded (beta:=beta) b y ∧
        (_root_.F2R y) ≤ (_root_.F2R x) ∧
        (_root_.F2R x) ≤ 2 * (_root_.F2R y)⌝⦄
    (pure (SterbenzAux_check (beta:=beta) b x y) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b (FloatSpec.Calc.Operations.Fminus (beta:=beta) x y)⌝⦄ := by
  sorry

-- Coq: `Sterbenz` — symmetric bound version using 1/2 ≤ x/y ≤ 2
noncomputable def Sterbenz_check {beta : Int}
    (b : Fbound_skel)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `Sterbenz` — if `x` and `y` are bounded in `b` and satisfy
    `(1/2)*F2R y ≤ F2R x ≤ 2 * F2R y`, then `Fminus x y` is bounded in `b`. -/
theorem Sterbenz {beta : Int}
    (b : Fbound_skel)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜Fbounded (beta:=beta) b x ∧
        Fbounded (beta:=beta) b y ∧
        ((1/2 : ℝ) * (_root_.F2R y)) ≤ (_root_.F2R x) ∧
        (_root_.F2R x) ≤ 2 * (_root_.F2R y)⌝⦄
    (pure (Sterbenz_check (beta:=beta) b x y) : Id Unit)
    ⦃⇓_ => ⌜Fbounded (beta:=beta) b (FloatSpec.Calc.Operations.Fminus (beta:=beta) x y)⌝⦄ := by
  sorry

-- Coq: `Fdigit_abs` — digit invariant under absolute value
noncomputable def Fdigit_abs_check {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem Fdigit_abs {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (Fdigit_abs_check (beta:=beta) radix x) : Id Unit)
    ⦃⇓_ => ⌜Fdigit (beta:=beta) radix (Fabs (beta:=beta) x) = Fdigit (beta:=beta) radix x⌝⦄ := by
  sorry

-- Coq: `Fabs_correct1` — if 0 ≤ F2R x then F2R (Fabs x) = F2R x
noncomputable def Fabs_correct1_check {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem Fabs_correct1 {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜0 ≤ _root_.F2R x⌝⦄
    (pure (Fabs_correct1_check (beta:=beta) x) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (Fabs (beta:=beta) x) = _root_.F2R x⌝⦄ := by
  sorry

-- Coq: `Fabs_correct2` — if F2R x ≤ 0 then F2R (Fabs x) = - F2R x
noncomputable def Fabs_correct2_check {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem Fabs_correct2 {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜_root_.F2R x ≤ 0⌝⦄
    (pure (Fabs_correct2_check (beta:=beta) x) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (Fabs (beta:=beta) x) = - _root_.F2R x⌝⦄ := by
  sorry

-- Coq: `Fabs_correct` — F2R (Fabs x) = |F2R x|
noncomputable def Fabs_correct_check {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem Fabs_correct {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (Fabs_correct_check (beta:=beta) x) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (Fabs (beta:=beta) x) = |_root_.F2R x|⌝⦄ := by
  sorry

-- Coq: `RleFexpFabs` — for nonzero real value, Float 1 (Fexp p) ≤ Fabs p
noncomputable def RleFexpFabs_check {beta : Int}
    (p : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem RleFexpFabs {beta : Int}
    (p : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜_root_.F2R p ≠ 0⌝⦄
    (pure (RleFexpFabs_check (beta:=beta) p) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (FloatSpec.Core.Defs.FlocqFloat.mk (beta:=beta) 1 p.Fexp)
            ≤ _root_.F2R (Fabs (beta:=beta) p)⌝⦄ := by
  sorry

-- Coq: `Fabs_Fzero` — nonzero stays nonzero under absolute value
noncomputable def Fabs_Fzero_check {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem Fabs_Fzero {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜¬ is_Fzero x⌝⦄
    (pure (Fabs_Fzero_check (beta:=beta) x) : Id Unit)
    ⦃⇓_ => ⌜¬ is_Fzero (Fabs (beta:=beta) x)⌝⦄ := by
  sorry

-- Compatibility operations
def pff_add (x y : PffFloat) : PffFloat := by
  sorry

def pff_mul (x y : PffFloat) : PffFloat := by
  sorry

-- Error bounds compatibility
noncomputable def pff_error_bound (prec : Int) : ℝ :=
  (2 : ℝ)^(-prec)

-- Legacy rounding modes
inductive PffRounding where
  | RN : PffRounding  -- Round to nearest
  | RZ : PffRounding  -- Round toward zero
  | RP : PffRounding  -- Round toward plus infinity
  | RM : PffRounding  -- Round toward minus infinity

-- Convert Pff rounding to Flocq rounding
def pff_to_flocq_rnd (mode : PffRounding) : ℝ → Int := by
  sorry

-- ---------------------------------------------------------------
-- Minimal LSB/MSB infrastructure (placeholders for compatibility)

-- A simplistic divisor-count function used in Coq's LSB definition.
-- Here we only need the type to state lemmas; its actual behavior
-- is irrelevant for this port's specifications.
noncomputable def maxDiv (v : Int) (p : Nat) : Nat := 0

-- Number of significant digits of a float at a given radix (placeholder)
-- (moved earlier)

-- Shift operation on floats (placeholder, no-op)
-- NOTE: a duplicate placeholder existed later; keep only the early one above.

-- Coq: `FshiftFdigit` — ~is_Fzero x -> Fdigit (Fshift n x) = Fdigit x + n
noncomputable def FshiftFdigit_check {beta : Int}
    (radix : Int) (n : Nat) (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem FshiftFdigit {beta : Int}
    (radix : Int) (n : Nat) (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜¬ is_Fzero x⌝⦄
    (pure (FshiftFdigit_check (beta:=beta) radix n x) : Id Unit)
    ⦃⇓_ => ⌜Fdigit (beta:=beta) radix (Fshift (beta:=beta) radix n x) =
            Fdigit (beta:=beta) radix x + n⌝⦄ := by
  sorry

-- Coq: `FshiftCorrect` — shifting does not change the real value
noncomputable def FshiftCorrect_check {beta : Int}
    (radix : Int) (n : Nat) (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem FshiftCorrect {beta : Int}
    (radix : Int) (n : Nat) (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (FshiftCorrect_check (beta:=beta) radix n x) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R (Fshift (beta:=beta) radix n x) = _root_.F2R x⌝⦄ := by
  sorry

-- Coq: `FshiftCorrectInv` — align exponents by shifting the larger one down
noncomputable def FshiftCorrectInv_check {beta : Int}
    (radix : Int)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem FshiftCorrectInv {beta : Int}
    (radix : Int)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜_root_.F2R x = _root_.F2R y ∧ x.Fexp ≤ y.Fexp⌝⦄
    (pure (FshiftCorrectInv_check (beta:=beta) radix x y) : Id Unit)
    ⦃⇓_ => ⌜Fshift (beta:=beta) radix (Int.natAbs (y.Fexp - x.Fexp)) y = x⌝⦄ := by
  sorry

-- Coq: `FshiftO` — shifting by 0 is identity
noncomputable def FshiftO_check {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem FshiftO {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (FshiftO_check (beta:=beta) radix x) : Id Unit)
    ⦃⇓_ => ⌜Fshift (beta:=beta) radix 0 x = x ⌝⦄ := by
  sorry

-- Coq: `FshiftCorrectSym` — equal reals imply some shifts match
noncomputable def FshiftCorrectSym_check {beta : Int}
    (radix : Int) (x y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem FshiftCorrectSym {beta : Int}
    (radix : Int) (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜_root_.F2R x = _root_.F2R y⌝⦄
    (pure (FshiftCorrectSym_check (beta:=beta) radix x y) : Id Unit)
    ⦃⇓_ => ⌜∃ n m : Nat, Fshift (beta:=beta) radix n x = Fshift (beta:=beta) radix m y⌝⦄ := by
  sorry

-- Coq: `FdigitEq` — if not zero and same real/digit, floats are equal
noncomputable def FdigitEq_check {beta : Int}
    (radix : Int) (x y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem FdigitEq {beta : Int}
    (radix : Int) (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜¬ is_Fzero x ∧ _root_.F2R x = _root_.F2R y ∧
        Fdigit (beta:=beta) radix x = Fdigit (beta:=beta) radix y⌝⦄
    (pure (FdigitEq_check (beta:=beta) radix x y) : Id Unit)
    ⦃⇓_ => ⌜x = y⌝⦄ := by
  sorry

-- Least significant bit position of a float (placeholder definition)
noncomputable def LSB {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) : Int :=
  Int.ofNat (maxDiv x.Fnum (Fdigit (beta:=beta) radix x)) + x.Fexp

-- Coq: `LSB_shift` — ~is_Fzero x -> LSB x = LSB (Fshift n x)
noncomputable def LSB_shift_check {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) (n : Nat) : Unit :=
  ()

theorem LSB_shift {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) (n : Nat) :
    ⦃⌜¬ is_Fzero x⌝⦄
    (pure (LSB_shift_check (beta:=beta) radix x n) : Id Unit)
    ⦃⇓_ => ⌜LSB (beta:=beta) radix x = LSB (beta:=beta) radix (Fshift (beta:=beta) radix n x)⌝⦄ := by
  sorry

-- Coq: `maxDivLess` — maxDiv v p ≤ p
noncomputable def maxDivLess_check (v : Int) (p : Nat) : Unit :=
  ()

theorem maxDivLess (v : Int) (p : Nat) :
    ⦃⌜True⌝⦄
    (pure (maxDivLess_check v p) : Id Unit)
    ⦃⇓_ => ⌜maxDiv v p ≤ p⌝⦄ := by
  sorry

-- Coq: `LSB_comp` — ~is_Fzero x → x = y :>R → LSB x = LSB y
noncomputable def LSB_comp_check {beta : Int}
    (radix : Int)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) (n : Nat) : Unit :=
  ()

theorem LSB_comp {beta : Int}
    (radix : Int)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) (n : Nat) :
    ⦃⌜¬ is_Fzero x ∧ _root_.F2R x = _root_.F2R y⌝⦄
    (pure (LSB_comp_check (beta:=beta) radix x y n) : Id Unit)
    ⦃⇓_ => ⌜LSB (beta:=beta) radix x = LSB (beta:=beta) radix y⌝⦄ := by
  sorry

-- Coq: `maxDivCorrect` — Zdivides v (radix^maxDiv v p)
noncomputable def maxDivCorrect_check (radix : Int) (v : Int) (p : Nat) : Unit :=
  ()

/-- Coq: `maxDivCorrect` — for any integer `v` and natural `p`,
`v` divides `radix^(maxDiv v p)`. We only state the property here. -/
theorem maxDivCorrect (radix : Int) (v : Int) (p : Nat) :
    ⦃⌜True⌝⦄
    (pure (maxDivCorrect_check radix v p) : Id Unit)
    ⦃⇓_ => ⌜Zdivides v (Zpower_nat radix (maxDiv v p))⌝⦄ := by
  sorry

-- Coq: `maxDivLt` — ~Zdivides v (radix^p) → maxDiv v p < p
noncomputable def maxDivLt_check (radix : Int) (v : Int) (p : Nat) : Unit :=
  ()

/-- Coq: `maxDivLt` — if `v` does not divide `radix^p` then the maximal
exponent `maxDiv v p` is strictly less than `p`. Statement only. -/
theorem maxDivLt (radix : Int) (v : Int) (p : Nat) :
    ⦃⌜¬ Zdivides v (Zpower_nat radix p)⌝⦄
    (pure (maxDivLt_check radix v p) : Id Unit)
    ⦃⇓_ => ⌜maxDiv v p < p⌝⦄ := by
  sorry

-- Coq: `maxDiv_opp` — maxDiv v p = maxDiv (-v) p
noncomputable def maxDiv_opp_check (v : Int) (p : Nat) : Unit :=
  ()

theorem maxDiv_opp (v : Int) (p : Nat) :
    ⦃⌜True⌝⦄
    (pure (maxDiv_opp_check v p) : Id Unit)
    ⦃⇓_ => ⌜maxDiv v p = maxDiv (-v) p⌝⦄ := by
  sorry

-- Coq: `LSB_opp` — LSB x = LSB (Fopp x)
noncomputable def LSB_opp_check {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem LSB_opp {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (LSB_opp_check (beta:=beta) radix x) : Id Unit)
    ⦃⇓_ => ⌜LSB (beta:=beta) radix x = LSB (beta:=beta) radix (Fopp x)⌝⦄ := by
  sorry

-- Coq: `maxDiv_abs` — maxDiv v p = maxDiv (|v|) p
noncomputable def maxDiv_abs_check (v : Int) (p : Nat) : Unit :=
  ()

theorem maxDiv_abs (v : Int) (p : Nat) :
    ⦃⌜True⌝⦄
    (pure (maxDiv_abs_check v p) : Id Unit)
    ⦃⇓_ => ⌜maxDiv v p = maxDiv |v| p⌝⦄ := by
  sorry

-- Coq: `LSB_abs` — LSB x = LSB (Fabs x)
noncomputable def LSB_abs_check {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem LSB_abs {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (LSB_abs_check (beta:=beta) radix x) : Id Unit)
    ⦃⇓_ => ⌜LSB (beta:=beta) radix x = LSB (beta:=beta) radix (Fabs x)⌝⦄ := by
  sorry

-- Most significant bit position of a float (placeholder definition)
noncomputable def MSB {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) : Int :=
  Int.pred (Int.ofNat (Fdigit (beta:=beta) radix x) + x.Fexp)

-- Coq: `MSB_shift` — ~is_Fzero x -> MSB x = MSB (Fshift n x)
noncomputable def MSB_shift_check {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) (n : Nat) : Unit :=
  ()

theorem MSB_shift {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) (n : Nat) :
    ⦃⌜¬ is_Fzero x⌝⦄
    (pure (MSB_shift_check (beta:=beta) radix x n) : Id Unit)
    ⦃⇓_ => ⌜MSB (beta:=beta) radix x = MSB (beta:=beta) radix (Fshift (beta:=beta) radix n x)⌝⦄ := by
  sorry

-- Coq: `MSB_comp` — ~is_Fzero x → x = y :>R → MSB x = MSB y
noncomputable def MSB_comp_check {beta : Int}
    (radix : Int)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) (n : Nat) : Unit :=
  ()

theorem MSB_comp {beta : Int}
    (radix : Int)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) (n : Nat) :
    ⦃⌜¬ is_Fzero x ∧ _root_.F2R x = _root_.F2R y⌝⦄
    (pure (MSB_comp_check (beta:=beta) radix x y n) : Id Unit)
    ⦃⇓_ => ⌜MSB (beta:=beta) radix x = MSB (beta:=beta) radix y⌝⦄ := by
  sorry

-- Coq: `MSB_opp` — MSB x = MSB (Fopp x)
noncomputable def MSB_opp_check {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem MSB_opp {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (MSB_opp_check (beta:=beta) radix x) : Id Unit)
    ⦃⇓_ => ⌜MSB (beta:=beta) radix x = MSB (beta:=beta) radix (Fopp x)⌝⦄ := by
  sorry

-- Coq: `MSB_abs` — MSB x = MSB (Fabs x)
noncomputable def MSB_abs_check {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem MSB_abs {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (MSB_abs_check (beta:=beta) radix x) : Id Unit)
    ⦃⇓_ => ⌜MSB (beta:=beta) radix x = MSB (beta:=beta) radix (Fabs x)⌝⦄ := by
  sorry

-- Coq: `LSB_le_MSB` — for nonzero floats, least ≤ most significant bit
noncomputable def LSB_le_MSB_check {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem LSB_le_MSB {beta : Int}
    (radix : Int) (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜¬ is_Fzero x⌝⦄
    (pure (LSB_le_MSB_check (beta:=beta) radix x) : Id Unit)
    ⦃⇓_ => ⌜LSB (beta:=beta) radix x ≤ MSB (beta:=beta) radix x⌝⦄ := by
  sorry

-- Coq: `Zlt_mult_simpl_l` — cancel positive multiplier on left for <
noncomputable def Zlt_mult_simpl_l_check (a b c : Int) : Unit :=
  ()

theorem Zlt_mult_simpl_l (a b c : Int) :
    ⦃⌜0 < c ∧ c * a < c * b⌝⦄
    (pure (Zlt_mult_simpl_l_check a b c) : Id Unit)
    ⦃⇓_ => ⌜a < b⌝⦄ := by
  sorry

-- Coq: `Z_eq_bool_correct` — boolean equality correctness for Int
noncomputable def Z_eq_bool (p q : Int) : Bool := decide (p = q)

noncomputable def Z_eq_bool_correct_check (p q : Int) : Unit :=
  ()

theorem Z_eq_bool_correct (p q : Int) :
    ⦃⌜True⌝⦄
    (pure (Z_eq_bool_correct_check p q) : Id Unit)
    ⦃⇓_ => ⌜(if Z_eq_bool p q then p = q else p ≠ q)⌝⦄ := by
  sorry

-- Coq: `Zcompare_correct` — trichotomy via a comparison function
noncomputable def Zcompare (p q : Int) : Ordering :=
  if p < q then Ordering.lt else if p = q then Ordering.eq else Ordering.gt

noncomputable def Zcompare_correct_check (p q : Int) : Unit :=
  ()

theorem Zcompare_correct (p q : Int) :
    ⦃⌜True⌝⦄
    (pure (Zcompare_correct_check p q) : Id Unit)
    ⦃⇓_ => ⌜match Zcompare p q with
            | Ordering.gt => q < p
            | Ordering.lt => p < q
            | Ordering.eq => p = q⌝⦄ := by
  sorry

-- Coq: `Zabs_Zopp` — | -z | = | z |
noncomputable def Zabs_Zopp_check (z : Int) : Unit :=
  ()

theorem Zabs_Zopp (z : Int) :
    ⦃⌜True⌝⦄
    (pure (Zabs_Zopp_check z) : Id Unit)
    ⦃⇓_ => ⌜|-z| = |z|⌝⦄ := by
  sorry

-- Coq: `Zle_Zpred_Zpred` — predecessor is monotone
noncomputable def Zle_Zpred_Zpred_check (z1 z2 : Int) : Unit :=
  ()

theorem Zle_Zpred_Zpred (z1 z2 : Int) :
    ⦃⌜z1 ≤ z2⌝⦄
    (pure (Zle_Zpred_Zpred_check z1 z2) : Id Unit)
    ⦃⇓_ => ⌜Int.pred z1 ≤ Int.pred z2⌝⦄ := by
  sorry

-- Coq: `Zle_n_Zpred` — cancel pred on both sides for ≤
noncomputable def Zle_n_Zpred_check (z1 z2 : Int) : Unit :=
  ()

theorem Zle_n_Zpred (z1 z2 : Int) :
    ⦃⌜Int.pred z1 ≤ Int.pred z2⌝⦄
    (pure (Zle_n_Zpred_check z1 z2) : Id Unit)
    ⦃⇓_ => ⌜z1 ≤ z2⌝⦄ := by
  sorry

-- Coq: `Zlt_1_O` — 1 ≤ z → 0 < z
noncomputable def Zlt_1_O_check (z : Int) : Unit :=
  ()

theorem Zlt_1_O (z : Int) :
    ⦃⌜1 ≤ z⌝⦄
    (pure (Zlt_1_O_check z) : Id Unit)
    ⦃⇓_ => ⌜0 < z⌝⦄ := by
  sorry

noncomputable def LtR0Fnum_check {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem LtR0Fnum {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜0 < _root_.F2R x⌝⦄
    (pure (LtR0Fnum_check (beta:=beta) x) : Id Unit)
    ⦃⇓_ => ⌜0 < x.Fnum⌝⦄ := by
  sorry

-- Coq: `LeR0Fnum` — 0 ≤ x → 0 ≤ Fnum x
noncomputable def LeR0Fnum_check {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem LeR0Fnum {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜0 ≤ _root_.F2R x⌝⦄
    (pure (LeR0Fnum_check (beta:=beta) x) : Id Unit)
    ⦃⇓_ => ⌜0 ≤ x.Fnum⌝⦄ := by
  sorry

-- Coq: `LeFnumZERO` — 0 ≤ Fnum x → 0 ≤ x
noncomputable def LeFnumZERO_check {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem LeFnumZERO {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜0 ≤ x.Fnum⌝⦄
    (pure (LeFnumZERO_check (beta:=beta) x) : Id Unit)
    ⦃⇓_ => ⌜0 ≤ _root_.F2R x⌝⦄ := by
  sorry

-- Coq: `R0LtFnum` — x < 0 → Fnum x < 0
noncomputable def R0LtFnum_check {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem R0LtFnum {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜_root_.F2R x < 0⌝⦄
    (pure (R0LtFnum_check (beta:=beta) x) : Id Unit)
    ⦃⇓_ => ⌜x.Fnum < 0⌝⦄ := by
  sorry

-- Coq: `R0LeFnum` — x ≤ 0 → Fnum x ≤ 0
noncomputable def R0LeFnum_check {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem R0LeFnum {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜_root_.F2R x ≤ 0⌝⦄
    (pure (R0LeFnum_check (beta:=beta) x) : Id Unit)
    ⦃⇓_ => ⌜x.Fnum ≤ 0⌝⦄ := by
  sorry

-- Coq: `LeZEROFnum` — Fnum x ≤ 0 → x ≤ 0
noncomputable def LeZEROFnum_check {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem LeZEROFnum {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜x.Fnum ≤ 0⌝⦄
    (pure (LeZEROFnum_check (beta:=beta) x) : Id Unit)
    ⦃⇓_ => ⌜_root_.F2R x ≤ 0⌝⦄ := by
  sorry

-- Coq: `LtFnumZERO` — 0 < Fnum x → 0 < x
noncomputable def LtFnumZERO_check {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

theorem LtFnumZERO {beta : Int}
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜0 < x.Fnum⌝⦄
    (pure (LtFnumZERO_check (beta:=beta) x) : Id Unit)
    ⦃⇓_ => ⌜0 < _root_.F2R x⌝⦄ := by
  sorry

-- Coq: `Zlt_Zabs_inv1` — |z1| < z2 → -z2 < z1
noncomputable def Zlt_Zabs_inv1_check (z1 z2 : Int) : Unit :=
  ()

theorem Zlt_Zabs_inv1 (z1 z2 : Int) :
    ⦃⌜|z1| < z2⌝⦄
    (pure (Zlt_Zabs_inv1_check z1 z2) : Id Unit)
    ⦃⇓_ => ⌜-z2 < z1⌝⦄ := by
  sorry

-- Coq: `Zle_Zabs_inv1` — |z1| ≤ z2 → -z2 ≤ z1
noncomputable def Zle_Zabs_inv1_check (z1 z2 : Int) : Unit :=
  ()

theorem Zle_Zabs_inv1 (z1 z2 : Int) :
    ⦃⌜|z1| ≤ z2⌝⦄
    (pure (Zle_Zabs_inv1_check z1 z2) : Id Unit)
    ⦃⇓_ => ⌜-z2 ≤ z1⌝⦄ := by
  sorry

-- Coq: `Zle_Zabs_inv2` — |z1| ≤ z2 → z1 ≤ z2
noncomputable def Zle_Zabs_inv2_check (z1 z2 : Int) : Unit :=
  ()

theorem Zle_Zabs_inv2 (z1 z2 : Int) :
    ⦃⌜|z1| ≤ z2⌝⦄
    (pure (Zle_Zabs_inv2_check z1 z2) : Id Unit)
    ⦃⇓_ => ⌜z1 ≤ z2⌝⦄ := by
  sorry

-- Coq: `Zlt_Zabs_Zpred` — if |z1| < z2 and z1 ≠ pred z2 then |succ z1| < z2
noncomputable def Zlt_Zabs_Zpred_check (z1 z2 : Int) : Unit :=
  ()

theorem Zlt_Zabs_Zpred (z1 z2 : Int) :
    ⦃⌜|z1| < z2 ∧ z1 ≠ Int.pred z2⌝⦄
    (pure (Zlt_Zabs_Zpred_check z1 z2) : Id Unit)
    ⦃⇓_ => ⌜|Int.succ z1| < z2⌝⦄ := by
  sorry

-- (removed duplicate EvenO declarations)

-- Coq: `Zlt_not_eq_rev` — if q < p then p ≠ q
noncomputable def Zlt_not_eq_rev_check (p q : Int) : Unit :=
  ()

theorem Zlt_not_eq_rev (p q : Int) :
    ⦃⌜q < p⌝⦄
    (pure (Zlt_not_eq_rev_check p q) : Id Unit)
    ⦃⇓_ => ⌜p ≠ q⌝⦄ := by
  sorry

-- Coq: `Zle_Zpred_inv` — if z1 ≤ pred z2 then z1 < z2
noncomputable def Zle_Zpred_inv_check (z1 z2 : Int) : Unit :=
  ()

theorem Zle_Zpred_inv (z1 z2 : Int) :
    ⦃⌜z1 ≤ Int.pred z2⌝⦄
    (pure (Zle_Zpred_inv_check z1 z2) : Id Unit)
    ⦃⇓_ => ⌜z1 < z2⌝⦄ := by
  sorry

-- Coq: `Zabs_intro` — if `P` holds for `-z` and `z`, it holds for `|z|`
noncomputable def Zabs_intro_check (P : Int → Prop) (z : Int) : Unit :=
  ()

theorem Zabs_intro (P : Int → Prop) (z : Int) :
    ⦃⌜P (-z) ∧ P z⌝⦄
    (pure (Zabs_intro_check P z) : Id Unit)
    ⦃⇓_ => ⌜P (|z|)⌝⦄ := by
  sorry

-- Coq: `Zpred_Zle_Zabs_intro` — if -pred z2 ≤ z1 ≤ pred z2 then |z1| < z2
noncomputable def Zpred_Zle_Zabs_intro_check (z1 z2 : Int) : Unit :=
  ()

theorem Zpred_Zle_Zabs_intro (z1 z2 : Int) :
    ⦃⌜-Int.pred z2 ≤ z1 ∧ z1 ≤ Int.pred z2⌝⦄
    (pure (Zpred_Zle_Zabs_intro_check z1 z2) : Id Unit)
    ⦃⇓_ => ⌜|z1| < z2⌝⦄ := by
  sorry

-- Coq: `Zlt_Zabs_intro` — if -z2 < z1 < z2 then |z1| < z2
noncomputable def Zlt_Zabs_intro_check (z1 z2 : Int) : Unit :=
  ()

theorem Zlt_Zabs_intro (z1 z2 : Int) :
    ⦃⌜-z2 < z1 ∧ z1 < z2⌝⦄
    (pure (Zlt_Zabs_intro_check z1 z2) : Id Unit)
    ⦃⇓_ => ⌜|z1| < z2⌝⦄ := by
  sorry

-- Coq: `Zpower_nat_less` — for q > 0, Zpower_nat n q > 0
noncomputable def Zpower_nat_less_check (n : Int) (q : Nat) : Unit :=
  ()

theorem Zpower_nat_less (n : Int) (q : Nat) :
    ⦃⌜0 < q⌝⦄
    (pure (Zpower_nat_less_check n q) : Id Unit)
    ⦃⇓_ => ⌜0 < n ^ q⌝⦄ := by
  sorry

-- Coq: `Zpower_nat_monotone_S` — n^(q+1) ≥ n^q for n ≥ 1
noncomputable def Zpower_nat_monotone_S_check (n : Int) (q : Nat) : Unit :=
  ()

theorem Zpower_nat_monotone_S (n : Int) (q : Nat) :
    ⦃⌜1 ≤ n⌝⦄
    (pure (Zpower_nat_monotone_S_check n q) : Id Unit)
    ⦃⇓_ => ⌜n ^ q ≤ n ^ (q+1)⌝⦄ := by
  sorry

-- Coq: `Zpower_nat_monotone_lt` — if 1 < n then n^q < n^(q+1)
noncomputable def Zpower_nat_monotone_lt_check (n : Int) (q : Nat) : Unit :=
  ()

theorem Zpower_nat_monotone_lt (n : Int) (q : Nat) :
    ⦃⌜1 < n⌝⦄
    (pure (Zpower_nat_monotone_lt_check n q) : Id Unit)
    ⦃⇓_ => ⌜n ^ q < n ^ (q+1)⌝⦄ := by
  sorry

-- Coq: `Zpower_nat_anti_monotone_lt` — if 0 ≤ n < 1 then n^(q+1) < n^q
noncomputable def Zpower_nat_anti_monotone_lt_check (n : Int) (q : Nat) : Unit :=
  ()

theorem Zpower_nat_anti_monotone_lt (n : Int) (q : Nat) :
    ⦃⌜0 ≤ n ∧ n < 1⌝⦄
    (pure (Zpower_nat_anti_monotone_lt_check n q) : Id Unit)
    ⦃⇓_ => ⌜n ^ (q+1) < n ^ q⌝⦄ := by
  sorry

-- Coq: `Zpower_nat_monotone_le` — if 1 ≤ n then n^q ≤ n^r for q ≤ r
noncomputable def Zpower_nat_monotone_le_check (n : Int) (q r : Nat) : Unit :=
  ()

theorem Zpower_nat_monotone_le (n : Int) (q r : Nat) :
    ⦃⌜1 ≤ n ∧ q ≤ r⌝⦄
    (pure (Zpower_nat_monotone_le_check n q r) : Id Unit)
    ⦃⇓_ => ⌜n ^ q ≤ n ^ r⌝⦄ := by
  sorry

-- Alias for Coq's Zpower_nat on integers
-- (moved earlier)

-- Coq: `digitAux1` — (Zpower_nat n (S p) * r) = (Zpower_nat n p * (n * r))
noncomputable def digitAux1_check (n : Int) (p : Nat) (r : Int) : Unit :=
  ()

theorem digitAux1 (n : Int) (p : Nat) (r : Int) :
    ⦃⌜True⌝⦄
    (pure (digitAux1_check n p r) : Id Unit)
    ⦃⇓_ => ⌜Zpower_nat n (Nat.succ p) * r = Zpower_nat n p * (n * r)⌝⦄ := by
  sorry

-- Minimal positive and digit infrastructure used by digit lemmas
-- Reuse existing `Positive` defined above; define a placeholder `digitAux`.
noncomputable def digitAux (n v r : Int) (q : Positive) : Nat := 0

-- Coq: `digitAuxLess`
noncomputable def digitAuxLess_check (n : Int) (v r : Int) (q : Positive) : Unit :=
  ()

theorem digitAuxLess (n : Int) (v r : Int) (q : Positive) :
    ⦃⌜True⌝⦄
    (pure (digitAuxLess_check n v r q) : Id Unit)
    ⦃⇓_ => ⌜match digitAux n v r q with
            | Nat.succ r' => Zpower_nat n r' * r ≤ v
            | 0 => True⌝⦄ := by
  sorry

-- Coq: `digitLess` — if q ≠ 0 then Zpower_nat n (pred (digit q)) ≤ |q|
noncomputable def digitLess_check (n : Int) (q : Int) : Unit :=
  ()

-- `digit` is defined earlier near its first use (NotDividesDigit).

theorem digitLess (n : Int) (q : Int) :
    ⦃⌜q ≠ 0⌝⦄
    (pure (digitLess_check n q) : Id Unit)
    ⦃⇓_ => ⌜Zpower_nat n (Nat.pred (digit n q)) ≤ |q|⌝⦄ := by
  sorry

-- Length of a positive number in base-2 (placeholder)
noncomputable def pos_length (p : Positive) : Nat := 0

-- Coq: `pos_length_pow` — Zpos p < Zpower_nat n (S (pos_length p))
noncomputable def pos_length_pow_check (n : Int) (p : Positive) : Unit :=
  ()

theorem pos_length_pow (n : Int) (p : Positive) :
    ⦃⌜True⌝⦄
    (pure (pos_length_pow_check n p) : Id Unit)
    ⦃⇓_ => ⌜Int.ofNat (nat_of_P p) < Zpower_nat n (Nat.succ (pos_length p))⌝⦄ := by
  sorry

-- Coq: `digitMore` — |q| < Zpower_nat n (digit q)
noncomputable def digitMore_check (n : Int) (q : Int) : Unit :=
  ()

theorem digitMore (n : Int) (q : Int) :
    ⦃⌜True⌝⦄
    (pure (digitMore_check n q) : Id Unit)
    ⦃⇓_ => ⌜|q| < Zpower_nat n (digit n q)⌝⦄ := by
  sorry

-- Coq: `digitAuxMore` — complementary case for digit auxiliary
noncomputable def digitAuxMore_check (n : Int) (v r : Int) (p : Positive) : Unit :=
  ()

theorem digitAuxMore (n : Int) (v r : Int) (p : Positive) :
    ⦃⌜True⌝⦄
    (pure (digitAuxMore_check n v r p) : Id Unit)
    ⦃⇓_ => ⌜match digitAux n v r p with
            | Nat.succ r' => v < Zpower_nat n r' * r
            | 0 => True⌝⦄ := by
  sorry

-- Coq: `digitInv` — if n^(pred r) ≤ |q| < n^r then digit n q = r
noncomputable def digitInv_check (n : Int) (q : Int) (r : Nat) : Unit :=
  ()

theorem digitInv (n : Int) (q : Int) (r : Nat) :
    ⦃⌜Zpower_nat n (Nat.pred r) ≤ |q| ∧ |q| < Zpower_nat n r⌝⦄
    (pure (digitInv_check n q r) : Id Unit)
    ⦃⇓_ => ⌜digit n q = r⌝⦄ := by
  sorry

-- Coq: `digit_monotone` — if |p| ≤ |q| then digit n p ≤ digit n q
noncomputable def digit_monotone_check (n : Int) (p q : Int) : Unit :=
  ()

theorem digit_monotone (n : Int) (p q : Int) :
    ⦃⌜|p| ≤ |q|⌝⦄
    (pure (digit_monotone_check n p q) : Id Unit)
    ⦃⇓_ => ⌜digit n p ≤ digit n q⌝⦄ := by
  sorry

-- Coq: `digitNotZero` — if q ≠ 0 then 0 < digit n q
noncomputable def digitNotZero_check (n : Int) (q : Int) : Unit :=
  ()

theorem digitNotZero (n : Int) (q : Int) :
    ⦃⌜q ≠ 0⌝⦄
    (pure (digitNotZero_check n q) : Id Unit)
    ⦃⇓_ => ⌜0 < digit n q⌝⦄ := by
  sorry

-- Coq: `digitAdd` — digit n (q * n^r) = digit n q + r for q ≠ 0
noncomputable def digitAdd_check (n : Int) (q : Int) (r : Nat) : Unit :=
  ()

theorem digitAdd (n : Int) (q : Int) (r : Nat) :
    ⦃⌜q ≠ 0⌝⦄
    (pure (digitAdd_check n q r) : Id Unit)
    ⦃⇓_ => ⌜digit n (q * Zpower_nat n r) = digit n q + r⌝⦄ := by
  sorry

-- Coq: `maxDivPlus` — multiplicative stability of maxDiv against n-th power of radix
noncomputable def maxDivPlus_check (radix : Int) (v : Int) (n : Nat) : Unit :=
  ()

theorem maxDivPlus (radix : Int) (v : Int) (n : Nat) :
    ⦃⌜v ≠ 0⌝⦄
    (pure (maxDivPlus_check radix v n) : Id Unit)
    ⦃⇓_ => ⌜maxDiv (v * Zpower_nat radix n) (digit radix v + n) =
            maxDiv v (digit radix v) + n⌝⦄ := by
  sorry

-- Coq: `digit_abs` — digit n (|p|) = digit n p
noncomputable def digit_abs_check (n : Int) (p : Int) : Unit :=
  ()

theorem digit_abs (n : Int) (p : Int) :
    ⦃⌜True⌝⦄
    (pure (digit_abs_check n p) : Id Unit)
    ⦃⇓_ => ⌜digit n (|p|) = digit n p⌝⦄ := by
  sorry

-- Coq: `digit_anti_monotone_lt` — if 1 < n and digit n p < digit n q, then |p| < |q|
noncomputable def digit_anti_monotone_lt_check (n : Int) (p q : Int) : Unit :=
  ()

theorem digit_anti_monotone_lt (n : Int) (p q : Int) :
    ⦃⌜1 < n ∧ digit n p < digit n q⌝⦄
    (pure (digit_anti_monotone_lt_check n p q) : Id Unit)
    ⦃⇓_ => ⌜|p| < |q|⌝⦄ := by
  sorry
