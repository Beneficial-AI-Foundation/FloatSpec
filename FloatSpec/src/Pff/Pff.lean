-- Legacy Pff library compatibility layer
-- Translated from Coq file: flocq/src/Pff/Pff.v

import Std.Do.Triple
import FloatSpec.src.Core
import FloatSpec.src.Compat
import Mathlib.Data.Real.Basic

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
  sorry

theorem not_odd_0 : ¬nat_odd 0 := by
  sorry

-- Double operation
def nat_double (n : Nat) : Nat := 2 * n

-- Division by 2
def nat_div2 (n : Nat) : Nat := n / 2

-- Even/Odd characterization
theorem even_iff_double (n : Nat) : nat_even n ↔ n = nat_double (nat_div2 n) := by
  sorry

theorem odd_iff_double (n : Nat) : nat_odd n ↔ n = nat_double (nat_div2 n) + 1 := by
  sorry

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
  sorry

theorem pow_neg (r : ℝ) (z : Int) :
  r^(-z) = (r^z)⁻¹ := by
  sorry

-- Real number compatibility
theorem abs_inv_compat (r : ℝ) : |r⁻¹| = |r|⁻¹ := by
  sorry

-- Coq: `pow_NR0` — if e ≠ 0 then e^n ≠ 0
noncomputable def pow_NR0_check (e : ℝ) (n : Nat) : Id Unit :=
  pure ()

theorem pow_NR0 (e : ℝ) (n : Nat) :
    ⦃⌜e ≠ 0⌝⦄
    pow_NR0_check e n
    ⦃⇓_ => ⌜e ^ n ≠ 0⌝⦄ := by
  sorry

-- Coq: `pow_add` — e^(n+m) = e^n * e^m
noncomputable def pow_add_compat_check (e : ℝ) (n m : Nat) : Id Unit :=
  pure ()

-- Renamed to avoid clashing with Mathlib's `pow_add`
theorem pow_add_compat (e : ℝ) (n m : Nat) :
    ⦃⌜True⌝⦄
    pow_add_compat_check e n m
    ⦃⇓_ => ⌜e ^ (n + m) = e ^ n * e ^ m⌝⦄ := by
  sorry

-- Coq: `pow_RN_plus` — e ≠ 0 → e^n = e^(n+m) * (e^m)⁻¹
noncomputable def pow_RN_plus_check (e : ℝ) (n m : Nat) : Id Unit :=
  pure ()

theorem pow_RN_plus (e : ℝ) (n m : Nat) :
    ⦃⌜e ≠ 0⌝⦄
    pow_RN_plus_check e n m
    ⦃⇓_ => ⌜e ^ n = e ^ (n + m) * (e ^ m)⁻¹⌝⦄ := by
  sorry

-- Coq: `pow_lt` — 0 < e → 0 < e^n
noncomputable def pow_lt_check (e : ℝ) (n : Nat) : Id Unit :=
  pure ()

theorem pow_lt (e : ℝ) (n : Nat) :
    ⦃⌜0 < e⌝⦄
    pow_lt_check e n
    ⦃⇓_ => ⌜0 < e ^ n⌝⦄ := by
  sorry

-- Coq: `Rlt_pow_R1` — 1 < e → 0 < n → 1 < e^n
noncomputable def Rlt_pow_R1_check (e : ℝ) (n : Nat) : Id Unit :=
  pure ()

theorem Rlt_pow_R1 (e : ℝ) (n : Nat) :
    ⦃⌜1 < e ∧ 0 < n⌝⦄
    Rlt_pow_R1_check e n
    ⦃⇓_ => ⌜1 < e ^ n⌝⦄ := by
  sorry

-- Coq: `Rlt_pow` — 1 < e → n < m → e^n < e^m
noncomputable def Rlt_pow_check (e : ℝ) (n m : Nat) : Id Unit :=
  pure ()

theorem Rlt_pow (e : ℝ) (n m : Nat) :
    ⦃⌜1 < e ∧ n < m⌝⦄
    Rlt_pow_check e n m
    ⦃⇓_ => ⌜e ^ n < e ^ m⌝⦄ := by
  sorry

-- Coq: `pow_R1` — r^n = 1 → |r| = 1 ∨ n = 0
noncomputable def pow_R1_check (r : ℝ) (n : Nat) : Id Unit :=
  pure ()

theorem pow_R1 (r : ℝ) (n : Nat) :
    ⦃⌜r ^ n = 1⌝⦄
    pow_R1_check r n
    ⦃⇓_ => ⌜|r| = 1 ∨ n = 0⌝⦄ := by
  sorry

-- Coq: `powerRZ_O` — e^0 = 1 (integer exponent)
noncomputable def powerRZ_O_check (e : ℝ) : Id Unit :=
  pure ()

theorem powerRZ_O (e : ℝ) :
    ⦃⌜True⌝⦄
    powerRZ_O_check e
    ⦃⇓_ => ⌜e ^ (0 : Int) = (1 : ℝ)⌝⦄ := by
  sorry

-- Coq: `Zpower_NR0` — 0 ≤ e → 0 ≤ e^n (as integer power on Int)
noncomputable def Zpower_NR0_check (e : Int) (n : Nat) : Id Unit :=
  pure ()

theorem Zpower_NR0 (e : Int) (n : Nat) :
    ⦃⌜0 ≤ e⌝⦄
    Zpower_NR0_check e n
    ⦃⇓_ => ⌜0 ≤ (e : Int) ^ n⌝⦄ := by
  sorry

-- Coq: `Zpower_NR1` — 1 ≤ e → 1 ≤ e^n (as integer power on Int)
noncomputable def Zpower_NR1_check (e : Int) (n : Nat) : Id Unit :=
  pure ()

theorem Zpower_NR1 (e : Int) (n : Nat) :
    ⦃⌜1 ≤ e⌝⦄
    Zpower_NR1_check e n
    ⦃⇓_ => ⌜1 ≤ (e : Int) ^ n⌝⦄ := by
  sorry

-- Coq: `powerRZ_1` — e^1 = e (integer exponent)
noncomputable def powerRZ_1_check (e : ℝ) : Id Unit :=
  pure ()

theorem powerRZ_1 (e : ℝ) :
    ⦃⌜True⌝⦄
    powerRZ_1_check e
    ⦃⇓_ => ⌜e ^ (1 : Int) = e⌝⦄ := by
  sorry

-- Coq: `powerRZ_add` — e^(m+n) = e^m * e^n (integer exponent)
noncomputable def powerRZ_add_check (e : ℝ) (m n : Int) : Id Unit :=
  pure ()

theorem powerRZ_add (e : ℝ) (m n : Int) :
    ⦃⌜True⌝⦄
    powerRZ_add_check e m n
    ⦃⇓_ => ⌜e ^ (m + n) = e ^ m * e ^ n⌝⦄ := by
  sorry

-- Coq: `Rledouble` — if 0 ≤ r then r ≤ 2r
noncomputable def Rledouble_check (r : ℝ) : Id Unit :=
  pure ()

theorem Rledouble (r : ℝ) :
    ⦃⌜0 ≤ r⌝⦄
    Rledouble_check r
    ⦃⇓_ => ⌜r ≤ 2 * r⌝⦄ := by
  sorry

-- Coq: `Rltdouble` — if 0 < r then r < 2r
noncomputable def Rltdouble_check (r : ℝ) : Id Unit :=
  pure ()

theorem Rltdouble (r : ℝ) :
    ⦃⌜0 < r⌝⦄
    Rltdouble_check r
    ⦃⇓_ => ⌜r < 2 * r⌝⦄ := by
  sorry

-- Coq: `powerRZ_NOR` — e^n ≠ 0 when e ≠ 0 (integer exponent)
noncomputable def powerRZ_NOR_check (e : ℝ) (n : Int) : Id Unit :=
  pure ()

theorem powerRZ_NOR (e : ℝ) (n : Int) :
    ⦃⌜e ≠ 0⌝⦄
    powerRZ_NOR_check e n
    ⦃⇓_ => ⌜e ^ n ≠ 0⌝⦄ := by
  sorry

-- Coq: `Rle_Rinv` — monotonicity of inverse on (0, ∞)
noncomputable def Rle_Rinv_check (x y : ℝ) : Id Unit :=
  pure ()

theorem Rle_Rinv (x y : ℝ) :
    ⦃⌜0 < x ∧ x ≤ y⌝⦄
    Rle_Rinv_check x y
    ⦃⇓_ => ⌜y⁻¹ ≤ x⁻¹⌝⦄ := by
  sorry

-- Hoare-style wrapper for `min_or`
noncomputable def min_or_check (n m : Nat) : Id Unit :=
  pure ()

theorem min_or (n m : Nat) :
    ⦃⌜True⌝⦄
    min_or_check n m
    ⦃⇓_ => ⌜(Nat.min n m = n ∧ n ≤ m) ∨ (Nat.min n m = m ∧ m < n)⌝⦄ := by
  sorry

-- Coq: `ZmaxSym` — symmetry of integer max
noncomputable def ZmaxSym_check (a b : Int) : Id Unit :=
  pure ()

theorem ZmaxSym (a b : Int) :
    ⦃⌜True⌝⦄
    ZmaxSym_check a b
    ⦃⇓_ => ⌜max a b = max b a⌝⦄ := by
  sorry

-- Coq: `ZmaxLe1` — left argument ≤ max
noncomputable def ZmaxLe1_check (a b : Int) : Id Unit :=
  pure ()

theorem ZmaxLe1 (a b : Int) :
    ⦃⌜True⌝⦄
    ZmaxLe1_check a b
    ⦃⇓_ => ⌜a ≤ max a b⌝⦄ := by
  sorry

-- Coq: `ZmaxLe2` — right argument ≤ max
noncomputable def ZmaxLe2_check (a b : Int) : Id Unit :=
  pure ()

theorem ZmaxLe2 (a b : Int) :
    ⦃⌜True⌝⦄
    ZmaxLe2_check a b
    ⦃⇓_ => ⌜b ≤ max a b⌝⦄ := by
  sorry

noncomputable def ZleLe_check (x y : Nat) : Id Unit :=
  pure ()

theorem ZleLe (x y : Nat) :
    ⦃⌜(Int.ofNat x ≤ Int.ofNat y)⌝⦄
    ZleLe_check x y
    ⦃⇓_ => ⌜x ≤ y⌝⦄ := by
  sorry

-- Coq: `Zlt_Zopp` — negate flips strict inequality
noncomputable def Zlt_Zopp_check (x y : Int) : Id Unit :=
  pure ()

theorem Zlt_Zopp (x y : Int) :
    ⦃⌜x < y⌝⦄
    Zlt_Zopp_check x y
    ⦃⇓_ => ⌜-y < -x⌝⦄ := by
  sorry

-- Coq: `Zle_Zopp` — negate flips non-strict inequality
noncomputable def Zle_Zopp_check (x y : Int) : Id Unit :=
  pure ()

theorem Zle_Zopp (x y : Int) :
    ⦃⌜x ≤ y⌝⦄
    Zle_Zopp_check x y
    ⦃⇓_ => ⌜-y ≤ -x⌝⦄ := by
  sorry

-- Coq: `Zabs_absolu` — absolute value equals natAbs cast
noncomputable def Zabs_absolu_check (z : Int) : Id Unit :=
  pure ()

theorem Zabs_absolu (z : Int) :
    ⦃⌜True⌝⦄
    Zabs_absolu_check z
    ⦃⇓_ => ⌜|z| = Int.ofNat (Int.natAbs z)⌝⦄ := by
  sorry

-- Coq: `Zpower_nat_O` — any base to 0 is 1
noncomputable def Zpower_nat_O_check (z : Int) : Id Unit :=
  pure ()

theorem Zpower_nat_O (z : Int) :
    ⦃⌜True⌝⦄
    Zpower_nat_O_check z
    ⦃⇓_ => ⌜z^0 = (1 : Int)⌝⦄ := by
  sorry

-- Coq: `Zpower_nat_1` — any base to 1 is itself
noncomputable def Zpower_nat_1_check (z : Int) : Id Unit :=
  pure ()

theorem Zpower_nat_1 (z : Int) :
    ⦃⌜True⌝⦄
    Zpower_nat_1_check z
    ⦃⇓_ => ⌜z^1 = z⌝⦄ := by
  sorry

-- Coq: `Zmin_Zmax` — min is always ≤ max
noncomputable def Zmin_Zmax_check (z1 z2 : Int) : Id Unit :=
  pure ()

theorem Zmin_Zmax (z1 z2 : Int) :
    ⦃⌜True⌝⦄
    Zmin_Zmax_check z1 z2
    ⦃⇓_ => ⌜min z1 z2 ≤ max z1 z2⌝⦄ := by
  sorry

-- Coq: `Zeq_Zs` — if p ≤ q < succ p, then p = q
noncomputable def Zeq_Zs_check (p q : Int) : Id Unit :=
  pure ()

theorem Zeq_Zs (p q : Int) :
    ⦃⌜p ≤ q ∧ q < Int.succ p⌝⦄
    Zeq_Zs_check p q
    ⦃⇓_ => ⌜p = q⌝⦄ := by
  sorry

-- Coq: `Zopp_Zpred_Zs` — negation distributes over predecessor/successor
noncomputable def Zopp_Zpred_Zs_check (z : Int) : Id Unit :=
  pure ()

theorem Zopp_Zpred_Zs (z : Int) :
    ⦃⌜True⌝⦄
    Zopp_Zpred_Zs_check z
    ⦃⇓_ => ⌜-(Int.pred z) = Int.succ (-z)⌝⦄ := by
  sorry

-- Coq: `Zmin_Zle` — lower bound is ≤ minimum of two bounds
noncomputable def Zmin_Zle_check (z1 z2 z3 : Int) : Id Unit :=
  pure ()

theorem Zmin_Zle (z1 z2 z3 : Int) :
    ⦃⌜z1 ≤ z2 ∧ z1 ≤ z3⌝⦄
    Zmin_Zle_check z1 z2 z3
    ⦃⇓_ => ⌜z1 ≤ min z2 z3⌝⦄ := by
  sorry

-- Coq: `Zpred_Zopp_Zs` — predecessor of negation equals negation of successor
noncomputable def Zpred_Zopp_Zs_check (z : Int) : Id Unit :=
  pure ()

theorem Zpred_Zopp_Zs (z : Int) :
    ⦃⌜True⌝⦄
    Zpred_Zopp_Zs_check z
    ⦃⇓_ => ⌜Int.pred (-z) = -(Int.succ z)⌝⦄ := by
  sorry

-- Coq: `Zle_Zmult_comp_r` — multiply on the right preserves ≤ for nonnegative multiplier
noncomputable def Zle_Zmult_comp_r_check (x y z : Int) : Id Unit :=
  pure ()

theorem Zle_Zmult_comp_r (x y z : Int) :
    ⦃⌜0 ≤ z ∧ x ≤ y⌝⦄
    Zle_Zmult_comp_r_check x y z
    ⦃⇓_ => ⌜x * z ≤ y * z⌝⦄ := by
  sorry

-- Coq: `Zle_Zmult_comp_l` — multiply on the left preserves ≤ for nonnegative multiplier
noncomputable def Zle_Zmult_comp_l_check (x y z : Int) : Id Unit :=
  pure ()

theorem Zle_Zmult_comp_l (x y z : Int) :
    ⦃⌜0 ≤ z ∧ x ≤ y⌝⦄
    Zle_Zmult_comp_l_check x y z
    ⦃⇓_ => ⌜z * x ≤ z * y⌝⦄ := by
  sorry

-- Coq: `absolu_Zs` — natAbs of succ increments under nonnegativity
noncomputable def absolu_Zs_check (z : Int) : Id Unit :=
  pure ()

theorem absolu_Zs (z : Int) :
    ⦃⌜0 ≤ z⌝⦄
    absolu_Zs_check z
    ⦃⇓_ => ⌜Int.natAbs (Int.succ z) = Nat.succ (Int.natAbs z)⌝⦄ := by
  sorry

-- Coq: `Zlt_next` — either m = succ n or succ n < m when n < m
noncomputable def Zlt_next_check (n m : Int) : Id Unit :=
  pure ()

theorem Zlt_next (n m : Int) :
    ⦃⌜n < m⌝⦄
    Zlt_next_check n m
    ⦃⇓_ => ⌜m = Int.succ n ∨ Int.succ n < m⌝⦄ := by
  sorry

-- Coq: `Zle_next` — either m = n or succ n ≤ m when n ≤ m
noncomputable def Zle_next_check (n m : Int) : Id Unit :=
  pure ()

theorem Zle_next (n m : Int) :
    ⦃⌜n ≤ m⌝⦄
    Zle_next_check n m
    ⦃⇓_ => ⌜m = n ∨ Int.succ n ≤ m⌝⦄ := by
  sorry

-- Coq: `inj_pred` — Z_of_nat (pred n) = Z.pred (Z_of_nat n) for n ≠ 0
noncomputable def inj_pred_check (n : Nat) : Id Unit :=
  pure ()

theorem inj_pred (n : Nat) :
    ⦃⌜n ≠ 0⌝⦄
    inj_pred_check n
    ⦃⇓_ => ⌜Int.ofNat (Nat.pred n) = Int.pred (Int.ofNat n)⌝⦄ := by
  sorry

-- Coq: `Zle_abs` — p ≤ Z_of_nat (Z.abs_nat p)
noncomputable def Zle_abs_check (p : Int) : Id Unit :=
  pure ()

theorem Zle_abs (p : Int) :
    ⦃⌜True⌝⦄
    Zle_abs_check p
    ⦃⇓_ => ⌜p ≤ Int.ofNat (Int.natAbs p)⌝⦄ := by
  sorry

-- Coq: `inj_abs` — if 0 ≤ x then Z_of_nat (Z.abs_nat x) = x
noncomputable def inj_abs_check (x : Int) : Id Unit :=
  pure ()

theorem inj_abs (x : Int) :
    ⦃⌜0 ≤ x⌝⦄
    inj_abs_check x
    ⦃⇓_ => ⌜Int.ofNat (Int.natAbs x) = x⌝⦄ := by
  sorry

-- Coq `positive` compatibility and `nat_of_P`
structure Positive where
  val : Nat

noncomputable def nat_of_P (p : Positive) : Nat :=
  p.val.succ

-- Coq: `inject_nat_convert` — if p = Zpos q then Z_of_nat (nat_of_P q) = p
noncomputable def inject_nat_convert_check (p : Int) (q : Positive) : Id Unit :=
  pure ()

theorem inject_nat_convert (p : Int) (q : Positive) :
    ⦃⌜p = Int.ofNat (nat_of_P q)⌝⦄
    inject_nat_convert_check p q
    ⦃⇓_ => ⌜Int.ofNat (nat_of_P q) = p⌝⦄ := by
  -- Trivial restatement in Lean; Coq version states for Zpos q.
  sorry

-- Coq: `Zabs_eq_opp` — if x ≤ 0 then |x| = -x
noncomputable def Zabs_eq_opp_check (x : Int) : Id Unit :=
  pure ()

theorem Zabs_eq_opp (x : Int) :
    ⦃⌜x ≤ 0⌝⦄
    Zabs_eq_opp_check x
    ⦃⇓_ => ⌜|x| = -x⌝⦄ := by
  sorry

-- Coq: `Zabs_Zs` — |succ z| ≤ succ |z|
noncomputable def Zabs_Zs_check (z : Int) : Id Unit :=
  pure ()

theorem Zabs_Zs (z : Int) :
    ⦃⌜True⌝⦄
    Zabs_Zs_check z
    ⦃⇓_ => ⌜|Int.succ z| ≤ Int.succ |z|⌝⦄ := by
  sorry

-- Coq: `lt_Zlt_inv` — if Z_of_nat n < Z_of_nat m then n < m
noncomputable def lt_Zlt_inv_check (n m : Nat) : Id Unit :=
  pure ()

theorem lt_Zlt_inv (n m : Nat) :
    ⦃⌜Int.ofNat n < Int.ofNat m⌝⦄
    lt_Zlt_inv_check n m
    ⦃⇓_ => ⌜n < m⌝⦄ := by
  sorry

-- Coq: `Zle_Zpred` — if x < y then x ≤ pred y
noncomputable def Zle_Zpred_check (x y : Int) : Id Unit :=
  pure ()

theorem Zle_Zpred (x y : Int) :
    ⦃⌜x < y⌝⦄
    Zle_Zpred_check x y
    ⦃⇓_ => ⌜x ≤ Int.pred y⌝⦄ := by
  sorry

-- Coq: `NconvertO` — nat_of_P p <> 0 for positive p
noncomputable def NconvertO_check (p : Positive) : Id Unit :=
  pure ()

theorem NconvertO (p : Positive) :
    ⦃⌜True⌝⦄
    NconvertO_check p
    ⦃⇓_ => ⌜nat_of_P p ≠ 0⌝⦄ := by
  sorry

-- Coq: `convert_not_O` — nat_of_P p <> 0 for positive p (alias of NconvertO)
noncomputable def convert_not_O_check (p : Positive) : Id Unit :=
  pure ()

theorem convert_not_O (p : Positive) :
    ⦃⌜True⌝⦄
    convert_not_O_check p
    ⦃⇓_ => ⌜nat_of_P p ≠ 0⌝⦄ := by
  -- Mirrors `NconvertO`; proof deferred per import task.
  sorry

-- Coq: `Zle_Zabs` — z ≤ |z|
noncomputable def Zle_Zabs_check (z : Int) : Id Unit :=
  pure ()

theorem Zle_Zabs (z : Int) :
    ⦃⌜True⌝⦄
    Zle_Zabs_check z
    ⦃⇓_ => ⌜z ≤ |z|⌝⦄ := by
  sorry

-- We declare the `_check` and theorem later after `pff_to_flocq` is defined.

-- Coq: `absolu_lt_nz` — if z ≠ 0 then 0 < Z.abs_nat z
noncomputable def absolu_lt_nz_check (z : Int) : Id Unit :=
  pure ()

theorem absolu_lt_nz (z : Int) :
    ⦃⌜z ≠ 0⌝⦄
    absolu_lt_nz_check z
    ⦃⇓_ => ⌜0 < Int.natAbs z⌝⦄ := by
  sorry

-- List operations used in Pff
def list_sum (l : List ℝ) : ℝ :=
  l.foldr (· + ·) 0

def list_prod (l : List ℝ) : ℝ :=
  l.foldr (· * ·) 1

-- Legacy floating-point format compatibility
structure PffFloat where
  mantissa : Int
  exponent : Int
  sign : Bool

-- Conversion between Pff and Flocq formats
def pff_to_flocq (beta : Int) (f : PffFloat) : FloatSpec.Core.Defs.FlocqFloat beta :=
  FloatSpec.Core.Defs.FlocqFloat.mk (if f.sign then -f.mantissa else f.mantissa) f.exponent

def flocq_to_pff {beta : Int} (f : FloatSpec.Core.Defs.FlocqFloat beta) : PffFloat :=
  { mantissa := Int.natAbs f.Fnum,
    exponent := f.Fexp,
    sign := f.Fnum < 0 }

-- Coq: `Fle_Zle` — compare two floats of same exponent by their mantissas
-- We mirror the Coq statement Fle_Zle: n1 ≤ n2 → Fle (Float n1 d) (Float n2 d)
-- Our Pff compatibility struct `PffFloat` uses fields (mantissa, exponent, sign).
-- We state an analogous lemma at the level of reals via `F2R ∘ pff_to_flocq`.
noncomputable def Fle_Zle_check (beta : Int) (n1 n2 d : Int) : Id Unit :=
  pure ()

theorem Fle_Zle (beta : Int) (n1 n2 d : Int) :
    ⦃⌜n1 ≤ n2⌝⦄
    Fle_Zle_check beta n1 n2 d
    ⦃⇓_ => ⌜_root_.F2R (pff_to_flocq beta { mantissa := n1, exponent := d, sign := false })
            ≤ _root_.F2R (pff_to_flocq beta { mantissa := n2, exponent := d, sign := false })⌝⦄ := by
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

-- Coq: `Zlt_mult_simpl_l` — cancel positive multiplier on left for <
noncomputable def Zlt_mult_simpl_l_check (a b c : Int) : Id Unit :=
  pure ()

theorem Zlt_mult_simpl_l (a b c : Int) :
    ⦃⌜0 < c ∧ c * a < c * b⌝⦄
    Zlt_mult_simpl_l_check a b c
    ⦃⇓_ => ⌜a < b⌝⦄ := by
  sorry

-- Coq: `Z_eq_bool_correct` — boolean equality correctness for Int
noncomputable def Z_eq_bool (p q : Int) : Bool := decide (p = q)

noncomputable def Z_eq_bool_correct_check (p q : Int) : Id Unit :=
  pure ()

theorem Z_eq_bool_correct (p q : Int) :
    ⦃⌜True⌝⦄
    Z_eq_bool_correct_check p q
    ⦃⇓_ => ⌜(if Z_eq_bool p q then p = q else p ≠ q)⌝⦄ := by
  sorry

-- Coq: `Zcompare_correct` — trichotomy via a comparison function
noncomputable def Zcompare (p q : Int) : Ordering :=
  if p < q then Ordering.lt else if p = q then Ordering.eq else Ordering.gt

noncomputable def Zcompare_correct_check (p q : Int) : Id Unit :=
  pure ()

theorem Zcompare_correct (p q : Int) :
    ⦃⌜True⌝⦄
    Zcompare_correct_check p q
    ⦃⇓_ => ⌜match Zcompare p q with
            | Ordering.gt => q < p
            | Ordering.lt => p < q
            | Ordering.eq => p = q⌝⦄ := by
  sorry

-- Coq: `Zabs_Zopp` — | -z | = | z |
noncomputable def Zabs_Zopp_check (z : Int) : Id Unit :=
  pure ()

theorem Zabs_Zopp (z : Int) :
    ⦃⌜True⌝⦄
    Zabs_Zopp_check z
    ⦃⇓_ => ⌜|-z| = |z|⌝⦄ := by
  sorry

-- Coq: `Zle_Zpred_Zpred` — predecessor is monotone
noncomputable def Zle_Zpred_Zpred_check (z1 z2 : Int) : Id Unit :=
  pure ()

theorem Zle_Zpred_Zpred (z1 z2 : Int) :
    ⦃⌜z1 ≤ z2⌝⦄
    Zle_Zpred_Zpred_check z1 z2
    ⦃⇓_ => ⌜Int.pred z1 ≤ Int.pred z2⌝⦄ := by
  sorry

-- Coq: `Zle_n_Zpred` — cancel pred on both sides for ≤
noncomputable def Zle_n_Zpred_check (z1 z2 : Int) : Id Unit :=
  pure ()

theorem Zle_n_Zpred (z1 z2 : Int) :
    ⦃⌜Int.pred z1 ≤ Int.pred z2⌝⦄
    Zle_n_Zpred_check z1 z2
    ⦃⇓_ => ⌜z1 ≤ z2⌝⦄ := by
  sorry

-- Coq: `Zlt_1_O` — 1 ≤ z → 0 < z
noncomputable def Zlt_1_O_check (z : Int) : Id Unit :=
  pure ()

theorem Zlt_1_O (z : Int) :
    ⦃⌜1 ≤ z⌝⦄
    Zlt_1_O_check z
    ⦃⇓_ => ⌜0 < z⌝⦄ := by
  sorry

-- Coq: `Zlt_Zabs_inv1` — |z1| < z2 → -z2 < z1
noncomputable def Zlt_Zabs_inv1_check (z1 z2 : Int) : Id Unit :=
  pure ()

theorem Zlt_Zabs_inv1 (z1 z2 : Int) :
    ⦃⌜|z1| < z2⌝⦄
    Zlt_Zabs_inv1_check z1 z2
    ⦃⇓_ => ⌜-z2 < z1⌝⦄ := by
  sorry

-- Coq: `Zle_Zabs_inv1` — |z1| ≤ z2 → -z2 ≤ z1
noncomputable def Zle_Zabs_inv1_check (z1 z2 : Int) : Id Unit :=
  pure ()

theorem Zle_Zabs_inv1 (z1 z2 : Int) :
    ⦃⌜|z1| ≤ z2⌝⦄
    Zle_Zabs_inv1_check z1 z2
    ⦃⇓_ => ⌜-z2 ≤ z1⌝⦄ := by
  sorry

-- Coq: `Zle_Zabs_inv2` — |z1| ≤ z2 → z1 ≤ z2
noncomputable def Zle_Zabs_inv2_check (z1 z2 : Int) : Id Unit :=
  pure ()

theorem Zle_Zabs_inv2 (z1 z2 : Int) :
    ⦃⌜|z1| ≤ z2⌝⦄
    Zle_Zabs_inv2_check z1 z2
    ⦃⇓_ => ⌜z1 ≤ z2⌝⦄ := by
  sorry

-- Coq: `Zlt_Zabs_Zpred` — if |z1| < z2 and z1 ≠ pred z2 then |succ z1| < z2
noncomputable def Zlt_Zabs_Zpred_check (z1 z2 : Int) : Id Unit :=
  pure ()

theorem Zlt_Zabs_Zpred (z1 z2 : Int) :
    ⦃⌜|z1| < z2 ∧ z1 ≠ Int.pred z2⌝⦄
    Zlt_Zabs_Zpred_check z1 z2
    ⦃⇓_ => ⌜|Int.succ z1| < z2⌝⦄ := by
  sorry

-- Coq: `EvenO` — Even 0
noncomputable def EvenO_check : Id Unit :=
  pure ()

theorem EvenO :
    ⦃⌜True⌝⦄
    EvenO_check
    ⦃⇓_ => ⌜Even (0 : Int)⌝⦄ := by
  sorry

-- Coq: `Zlt_not_eq_rev` — if q < p then p ≠ q
noncomputable def Zlt_not_eq_rev_check (p q : Int) : Id Unit :=
  pure ()

theorem Zlt_not_eq_rev (p q : Int) :
    ⦃⌜q < p⌝⦄
    Zlt_not_eq_rev_check p q
    ⦃⇓_ => ⌜p ≠ q⌝⦄ := by
  sorry

-- Coq: `Zle_Zpred_inv` — if z1 ≤ pred z2 then z1 < z2
noncomputable def Zle_Zpred_inv_check (z1 z2 : Int) : Id Unit :=
  pure ()

theorem Zle_Zpred_inv (z1 z2 : Int) :
    ⦃⌜z1 ≤ Int.pred z2⌝⦄
    Zle_Zpred_inv_check z1 z2
    ⦃⇓_ => ⌜z1 < z2⌝⦄ := by
  sorry

-- Coq: `Zabs_intro` — if `P` holds for `-z` and `z`, it holds for `|z|`
noncomputable def Zabs_intro_check (P : Int → Prop) (z : Int) : Id Unit :=
  pure ()

theorem Zabs_intro (P : Int → Prop) (z : Int) :
    ⦃⌜P (-z) ∧ P z⌝⦄
    Zabs_intro_check P z
    ⦃⇓_ => ⌜P (|z|)⌝⦄ := by
  sorry

-- Coq: `Zpred_Zle_Zabs_intro` — if -pred z2 ≤ z1 ≤ pred z2 then |z1| < z2
noncomputable def Zpred_Zle_Zabs_intro_check (z1 z2 : Int) : Id Unit :=
  pure ()

theorem Zpred_Zle_Zabs_intro (z1 z2 : Int) :
    ⦃⌜-Int.pred z2 ≤ z1 ∧ z1 ≤ Int.pred z2⌝⦄
    Zpred_Zle_Zabs_intro_check z1 z2
    ⦃⇓_ => ⌜|z1| < z2⌝⦄ := by
  sorry

-- Coq: `Zlt_Zabs_intro` — if -z2 < z1 < z2 then |z1| < z2
noncomputable def Zlt_Zabs_intro_check (z1 z2 : Int) : Id Unit :=
  pure ()

theorem Zlt_Zabs_intro (z1 z2 : Int) :
    ⦃⌜-z2 < z1 ∧ z1 < z2⌝⦄
    Zlt_Zabs_intro_check z1 z2
    ⦃⇓_ => ⌜|z1| < z2⌝⦄ := by
  sorry

-- Coq: `Zpower_nat_less` — for q > 0, Zpower_nat n q > 0
noncomputable def Zpower_nat_less_check (n : Int) (q : Nat) : Id Unit :=
  pure ()

theorem Zpower_nat_less (n : Int) (q : Nat) :
    ⦃⌜0 < q⌝⦄
    Zpower_nat_less_check n q
    ⦃⇓_ => ⌜0 < n ^ q⌝⦄ := by
  sorry

-- Coq: `Zpower_nat_monotone_S` — n^(q+1) ≥ n^q for n ≥ 1
noncomputable def Zpower_nat_monotone_S_check (n : Int) (q : Nat) : Id Unit :=
  pure ()

theorem Zpower_nat_monotone_S (n : Int) (q : Nat) :
    ⦃⌜1 ≤ n⌝⦄
    Zpower_nat_monotone_S_check n q
    ⦃⇓_ => ⌜n ^ q ≤ n ^ (q+1)⌝⦄ := by
  sorry

-- Coq: `Zpower_nat_monotone_lt` — if 1 < n then n^q < n^(q+1)
noncomputable def Zpower_nat_monotone_lt_check (n : Int) (q : Nat) : Id Unit :=
  pure ()

theorem Zpower_nat_monotone_lt (n : Int) (q : Nat) :
    ⦃⌜1 < n⌝⦄
    Zpower_nat_monotone_lt_check n q
    ⦃⇓_ => ⌜n ^ q < n ^ (q+1)⌝⦄ := by
  sorry

-- Coq: `Zpower_nat_anti_monotone_lt` — if 0 ≤ n < 1 then n^(q+1) < n^q
noncomputable def Zpower_nat_anti_monotone_lt_check (n : Int) (q : Nat) : Id Unit :=
  pure ()

theorem Zpower_nat_anti_monotone_lt (n : Int) (q : Nat) :
    ⦃⌜0 ≤ n ∧ n < 1⌝⦄
    Zpower_nat_anti_monotone_lt_check n q
    ⦃⇓_ => ⌜n ^ (q+1) < n ^ q⌝⦄ := by
  sorry

-- Coq: `Zpower_nat_monotone_le` — if 1 ≤ n then n^q ≤ n^r for q ≤ r
noncomputable def Zpower_nat_monotone_le_check (n : Int) (q r : Nat) : Id Unit :=
  pure ()

theorem Zpower_nat_monotone_le (n : Int) (q r : Nat) :
    ⦃⌜1 ≤ n ∧ q ≤ r⌝⦄
    Zpower_nat_monotone_le_check n q r
    ⦃⇓_ => ⌜n ^ q ≤ n ^ r⌝⦄ := by
  sorry

-- Alias for Coq's Zpower_nat on integers
noncomputable def Zpower_nat (n : Int) (q : Nat) : Int := n ^ q

-- Coq: `digitAux1` — (Zpower_nat n (S p) * r) = (Zpower_nat n p * (n * r))
noncomputable def digitAux1_check (n : Int) (p : Nat) (r : Int) : Id Unit :=
  pure ()

theorem digitAux1 (n : Int) (p : Nat) (r : Int) :
    ⦃⌜True⌝⦄
    digitAux1_check n p r
    ⦃⇓_ => ⌜Zpower_nat n (Nat.succ p) * r = Zpower_nat n p * (n * r)⌝⦄ := by
  sorry

-- Minimal positive and digit infrastructure used by digit lemmas
-- Reuse existing `Positive` defined above; define a placeholder `digitAux`.
noncomputable def digitAux (n v r : Int) (q : Positive) : Nat := 0

-- Coq: `digitAuxLess`
noncomputable def digitAuxLess_check (n : Int) (v r : Int) (q : Positive) : Id Unit :=
  pure ()

theorem digitAuxLess (n : Int) (v r : Int) (q : Positive) :
    ⦃⌜True⌝⦄
    digitAuxLess_check n v r q
    ⦃⇓_ => ⌜match digitAux n v r q with
            | Nat.succ r' => Zpower_nat n r' * r ≤ v
            | 0 => True⌝⦄ := by
  sorry

-- Coq: `digitLess` — if q ≠ 0 then Zpower_nat n (pred (digit q)) ≤ |q|
noncomputable def digitLess_check (n : Int) (q : Int) : Id Unit :=
  pure ()

noncomputable def digit (n : Int) (q : Int) : Nat :=
  match q with
  | Int.ofNat _ => 0
  | Int.negSucc _ => 0

theorem digitLess (n : Int) (q : Int) :
    ⦃⌜q ≠ 0⌝⦄
    digitLess_check n q
    ⦃⇓_ => ⌜Zpower_nat n (Nat.pred (digit n q)) ≤ |q|⌝⦄ := by
  sorry

-- Length of a positive number in base-2 (placeholder)
noncomputable def pos_length (p : Positive) : Nat := 0

-- Coq: `pos_length_pow` — Zpos p < Zpower_nat n (S (pos_length p))
noncomputable def pos_length_pow_check (n : Int) (p : Positive) : Id Unit :=
  pure ()

theorem pos_length_pow (n : Int) (p : Positive) :
    ⦃⌜True⌝⦄
    pos_length_pow_check n p
    ⦃⇓_ => ⌜Int.ofNat (nat_of_P p) < Zpower_nat n (Nat.succ (pos_length p))⌝⦄ := by
  sorry

-- Coq: `digitMore` — |q| < Zpower_nat n (digit q)
noncomputable def digitMore_check (n : Int) (q : Int) : Id Unit :=
  pure ()

theorem digitMore (n : Int) (q : Int) :
    ⦃⌜True⌝⦄
    digitMore_check n q
    ⦃⇓_ => ⌜|q| < Zpower_nat n (digit n q)⌝⦄ := by
  sorry

-- Coq: `digitAuxMore` — complementary case for digit auxiliary
noncomputable def digitAuxMore_check (n : Int) (v r : Int) (p : Positive) : Id Unit :=
  pure ()

theorem digitAuxMore (n : Int) (v r : Int) (p : Positive) :
    ⦃⌜True⌝⦄
    digitAuxMore_check n v r p
    ⦃⇓_ => ⌜match digitAux n v r p with
            | Nat.succ r' => v < Zpower_nat n r' * r
            | 0 => True⌝⦄ := by
  sorry

-- Coq: `digitInv` — if n^(pred r) ≤ |q| < n^r then digit n q = r
noncomputable def digitInv_check (n : Int) (q : Int) (r : Nat) : Id Unit :=
  pure ()

theorem digitInv (n : Int) (q : Int) (r : Nat) :
    ⦃⌜Zpower_nat n (Nat.pred r) ≤ |q| ∧ |q| < Zpower_nat n r⌝⦄
    digitInv_check n q r
    ⦃⇓_ => ⌜digit n q = r⌝⦄ := by
  sorry
