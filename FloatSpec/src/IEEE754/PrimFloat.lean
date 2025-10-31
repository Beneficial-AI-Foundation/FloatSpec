-- Primitive floating-point operations
-- Translated from Coq file: flocq/src/IEEE754/PrimFloat.v

import FloatSpec.src.IEEE754.Binary
import FloatSpec.src.IEEE754.Bits
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Classical
open Std.Do

-- Primitive float type placeholder (use real numbers for compilation)
abbrev PrimFloat := ℝ

-- Operations on primitive floats
def prim_add (x y : PrimFloat) : PrimFloat := x + y
def prim_sub (x y : PrimFloat) : PrimFloat := x - y
def prim_mul (x y : PrimFloat) : PrimFloat := x * y
noncomputable def prim_div (x y : PrimFloat) : PrimFloat := x / y
noncomputable def prim_sqrt (x : PrimFloat) : PrimFloat := Real.sqrt x

-- Comparison operations
noncomputable def prim_eq (x y : PrimFloat) : Bool := decide (x = y)
noncomputable def prim_lt (x y : PrimFloat) : Bool := decide (x < y)
noncomputable def prim_le (x y : PrimFloat) : Bool := decide (x ≤ y)

-- Classification functions
noncomputable def prim_is_zero (x : PrimFloat) : Bool := decide (x = 0)
def prim_is_finite (_x : PrimFloat) : Bool := true
def prim_is_nan (_x : PrimFloat) : Bool := false
def prim_is_infinite (_x : PrimFloat) : Bool := false

-- Special values
def prim_zero : PrimFloat := 0
def prim_infinity : PrimFloat := 0
def prim_nan : PrimFloat := 0

-- Sign operations
def prim_neg (x : PrimFloat) : PrimFloat := -x
def prim_abs (x : PrimFloat) : PrimFloat := |x|
noncomputable def prim_sign (x : PrimFloat) : Bool := decide (x < 0)

-- Conversion between Binary754 and PrimFloat
def binary_to_prim (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) : PrimFloat := by
  sorry

def prim_to_binary (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Binary754 prec emax := by
  sorry

-- Bridge view: StandardFloat image of a PrimFloat via Binary754
noncomputable def Prim2SF (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : StandardFloat :=
  B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x)

-- Correctness theorems
theorem prim_add_correct (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) :
  binary_to_prim prec emax ((binary_add (prec:=prec) (emax:=emax) x y)) = 
  prim_add (binary_to_prim prec emax x) (binary_to_prim prec emax y) := by
  sorry

theorem prim_mul_correct (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) :
  binary_to_prim prec emax ((binary_mul (prec:=prec) (emax:=emax) x y)) = 
  prim_mul (binary_to_prim prec emax x) (binary_to_prim prec emax y) := by
  sorry

-- Coq: B2SF_Prim2B — standard view after Prim→Binary equals Prim2SF
def B2SF_Prim2B_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Id StandardFloat :=
  pure (B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x))

theorem B2SF_Prim2B (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  B2SF_Prim2B_check prec emax x
  ⦃⇓result => ⌜result = Prim2SF prec emax x⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `B2SF_Prim2B` round-trip property.
  exact sorry

-- Coq: Prim2SF_B2Prim — standard view of Binary→Prim equals direct B2SF
noncomputable def Prim2SF_B2Prim_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) : Id StandardFloat :=
  pure (Prim2SF prec emax (binary_to_prim prec emax x))

theorem Prim2SF_B2Prim (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  Prim2SF_B2Prim_check prec emax x
  ⦃⇓result => ⌜result = B2SF (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `Prim2SF_B2Prim` lemma.
  exact sorry

-- Coq: compare_equiv — comparison correspondence between PrimFloat and Binary754
noncomputable def prim_compare (x y : PrimFloat) : Option Int :=
  some ((FloatSpec.Core.Raux.Rcompare x y).run)

noncomputable def compare_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : Id (Option Int) :=
  pure (prim_compare x y)

theorem compare_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  compare_equiv_check prec emax x y
  ⦃⇓result => ⌜result =
      (Bcompare_check (prec:=prec) (emax:=emax)
        (prim_to_binary prec emax x) (prim_to_binary prec emax y))⌝⦄ := by
  intro _
  -- Proof deferred; follows Coq's `compare_equiv` via `B2SF`/`SF2B` bridges.
  exact sorry

-- Coq: B2Prim_Prim2B — roundtrip Prim → Binary → Prim
def B2Prim_Prim2B_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Id PrimFloat :=
  pure (binary_to_prim prec emax (prim_to_binary prec emax x))

theorem B2Prim_Prim2B (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  B2Prim_Prim2B_check prec emax x
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  -- Proof deferred; relies on intended equivalence between Prim and Binary.
  exact sorry

-- Coq: opp_equiv — negation correspondence between PrimFloat and Binary754
def opp_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Id FullFloat :=
  pure (B2FF (prim_to_binary prec emax (prim_neg x)))

theorem opp_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  opp_equiv_check prec emax x
  ⦃⇓result => ⌜result = Bopp (B2FF (prim_to_binary prec emax x))⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `opp_equiv` using bridge lemmas.
  exact sorry

-- Coq: Prim2B_B2Prim — roundtrip Binary → Prim → Binary
def Prim2B_B2Prim_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) : Id (Binary754 prec emax) :=
  pure (prim_to_binary prec emax (binary_to_prim prec emax x))

theorem Prim2B_B2Prim (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  Prim2B_B2Prim_check prec emax x
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  -- Proof deferred; relies on intended equivalence between Prim and Binary.
  exact sorry

-- Coq: Prim2B_inj — injectivity of Prim→Binary conversion
def Prim2B_inj_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : Id Unit :=
  pure ()

theorem Prim2B_inj (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat)
  (h : prim_to_binary prec emax x = prim_to_binary prec emax y) :
  ⦃⌜True⌝⦄
  Prim2B_inj_check prec emax x y
  ⦃⇓_ => ⌜x = y⌝⦄ := by
  intro _
  -- Proof deferred; follows Coq's Prim2B_inj using roundtrip lemmas.
  exact sorry

-- Coq: B2Prim_inj — injectivity of Binary→Prim conversion
def B2Prim_inj_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Id Unit :=
  pure ()

theorem B2Prim_inj (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax)
  (h : binary_to_prim prec emax x = binary_to_prim prec emax y) :
  ⦃⌜True⌝⦄
  B2Prim_inj_check prec emax x y
  ⦃⇓_ => ⌜x = y⌝⦄ := by
  intro _
  -- Proof deferred; follows Coq's B2Prim_inj using roundtrip lemmas.
  exact sorry

-- Coq: abs_equiv — absolute-value correspondence between PrimFloat and Binary754
def abs_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Id FullFloat :=
  pure (B2FF (prim_to_binary prec emax (prim_abs x)))

theorem abs_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  abs_equiv_check prec emax x
  ⦃⇓result => ⌜result = Babs (B2FF (prim_to_binary prec emax x))⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `abs_equiv` using bridge lemmas.
  exact sorry

-- Coq: div_equiv — division correspondence between PrimFloat and Flocq Binary
noncomputable def div_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : Id FullFloat :=
  pure (B2FF (prim_to_binary prec emax (prim_div x y)))

theorem div_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  div_equiv_check prec emax x y
  ⦃⇓result => ⌜result =
      B2FF (binary_div (prec:=prec) (emax:=emax)
              (prim_to_binary prec emax x)
              (prim_to_binary prec emax y))⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `div_equiv` via SingleNaN bridge.
  exact sorry

-- Coq: sub_equiv — subtraction correspondence between PrimFloat and Flocq Binary
def sub_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : Id FullFloat :=
  pure (B2FF (prim_to_binary prec emax (prim_sub x y)))

theorem sub_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  sub_equiv_check prec emax x y
  ⦃⇓result => ⌜result =
      B2FF (binary_sub (prec:=prec) (emax:=emax)
              (prim_to_binary prec emax x)
              (prim_to_binary prec emax y))⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `sub_equiv` via SingleNaN bridge.
  exact sorry

-- Coq: sqrt_equiv — square-root correspondence between PrimFloat and Flocq Binary
noncomputable def sqrt_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Id FullFloat :=
  pure (B2FF (prim_to_binary prec emax (prim_sqrt x)))

theorem sqrt_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  sqrt_equiv_check prec emax x
  ⦃⇓result => ⌜result =
      B2FF (binary_sqrt (prec:=prec) (emax:=emax)
              (prim_to_binary prec emax x))⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `sqrt_equiv` via SingleNaN bridge.
  exact sorry

-- Coq: infinity_equiv — primitive +∞ corresponds to Binary infinity
noncomputable def infinity_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax] : Id PrimFloat :=
  pure (binary_to_prim prec emax (FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_infinity false)))

theorem infinity_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
  ⦃⌜True⌝⦄
  infinity_equiv_check prec emax
  ⦃⇓result => ⌜result = prim_infinity⌝⦄ := by
  intro _
  -- Proof deferred; follows from the intended semantics of `binary_to_prim` and constants.
  exact sorry

-- Coq: neg_infinity_equiv — primitive −∞ corresponds to Binary −∞
noncomputable def neg_infinity_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax] : Id PrimFloat :=
  pure (binary_to_prim prec emax (FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_infinity true)))

theorem neg_infinity_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
  ⦃⌜True⌝⦄
  neg_infinity_equiv_check prec emax
  ⦃⇓result => ⌜result = prim_infinity⌝⦄ := by
  intro _
  -- Proof deferred; follows from the intended semantics of `binary_to_prim` and constants.
  exact sorry

-- Coq: nan_equiv — primitive NaN corresponds to Binary NaN
noncomputable def nan_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax] : Id PrimFloat :=
  pure (binary_to_prim prec emax (FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_nan false 1)))

theorem nan_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
  ⦃⌜True⌝⦄
  nan_equiv_check prec emax
  ⦃⇓result => ⌜result = prim_nan⌝⦄ := by
  intro _
  -- Proof deferred; follows from the intended semantics of constants.
  exact sorry

-- Coq: zero_equiv — primitive +0 corresponds to Binary zero
noncomputable def zero_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax] : Id PrimFloat :=
  pure (binary_to_prim prec emax (FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_zero false)))

theorem zero_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
  ⦃⌜True⌝⦄
  zero_equiv_check prec emax
  ⦃⇓result => ⌜result = prim_zero⌝⦄ := by
  intro _
  -- Proof deferred; follows from the intended semantics.
  exact sorry

-- Coq: neg_zero_equiv — primitive −0 corresponds to Binary −0
noncomputable def neg_zero_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax] : Id PrimFloat :=
  pure (binary_to_prim prec emax (FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_zero true)))

theorem neg_zero_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
  ⦃⌜True⌝⦄
  neg_zero_equiv_check prec emax
  ⦃⇓result => ⌜result = prim_zero⌝⦄ := by
  intro _
  -- Proof deferred; follows from the intended semantics.
  exact sorry

-- Coq: one_equiv — primitive one corresponds to Binary constant one
noncomputable def one_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax] : Id PrimFloat :=
  pure (binary_to_prim prec emax (binary_one (prec:=prec) (emax:=emax)))

theorem one_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
  ⦃⌜True⌝⦄
  one_equiv_check prec emax
  ⦃⇓result => ⌜result = 1⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `one_equiv`.
  exact sorry

-- Coq: two_equiv — primitive two corresponds to Binary plus one one
noncomputable def two_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax] : Id PrimFloat :=
  pure (binary_to_prim prec emax
          (binary_add (prec:=prec) (emax:=emax)
            (binary_one (prec:=prec) (emax:=emax))
            (binary_one (prec:=prec) (emax:=emax))))

theorem two_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
  ⦃⌜True⌝⦄
  two_equiv_check prec emax
  ⦃⇓result => ⌜result = 2⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `two_equiv`.
  exact sorry

-- Coq: is_nan_equiv — NaN classifier correspondence
noncomputable def is_nan_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Id Bool :=
  pure (prim_is_nan x)

theorem is_nan_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  is_nan_equiv_check prec emax x
  ⦃⇓result => ⌜result = is_nan_B (prec:=prec) (emax:=emax) (prim_to_binary prec emax x)⌝⦄ := by
  intro _
  -- Proof deferred; follows via `B2SF_Prim2B` cases.
  exact sorry

-- Coq: is_zero_equiv — zero classifier correspondence
noncomputable def is_zero_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Id Bool :=
  pure (prim_is_zero x)

theorem is_zero_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  is_zero_equiv_check prec emax x
  ⦃⇓result => ⌜result = decide (B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x) = StandardFloat.S754_zero false ∨
                                   B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x) = StandardFloat.S754_zero true)⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's zero predicate equivalence.
  exact sorry

-- Coq: of_int63_equiv — integer conversion equivalence
noncomputable def of_int63_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (z : Int) : Id PrimFloat :=
  pure (z)

theorem of_int63_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (z : Int) :
  ⦃⌜True⌝⦄
  of_int63_equiv_check prec emax z
  ⦃⇓result => ⌜result =
      binary_to_prim prec emax (prim_to_binary prec emax (z))⌝⦄ := by
  intro _
  -- Proof deferred; corresponds to Coq's `of_int63_equiv` through conversions.
  exact sorry

-- Coq: is_infinity_equiv — infinity classifier correspondence
noncomputable def is_infinity_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Id Bool :=
  pure (prim_is_infinite x)

theorem is_infinity_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  is_infinity_equiv_check prec emax x
  ⦃⇓result => ⌜result = decide (∃ s, B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x) = StandardFloat.S754_infinity s)⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's infinity predicate equivalence.
  exact sorry

-- Coq: is_finite_equiv — finiteness classifier correspondence
noncomputable def is_finite_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Id Bool :=
  pure (prim_is_finite x)

theorem is_finite_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  is_finite_equiv_check prec emax x
  ⦃⇓result => ⌜result = is_finite_B (prec:=prec) (emax:=emax) (prim_to_binary prec emax x)⌝⦄ := by
  intro _
  -- Proof deferred; aligns with Coq's `is_finite_equiv`.
  exact sorry

-- Coq: get_sign_equiv — sign bit correspondence
noncomputable def get_sign_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Id Bool :=
  pure (prim_sign x)

theorem get_sign_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  get_sign_equiv_check prec emax x
  ⦃⇓result => ⌜result = Bsign (prec:=prec) (emax:=emax) (prim_to_binary prec emax x)⌝⦄ := by
  intro _
  -- Proof deferred; aligns with Coq's `get_sign_equiv` via `B2SF_Prim2B`.
  exact sorry

-- Binary-side boolean comparisons used in Coq's eqb/ltb/leb lemmas
noncomputable def Beqb (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Bool :=
  match B2SF (prec:=prec) (emax:=emax) x, B2SF (prec:=prec) (emax:=emax) y with
  | StandardFloat.S754_zero sx, StandardFloat.S754_zero sy => decide (sx = sy)
  | StandardFloat.S754_infinity sx, StandardFloat.S754_infinity sy => decide (sx = sy)
  | StandardFloat.S754_nan, StandardFloat.S754_nan => true
  | StandardFloat.S754_finite sx mx ex, StandardFloat.S754_finite sy my ey =>
      decide (sx = sy ∧ mx = my ∧ ex = ey)
  | _, _ => false

-- Coq: Beqb_correct — equality on binary numbers matches real equality under finiteness
noncomputable def Beqb_correct_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Id Bool :=
  pure (Beqb prec emax x y)

theorem Beqb_correct (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax)
  (hx : is_finite_B (prec:=prec) (emax:=emax) x = true)
  (hy : is_finite_B (prec:=prec) (emax:=emax) y = true) :
  ⦃⌜True⌝⦄
  Beqb_correct_check prec emax x y
  ⦃⇓result => ⌜result = decide (B2R (prec:=prec) (emax:=emax) x = B2R (prec:=prec) (emax:=emax) y)⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `Beqb_correct` via `Bcompare_correct`.
  exact sorry

noncomputable def Bcmp (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Int :=
  ((FloatSpec.Core.Raux.Rcompare (B2R (prec:=prec) (emax:=emax) x)
                                 (B2R (prec:=prec) (emax:=emax) y)).run)

noncomputable def Bltb (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Bool :=
  Bcmp prec emax x y = (-1)

noncomputable def Bleb (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Bool :=
  Bcmp prec emax x y ≠ 1

-- Coq: Beqb_refl — reflexivity of Beqb except NaN
noncomputable def Beqb_refl_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) : Id Bool :=
  pure (Beqb prec emax x x)

theorem Beqb_refl (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  Beqb_refl_check prec emax x
  ⦃⇓result => ⌜result = bnot (is_nan_B (prec:=prec) (emax:=emax) x)⌝⦄ := by
  intro _
  -- Proof deferred; follows Coq's `Beqb_refl` by case analysis.
  exact sorry

-- Coq: Bltb_correct — strict-ordered comparison matches real comparison
noncomputable def Bltb_correct_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Id Bool :=
  pure (Bltb prec emax x y)

theorem Bltb_correct (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax)
  (hx : is_finite_B (prec:=prec) (emax:=emax) x = true)
  (hy : is_finite_B (prec:=prec) (emax:=emax) y = true) :
  ⦃⌜True⌝⦄
  Bltb_correct_check prec emax x y
  ⦃⇓result => ⌜result = decide (B2R (prec:=prec) (emax:=emax) x < B2R (prec:=prec) (emax:=emax) y)⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `Bltb_correct` via `Bcompare_correct` and `Rcompare`.
  exact sorry

-- Coq: Bleb_correct — non-strict-ordered comparison matches real comparison
noncomputable def Bleb_correct_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Id Bool :=
  pure (Bleb prec emax x y)

theorem Bleb_correct (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax)
  (hx : is_finite_B (prec:=prec) (emax:=emax) x = true)
  (hy : is_finite_B (prec:=prec) (emax:=emax) y = true) :
  ⦃⌜True⌝⦄
  Bleb_correct_check prec emax x y
  ⦃⇓result => ⌜result = decide (B2R (prec:=prec) (emax:=emax) x ≤ B2R (prec:=prec) (emax:=emax) y)⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `Bleb_correct` via `Bcompare_correct` and `Rcompare`.
  exact sorry

-- Coq: eqb_equiv — boolean equality correspondence
noncomputable def eqb_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : Id Bool :=
  pure (prim_eq x y)

theorem eqb_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  eqb_equiv_check prec emax x y
  ⦃⇓result => ⌜result =
      Beqb prec emax (prim_to_binary prec emax x) (prim_to_binary prec emax y)⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `eqb_equiv` via `B2SF_Prim2B`.
  exact sorry

-- Coq: ltb_equiv — boolean strict ordering correspondence
noncomputable def ltb_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : Id Bool :=
  pure (prim_lt x y)

theorem ltb_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  ltb_equiv_check prec emax x y
  ⦃⇓result => ⌜result =
      Bltb prec emax (prim_to_binary prec emax x) (prim_to_binary prec emax y)⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `ltb_equiv` via `B2R` and `Rcompare`.
  exact sorry

-- Coq: leb_equiv — boolean non-strict ordering correspondence
noncomputable def leb_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : Id Bool :=
  pure (prim_le x y)

theorem leb_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  leb_equiv_check prec emax x y
  ⦃⇓result => ⌜result =
      Bleb prec emax (prim_to_binary prec emax x) (prim_to_binary prec emax y)⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `leb_equiv` via `B2R` and `Rcompare`.
  exact sorry
