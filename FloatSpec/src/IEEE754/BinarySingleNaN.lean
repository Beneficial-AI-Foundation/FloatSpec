-- Binary single NaN operations
-- Translated from Coq file: flocq/src/IEEE754/BinarySingleNaN.v

import FloatSpec.src.IEEE754.Binary
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import Std.Do.Triple
import Std.Tactic.Do
import Mathlib.Data.Real.Basic

open Real
open Std.Do

variable (prec emax : Int)
variable [Prec_gt_0 prec]
variable [Prec_lt_emax prec emax]

-- Binary float with single NaN representation
inductive B754 where
  | B754_zero (s : Bool) : B754
  | B754_infinity (s : Bool) : B754
  | B754_nan : B754
  | B754_finite (s : Bool) (m : Nat) (e : Int) : B754

-- Conversion to real number
noncomputable def B754_to_R (x : B754) : ℝ :=
  match x with
  | B754.B754_finite s m e => 
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk (if s then -(m : Int) else (m : Int)) e : FloatSpec.Core.Defs.FlocqFloat 2)
  | _ => 0

-- Bridge from Binary754 to single-NaN binary (Coq: B2BSN)
def B2BSN {prec emax} (x : Binary754 prec emax) : B754 :=
  match x.val with
  | FullFloat.F754_finite s m e => B754.B754_finite s m e
  | FullFloat.F754_infinity s => B754.B754_infinity s
  | FullFloat.F754_zero s => B754.B754_zero s
  | FullFloat.F754_nan _ _ => B754.B754_nan

-- View a single-NaN binary into the standard IEEE 754 float
def B2SF_BSN (x : B754) : StandardFloat :=
  match x with
  | B754.B754_finite s m e => StandardFloat.S754_finite s m e
  | B754.B754_infinity s => StandardFloat.S754_infinity s
  | B754.B754_zero s => StandardFloat.S754_zero s
  | B754.B754_nan => StandardFloat.S754_nan

-- Bridge from StandardFloat to BinarySingleNaN (Coq: SF2B)
def SF2B (x : StandardFloat) : B754 :=
  match x with
  | StandardFloat.S754_finite s m e => B754.B754_finite s m e
  | StandardFloat.S754_infinity s => B754.B754_infinity s
  | StandardFloat.S754_zero s => B754.B754_zero s
  | StandardFloat.S754_nan => B754.B754_nan

-- Coq: match_SF2B — pattern match through SF2B corresponds to match on source
def match_SF2B_check {T : Type}
  (fz : Bool → T) (fi : Bool → T) (fn : T) (ff : Bool → Nat → Int → T)
  (x : StandardFloat) : Id T :=
  pure <|
    match x with
    | StandardFloat.S754_zero sx => fz sx
    | StandardFloat.S754_infinity sx => fi sx
    | StandardFloat.S754_nan => fn
    | StandardFloat.S754_finite sx mx ex => ff sx mx ex

theorem match_SF2B {T : Type}
  (fz : Bool → T) (fi : Bool → T) (fn : T) (ff : Bool → Nat → Int → T)
  (x : StandardFloat) :
  ⦃⌜True⌝⦄
  match_SF2B_check fz fi fn ff x
  ⦃⇓result => ⌜result =
      (match SF2B x with
       | B754.B754_zero sx => fz sx
       | B754.B754_infinity sx => fi sx
       | B754.B754_nan => fn
       | B754.B754_finite sx mx ex => ff sx mx ex)⌝⦄ := by
  intro _
  unfold match_SF2B_check SF2B
  cases x <;> rfl

-- Coq: B2SF_SF2B — standard view after SF2B is identity
def B2SF_SF2B_check (x : StandardFloat) : Id StandardFloat :=
  pure (B2SF_BSN (SF2B x))

theorem B2SF_SF2B (x : StandardFloat) :
  ⦃⌜True⌝⦄
  B2SF_SF2B_check x
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  -- Follows by cases on x; mirroring Coq's SF2B/B2SF roundtrip.
  exact sorry

-- Finite/NaN/sign classifiers on the BinarySingleNaN side
def BSN_is_finite (x : B754) : Bool :=
  match x with
  | B754.B754_finite _ _ _ => true
  | B754.B754_zero _ => true
  | _ => false

def BSN_is_nan (x : B754) : Bool :=
  match x with
  | B754.B754_nan => true
  | _ => false

def BSN_sign (x : B754) : Bool :=
  match x with
  | B754.B754_zero s => s
  | B754.B754_infinity s => s
  | B754.B754_finite s _ _ => s
  | B754.B754_nan => false

-- Strict finiteness on StandardFloat (true iff finite, not considering zeros specially)
def is_finite_strict_SF (x : StandardFloat) : Bool :=
  match x with
  | StandardFloat.S754_finite _ _ _ => true
  | _ => false

-- Coq: B2SF_B2BSN — standard view commutes with bridge to single-NaN
def B2SF_B2BSN_check {prec emax} (x : Binary754 prec emax) : Id StandardFloat :=
  pure (B2SF_BSN (B2BSN (prec:=prec) (emax:=emax) x))

theorem B2SF_B2BSN {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  B2SF_B2BSN_check (prec:=prec) (emax:=emax) x
  ⦃⇓result => ⌜result = B2SF (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  exact sorry

-- Coq: is_finite_B2BSN — finiteness preserved by the bridge
def is_finite_B2BSN_check {prec emax} (x : Binary754 prec emax) : Id Bool :=
  pure (BSN_is_finite (B2BSN (prec:=prec) (emax:=emax) x))

theorem is_finite_B2BSN {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  is_finite_B2BSN_check (prec:=prec) (emax:=emax) x
  ⦃⇓result => ⌜result = is_finite_B (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  exact sorry

-- Strict finiteness (finite-but-not-zero) classifiers, used for missing Coq theorems.
def BSN_is_finite_strict (x : B754) : Bool :=
  match x with
  | B754.B754_finite _ _ _ => true
  | _ => false

def is_finite_strict_B {prec emax} (x : Binary754 prec emax) : Bool :=
  match x.val with
  | FullFloat.F754_finite _ _ _ => true
  | _ => false

-- Coq: is_finite_strict_B2BSN — strict finiteness preserved by the bridge
def is_finite_strict_B2BSN_check {prec emax} (x : Binary754 prec emax) : Id Bool :=
  pure (BSN_is_finite_strict (B2BSN (prec:=prec) (emax:=emax) x))

theorem is_finite_strict_B2BSN {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  is_finite_strict_B2BSN_check (prec:=prec) (emax:=emax) x
  ⦃⇓result => ⌜result = is_finite_strict_B (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  -- Proof deferred; follows by cases on `x.val`.
  exact sorry

-- Coq: is_nan_B2BSN — NaN preserved by the bridge
def is_nan_B2BSN_check {prec emax} (x : Binary754 prec emax) : Id Bool :=
  pure (BSN_is_nan (B2BSN (prec:=prec) (emax:=emax) x))

theorem is_nan_B2BSN {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  is_nan_B2BSN_check (prec:=prec) (emax:=emax) x
  ⦃⇓result => ⌜result = is_nan_B (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  exact sorry

-- Coq: Bsign_B2BSN — sign preserved by the bridge
def Bsign_B2BSN_check {prec emax} (x : Binary754 prec emax) : Id Bool :=
  pure (BSN_sign (B2BSN (prec:=prec) (emax:=emax) x))

theorem Bsign_B2BSN {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  Bsign_B2BSN_check (prec:=prec) (emax:=emax) x
  ⦃⇓result => ⌜result = Bsign (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  exact sorry

-- Coq: B2R_B2BSN — real semantics commutes with bridge to single-NaN
noncomputable def B2R_B2BSN_check {prec emax} (x : Binary754 prec emax) : Id ℝ :=
  pure (B754_to_R (B2BSN (prec:=prec) (emax:=emax) x))

theorem B2R_B2BSN {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  B2R_B2BSN_check (prec:=prec) (emax:=emax) x
  ⦃⇓result => ⌜result = B2R (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  exact sorry

-- Coq: is_finite_strict_B2R — nonzero real semantics implies strict finiteness
-- Stated for the single-NaN binary `B754` using `B754_to_R` as semantics.
def is_finite_strict_B2R_check (x : B754) : Id Bool :=
  pure (BSN_is_finite_strict x)

theorem is_finite_strict_B2R (x : B754)
  (h : B754_to_R x ≠ 0) :
  ⦃⌜True⌝⦄
  is_finite_strict_B2R_check x
  ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  -- Proof deferred; by cases on `x` and using `h` to exclude zero cases.
  exact sorry

-- Coq: SF2R_B2SF — Real semantics after mapping to StandardFloat
-- We state it in hoare-triple style around a pure computation.
noncomputable def SF2R_B2SF_check (x : B754) : Id ℝ :=
  pure (SF2R 2 (B2SF_BSN x))

theorem SF2R_B2SF (x : B754) :
  ⦃⌜True⌝⦄
  SF2R_B2SF_check x
  ⦃⇓result => ⌜result = B754_to_R x⌝⦄ := by
  intro _
  -- Structure follows the hoare-triple pattern used in this project.
  -- Proof deferred.
  exact sorry

-- Coq: SF2B_B2SF — roundtrip from B2SF back to B754 via SF2B
def SF2B_B2SF_check (x : B754) : Id B754 :=
  pure (SF2B (B2SF_BSN x))

theorem SF2B_B2SF (x : B754) :
  ⦃⌜True⌝⦄
  SF2B_B2SF_check x
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  -- By cases on x; definitionally equal.
  exact sorry

-- Coq: valid_binary_B2SF — validity of `B2SF` image
def valid_binary_B2SF_check {prec emax : Int} (x : B754) : Id Bool :=
  pure (valid_binary_SF (prec:=prec) (emax:=emax) (B2SF_BSN x))

theorem valid_binary_B2SF {prec emax} (x : B754) :
  ⦃⌜True⌝⦄
  valid_binary_B2SF_check (prec:=prec) (emax:=emax) x
  ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  -- Holds by the current definition of valid_binary_SF.
  unfold valid_binary_B2SF_check
  rfl

-- Coq: SF2B_B2SF_valid — roundtrip with validity argument
def SF2B_B2SF_valid_check (x : B754) : Id B754 :=
  pure (SF2B (B2SF_BSN x))

theorem SF2B_B2SF_valid (x : B754) :
  ⦃⌜True⌝⦄
  SF2B_B2SF_valid_check x
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  -- Same computation as SF2B_B2SF.
  unfold SF2B_B2SF_valid_check
  -- Proof deferred.
  exact sorry

-- Coq: is_finite_strict_SF2B — strict finiteness preserved by SF2B
def is_finite_strict_SF2B_check (x : StandardFloat) : Id Bool :=
  pure (BSN_is_finite_strict (SF2B x))

theorem is_finite_strict_SF2B (x : StandardFloat) :
  ⦃⌜True⌝⦄
  is_finite_strict_SF2B_check x
  ⦃⇓result => ⌜result = is_finite_strict_SF x⌝⦄ := by
  intro _
  -- Proof deferred; by cases on x.
  exact sorry

-- Coq: B2SF_inj — injectivity of B2SF on non-NaN values
theorem B2SF_inj (x y : B754)
  (hx : BSN_is_nan x = false)
  (hy : BSN_is_nan y = false)
  (h : B2SF_BSN x = B2SF_BSN y) : x = y := by
  -- Proof by cases on x and y; NaN excluded by hypotheses.
  exact sorry

-- Bridge back from single-NaN view to FullFloat (Coq: BSN2B)
def BSN2B (s : Bool) (payload : Nat) (x : B754) : FullFloat :=
  match x with
  | B754.B754_nan => FullFloat.F754_nan s payload
  | B754.B754_zero b => FullFloat.F754_zero b
  | B754.B754_infinity b => FullFloat.F754_infinity b
  | B754.B754_finite b m e => FullFloat.F754_finite b m e

-- A variant of the bridge that requires a non-NaN witness, mirroring Coq's `BSN2B'`.
-- For non-NaN inputs, it returns the corresponding `FullFloat` without needing a NaN payload.
def BSN2B' (x : B754) (nx : BSN_is_nan x = false) : FullFloat :=
  match x with
  | B754.B754_zero b => FullFloat.F754_zero b
  | B754.B754_infinity b => FullFloat.F754_infinity b
  | B754.B754_finite b m e => FullFloat.F754_finite b m e
  | B754.B754_nan => nomatch nx

-- Coq: B2BSN_BSN2B — roundtrip through the bridge
def B2BSN_BSN2B_check {prec emax : Int} (s : Bool) (payload : Nat) (x : B754) : Id B754 :=
  pure (B2BSN (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) (BSN2B s payload x)))

theorem B2BSN_BSN2B {prec emax : Int} (s : Bool) (payload : Nat) (x : B754) :
  ⦃⌜True⌝⦄
  B2BSN_BSN2B_check (prec:=prec) (emax:=emax) s payload x
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  unfold B2BSN_BSN2B_check BSN2B B2BSN FF2B
  cases x <;> rfl

-- Coq: Bsign_BSN2B — sign preserved by BSN2B on non-NaN values
def Bsign_BSN2B_check (s : Bool) (payload : Nat) (x : B754) : Id Bool :=
  pure (sign_FF (BSN2B s payload x))

theorem Bsign_BSN2B (s : Bool) (payload : Nat) (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  Bsign_BSN2B_check s payload x
  ⦃⇓result => ⌜result = BSN_sign x⌝⦄ := by
  intro _
  -- Proof deferred; by cases on x using nx to exclude NaN case
  exact sorry

-- A lifting combinator mirroring Coq's `lift` (Binary.v)
-- If `x` is NaN, return `x`; otherwise, rebuild a full float from `y`.
def lift (x : FullFloat) (y : B754)
  (Ny : BSN_is_nan y = is_nan_FF x) : FullFloat :=
  match h:is_nan_FF x with
  | true => x
  | false => BSN2B' y (by simpa [h] using Ny)

-- Coq: B2BSN_lift — viewing the lifted value back to BSN yields `y`
def B2BSN_lift_check {prec emax : Int}
  (x : FullFloat) (y : B754)
  (Ny : BSN_is_nan y = is_nan_FF x) : Id B754 :=
  pure (B2BSN (prec:=prec) (emax:=emax)
          (FF2B (prec:=prec) (emax:=emax)
            (lift x y Ny)))

theorem B2BSN_lift {prec emax : Int}
  (x : FullFloat) (y : B754)
  (Ny : BSN_is_nan y = is_nan_FF x) :
  ⦃⌜True⌝⦄
  B2BSN_lift_check (prec:=prec) (emax:=emax) x y Ny
  ⦃⇓result => ⌜result = y⌝⦄ := by
  intro _
  -- Proof deferred; follows Coq's `B2BSN_lift` by cases on `is_nan_FF x`.
  exact sorry

-- Coq: B2BSN_BSN2B' — roundtrip through the non-NaN bridge
def B2BSN_BSN2B'_check {prec emax : Int} (x : B754)
  (nx : BSN_is_nan x = false) : Id B754 :=
  pure (B2BSN (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) (BSN2B' x nx)))

theorem B2BSN_BSN2B' {prec emax : Int} (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  B2BSN_BSN2B'_check (prec:=prec) (emax:=emax) x nx
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  unfold B2BSN_BSN2B'_check BSN2B' B2BSN FF2B
  cases x <;> simp [BSN_is_nan] at nx <;> rfl

-- Coq: B2R_BSN2B' — real semantics preserved through BSN2B' on non-NaN values
noncomputable def B2R_BSN2B'_check (x : B754)
  (nx : BSN_is_nan x = false) : Id ℝ :=
  pure (FF2R 2 (BSN2B' x nx))

theorem B2R_BSN2B' (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  B2R_BSN2B'_check x nx
  ⦃⇓result => ⌜result = B754_to_R x⌝⦄ := by
  intro _
  unfold B2R_BSN2B'_check BSN2B'
  cases x <;> simp [B754_to_R, BSN_is_nan] at nx <;> rfl

-- Coq: B2FF_BSN2B' — standard full-float view after BSN2B'
def B2FF_BSN2B'_check {prec emax : Int} (x : B754)
  (nx : BSN_is_nan x = false) : Id FullFloat :=
  pure (B2FF (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) (BSN2B' x nx)))

theorem B2FF_BSN2B' {prec emax : Int} (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  B2FF_BSN2B'_check (prec:=prec) (emax:=emax) x nx
  ⦃⇓result => ⌜result = SF2FF (B2SF_BSN x)⌝⦄ := by
  intro _
  unfold B2FF_BSN2B'_check BSN2B' B2SF_BSN
  cases x <;> simp [BSN_is_nan] at nx <;> rfl

-- Coq: Bsign_BSN2B' — sign preserved through BSN2B' on non-NaN values
def Bsign_BSN2B'_check (x : B754)
  (nx : BSN_is_nan x = false) : Id Bool :=
  pure (sign_FF (BSN2B' x nx))

theorem Bsign_BSN2B' (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  Bsign_BSN2B'_check x nx
  ⦃⇓result => ⌜result = BSN_sign x⌝⦄ := by
  intro _
  unfold Bsign_BSN2B'_check BSN2B'
  cases x <;> simp [BSN_is_nan, BSN_sign] at nx <;> rfl

-- Coq: is_finite_BSN2B' — finiteness preserved through BSN2B'
def is_finite_BSN2B'_check (x : B754)
  (nx : BSN_is_nan x = false) : Id Bool :=
  pure (is_finite_FF (BSN2B' x nx))

theorem is_finite_BSN2B' (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  is_finite_BSN2B'_check x nx
  ⦃⇓result => ⌜result = BSN_is_finite x⌝⦄ := by
  intro _
  unfold is_finite_BSN2B'_check BSN2B'
  cases x <;> simp [BSN_is_nan, BSN_is_finite] at nx <;> rfl

-- Coq: is_nan_BSN2B' — NaN predicate preserved through BSN2B' (trivially false)
def is_nan_BSN2B'_check (x : B754)
  (nx : BSN_is_nan x = false) : Id Bool :=
  pure (is_nan_FF (BSN2B' x nx))

theorem is_nan_BSN2B' (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  is_nan_BSN2B'_check x nx
  ⦃⇓result => ⌜result = BSN_is_nan x⌝⦄ := by
  intro _
  unfold is_nan_BSN2B'_check BSN2B'
  cases x <;> simp [BSN_is_nan] at nx <;> rfl

-- Coq: B2R_BSN2B — real semantics preserved through BSN2B
noncomputable def B2R_BSN2B_check (s : Bool) (payload : Nat) (x : B754) : Id ℝ :=
  pure (FF2R 2 (BSN2B s payload x))

theorem B2R_BSN2B (s : Bool) (payload : Nat) (x : B754) :
  ⦃⌜True⌝⦄
  B2R_BSN2B_check s payload x
  ⦃⇓result => ⌜result = B754_to_R x⌝⦄ := by
  intro _
  -- Proof follows by cases on x; deferred.
  exact sorry

-- Coq: B2R_SF2B — real semantics after SF2B equals SF2R of source
noncomputable def B2R_SF2B_check (x : StandardFloat) : Id ℝ :=
  pure (B754_to_R (SF2B x))

theorem B2R_SF2B (x : StandardFloat) :
  ⦃⌜True⌝⦄
  B2R_SF2B_check x
  ⦃⇓result => ⌜result = SF2R 2 x⌝⦄ := by
  intro _
  -- Case split on x; follows definitions.
  exact sorry

-- Coq: is_finite_BSN2B — finiteness preserved through BSN2B
def is_finite_BSN2B_check (s : Bool) (payload : Nat) (x : B754) : Id Bool :=
  pure (is_finite_FF (BSN2B s payload x))

theorem is_finite_BSN2B (s : Bool) (payload : Nat) (x : B754) :
  ⦃⌜True⌝⦄
  is_finite_BSN2B_check s payload x
  ⦃⇓result => ⌜result = BSN_is_finite x⌝⦄ := by
  intro _
  -- Proof by cases on x; deferred.
  exact sorry

-- Coq: is_nan_BSN2B — NaN preserved through BSN2B
def is_nan_BSN2B_check (s : Bool) (payload : Nat) (x : B754) : Id Bool :=
  pure (is_nan_FF (BSN2B s payload x))

theorem is_nan_BSN2B (s : Bool) (payload : Nat) (x : B754) :
  ⦃⌜True⌝⦄
  is_nan_BSN2B_check s payload x
  ⦃⇓result => ⌜result = BSN_is_nan x⌝⦄ := by
  intro _
  -- Proof by cases on x; deferred.
  exact sorry

-- Valid B754 predicate
def validB754 (x : B754) : Prop :=
  match x with
  | B754.B754_finite s m e => 
    -- Mantissa in range and exponent constraints
    (1 ≤ m : Prop) ∧ (m < 2^(Int.natAbs (prec - 1) : Nat) : Prop) ∧
    (3 - emax - prec ≤ e : Prop) ∧ (e ≤ emax - prec : Prop)
  | _ => True

-- Operations preserving single NaN
def B754_plus (mode : RoundingMode) (x y : B754) : B754 := by
  sorry

def B754_mult (mode : RoundingMode) (x y : B754) : B754 := by
  sorry

def B754_div (mode : RoundingMode) (x y : B754) : B754 := by
  sorry

def B754_sqrt (mode : RoundingMode) (x : B754) : B754 := by
  sorry

-- Classification functions
def B754_is_finite (x : B754) : Bool :=
  match x with
  | B754.B754_finite _ _ _ => true
  | B754.B754_zero _ => true
  | _ => false

def B754_is_nan (x : B754) : Bool :=
  match x with
  | B754.B754_nan => true
  | _ => false

def B754_sign (x : B754) : Bool :=
  match x with
  | B754.B754_zero s => s
  | B754.B754_infinity s => s
  | B754.B754_finite s _ _ => s
  | B754.B754_nan => false

-- Correctness of operations
theorem B754_plus_correct (mode : RoundingMode) (x y : B754)
  (hx : True)
  (hy : True) :
  True ∧
  (¬B754_is_nan (B754_plus mode x y) → 
   B754_to_R (B754_plus mode x y) = 
   FloatSpec.Calc.Round.round 2 (FLT_exp (3 - emax - prec) prec) () 
     (B754_to_R x + B754_to_R y)) := by
  sorry

theorem B754_mult_correct (mode : RoundingMode) (x y : B754)
  (hx : True)
  (hy : True) :
  True ∧
  (¬B754_is_nan (B754_mult mode x y) → 
   B754_to_R (B754_mult mode x y) = 
   FloatSpec.Calc.Round.round 2 (FLT_exp (3 - emax - prec) prec) () 
     (B754_to_R x * B754_to_R y)) := by
  sorry
