-- IEEE-754 binary arithmetic
-- Translated from Coq file: flocq/src/IEEE754/Binary.v

import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do
import FloatSpec.src.SimprocWP

open Real
open Std.Do

-- Local boolean negation alias (to mirror Coq's `bnot`)
def bnot (b : Bool) : Bool := !b

-- IEEE 754 full float representation
inductive FullFloat where
  | F754_zero (s : Bool) : FullFloat
  | F754_infinity (s : Bool) : FullFloat
  | F754_nan (s : Bool) (m : Nat) : FullFloat
  | F754_finite (s : Bool) (m : Nat) (e : Int) : FullFloat

-- Standard float representation
inductive StandardFloat where
  | S754_zero (s : Bool) : StandardFloat
  | S754_infinity (s : Bool) : StandardFloat
  | S754_nan : StandardFloat
  | S754_finite (s : Bool) (m : Nat) (e : Int) : StandardFloat

-- Conversion from FullFloat to StandardFloat
def FF2SF (x : FullFloat) : StandardFloat :=
  match x with
  | FullFloat.F754_zero s => StandardFloat.S754_zero s
  | FullFloat.F754_infinity s => StandardFloat.S754_infinity s
  | FullFloat.F754_nan _ _ => StandardFloat.S754_nan
  | FullFloat.F754_finite s m e => StandardFloat.S754_finite s m e

-- Conversion from FullFloat to real number
noncomputable def FF2R (beta : Int) (x : FullFloat) : ℝ :=
  match x with
  | FullFloat.F754_finite s m e =>
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk (if s then -(m : Int) else (m : Int)) e : FloatSpec.Core.Defs.FlocqFloat beta)
  | _ => 0

-- Conversion from StandardFloat to real number
noncomputable def SF2R (beta : Int) (x : StandardFloat) : ℝ :=
  match x with
  | StandardFloat.S754_finite s m e =>
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk (if s then -(m : Int) else (m : Int)) e : FloatSpec.Core.Defs.FlocqFloat beta)
  | _ => 0

-- SF2R and FF2SF consistency
theorem SF2R_FF2SF (beta : Int) (x : FullFloat) :
  SF2R beta (FF2SF x) = FF2R beta x := by
  cases x <;> rfl

-- Conversion from StandardFloat to FullFloat
def SF2FF (x : StandardFloat) : FullFloat :=
  match x with
  | StandardFloat.S754_zero s => FullFloat.F754_zero s
  | StandardFloat.S754_infinity s => FullFloat.F754_infinity s
  | StandardFloat.S754_nan => FullFloat.F754_nan false 1
  | StandardFloat.S754_finite s m e => FullFloat.F754_finite s m e

-- Round-trip property
theorem FF2SF_SF2FF (x : StandardFloat) :
  FF2SF (SF2FF x) = x := by
  cases x <;> rfl

-- FF2R after SF2FF equals SF2R
theorem FF2R_SF2FF (beta : Int) (x : StandardFloat) :
  FF2R beta (SF2FF x) = SF2R beta x := by
  cases x <;> rfl

-- NaN detection for FullFloat
def is_nan_FF (f : FullFloat) : Bool :=
  match f with
  | FullFloat.F754_nan _ _ => true
  | _ => false

-- NaN detection for StandardFloat
def is_nan_SF (f : StandardFloat) : Bool :=
  match f with
  | StandardFloat.S754_nan => true
  | _ => false

-- Sign extraction for FullFloat
def sign_FF (x : FullFloat) : Bool :=
  match x with
  | FullFloat.F754_nan s _ => s
  | FullFloat.F754_zero s => s
  | FullFloat.F754_infinity s => s
  | FullFloat.F754_finite s _ _ => s

-- Finite check for FullFloat
def is_finite_FF (f : FullFloat) : Bool :=
  match f with
  | FullFloat.F754_finite _ _ _ => true
  | FullFloat.F754_zero _ => true
  | _ => false

-- NaN detection consistency
theorem is_nan_SF2FF (x : StandardFloat) :
  is_nan_FF (SF2FF x) = is_nan_SF x := by
  cases x <;> rfl

-- NaN detection consistency in the other direction
theorem is_nan_FF2SF (x : FullFloat) :
  is_nan_SF (FF2SF x) = is_nan_FF x := by
  cases x <;> rfl

-- Round-trip when not NaN (Coq: SF2FF_FF2SF)
theorem SF2FF_FF2SF (x : FullFloat)
  (hnotnan : is_nan_FF x = false) :
  SF2FF (FF2SF x) = x := by
  cases x <;> simp [FF2SF, SF2FF, is_nan_FF] at hnotnan ⊢

-- Build a NaN value (Coq: build_nan)
def build_nan (s : Bool) (payload : Nat) : FullFloat :=
  FullFloat.F754_nan s payload

-- Hoare wrapper for checking NaN-ness of build_nan
def is_nan_build_nan_check (s : Bool) (payload : Nat) : Bool :=
  (is_nan_FF (build_nan s payload))

-- Coq: is_nan_build_nan — building a NaN yields a NaN
theorem is_nan_build_nan (s : Bool) (payload : Nat) :
  ⦃⌜True⌝⦄
  is_nan_build_nan_check s payload
  ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold is_nan_build_nan_check build_nan is_nan_FF
  rfl

-- Real value of a freshly built NaN is zero (Coq: B2R_build_nan)
noncomputable def B2R_build_nan_check (s : Bool) (payload : Nat) : ℝ :=
  (FF2R 2 (build_nan s payload))

theorem B2R_build_nan (s : Bool) (payload : Nat) :
  ⦃⌜True⌝⦄
  B2R_build_nan_check s payload
  ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro _
  -- Follows from the definition of FF2R on non-finite values
  -- and the shape of build_nan.
  unfold B2R_build_nan_check build_nan FF2R
  rfl

-- Finiteness check of a freshly built NaN is false (Coq: is_finite_build_nan)
def is_finite_build_nan_check (s : Bool) (payload : Nat) : Bool :=
  (is_finite_FF (build_nan s payload))

theorem is_finite_build_nan (s : Bool) (payload : Nat) :
  ⦃⌜True⌝⦄
  is_finite_build_nan_check s payload
  ⦃⇓result => ⌜result = false⌝⦄ := by
  intro _
  unfold is_finite_build_nan_check build_nan is_finite_FF
  rfl

-- Extract a NaN payload (mirrors Coq `get_nan_pl`)
def get_nan_pl (x : FullFloat) : Nat :=
  match x with
  | FullFloat.F754_nan _ pl => pl
  | _ => 1

-- Hoare wrapper for Coq-style `build_nan_correct`
-- In Coq: for x with is_nan x = true, build_nan x = x
-- Here we rebuild a NaN from the sign and payload of `x` and assert equality.
def build_nan_correct_check (x : { f : FullFloat // is_nan_FF f = true }) : FullFloat :=
  (build_nan (sign_FF x.val) (get_nan_pl x.val))

theorem build_nan_correct (x : { f : FullFloat // is_nan_FF f = true }) :
  ⦃⌜True⌝⦄
  build_nan_correct_check x
  ⦃⇓result => ⌜result = x.val⌝⦄ := by
  intro _
  rcases x with ⟨f, hf⟩
  cases f <;>
    simp [build_nan_correct_check, build_nan, sign_FF, get_nan_pl, is_nan_FF] at hf ⊢

-- A no-op erasure on FullFloat (Coq: erase)
def erase (x : FullFloat) : FullFloat := x

def erase_check (x : FullFloat) : FullFloat :=
  (erase x)

theorem erase_correct (x : FullFloat) :
  ⦃⌜True⌝⦄
  erase_check x
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  unfold erase_check erase
  rfl

-- Opposite (negation) on FullFloat (Coq: Bopp)
def Bopp (x : FullFloat) : FullFloat :=
  match x with
  | FullFloat.F754_nan s pl => FullFloat.F754_nan (bnot s) pl
  | FullFloat.F754_infinity s => FullFloat.F754_infinity (bnot s)
  | FullFloat.F754_finite s m e => FullFloat.F754_finite (bnot s) m e
  | FullFloat.F754_zero s => FullFloat.F754_zero (bnot s)

def Bopp_involutive_check (x : FullFloat) : FullFloat :=
  (Bopp (Bopp x))

theorem Bopp_involutive (x : FullFloat)
  (hx : is_nan_FF x = false) :
  ⦃⌜True⌝⦄
  Bopp_involutive_check x
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  cases x <;> simp [Bopp_involutive_check, Bopp, bnot, is_nan_FF] at hx ⊢

noncomputable def B2R_Bopp_check (x : FullFloat) : ℝ :=
  (FF2R 2 (Bopp x))

theorem B2R_Bopp (x : FullFloat) :
  ⦃⌜True⌝⦄
  B2R_Bopp_check x
  ⦃⇓result => ⌜result = - FF2R 2 x⌝⦄ := by
  intro _
  cases x with
  | F754_zero s =>
      simp [B2R_Bopp_check, FF2R, Bopp]
  | F754_infinity s =>
      simp [B2R_Bopp_check, FF2R, Bopp]
  | F754_nan s m =>
      simp [B2R_Bopp_check, FF2R, Bopp]
  | F754_finite s m e =>
      simp [B2R_Bopp_check, FF2R, Bopp, bnot, F2R,
        FloatSpec.Core.Defs.F2R]
      cases s <;> simp [Id, Pure.pure]

def is_finite_Bopp_check (x : FullFloat) : Bool :=
  (is_finite_FF (Bopp x))

theorem is_finite_Bopp (x : FullFloat) :
  ⦃⌜True⌝⦄
  is_finite_Bopp_check x
  ⦃⇓result => ⌜result = is_finite_FF x⌝⦄ := by
  intro _
  cases x <;> simp [is_finite_Bopp_check, is_finite_FF, Bopp]

def Bsign_Bopp_check (x : FullFloat) : Bool :=
  (sign_FF (Bopp x))

theorem Bsign_Bopp (x : FullFloat) (hx : is_nan_FF x = false) :
  ⦃⌜True⌝⦄
  Bsign_Bopp_check x
  ⦃⇓result => ⌜result = bnot (sign_FF x)⌝⦄ := by
  intro _
  cases x <;>
    simp [Bsign_Bopp_check, sign_FF, Bopp, bnot, is_nan_FF] at hx ⊢

-- Absolute value on FullFloat (Coq: Babs)
def Babs (x : FullFloat) : FullFloat :=
  match x with
  | FullFloat.F754_nan s pl => FullFloat.F754_nan s pl
  | FullFloat.F754_infinity _ => FullFloat.F754_infinity false
  | FullFloat.F754_finite _ m e => FullFloat.F754_finite false m e
  | FullFloat.F754_zero _ => FullFloat.F754_zero false

noncomputable def B2R_Babs_check (x : FullFloat) : ℝ :=
  (FF2R 2 (Babs x))

theorem B2R_Babs (x : FullFloat) :
  ⦃⌜True⌝⦄
  B2R_Babs_check x
  ⦃⇓result => ⌜result = |FF2R 2 x|⌝⦄ := by
  intro _
  cases x with
  | F754_zero s =>
      simp [B2R_Babs_check, FF2R, Babs]
  | F754_infinity s =>
      simp [B2R_Babs_check, FF2R, Babs]
  | F754_nan s m =>
      simp [B2R_Babs_check, FF2R, Babs]
  | F754_finite s m e =>
      simp [B2R_Babs_check, FF2R, Babs, F2R, FloatSpec.Core.Defs.F2R]
      cases s <;> simp [Id, Pure.pure]

def is_finite_Babs_check (x : FullFloat) : Bool :=
  (is_finite_FF (Babs x))

theorem is_finite_Babs (x : FullFloat) :
  ⦃⌜True⌝⦄
  is_finite_Babs_check x
  ⦃⇓result => ⌜result = is_finite_FF x⌝⦄ := by
  intro _
  cases x <;> simp [is_finite_Babs_check, is_finite_FF, Babs]

def Bsign_Babs_check (x : FullFloat) : Bool :=
  (sign_FF (Babs x))

theorem Bsign_Babs (x : FullFloat) (hx : is_nan_FF x = false) :
  ⦃⌜True⌝⦄
  Bsign_Babs_check x
  ⦃⇓result => ⌜result = false⌝⦄ := by
  intro _
  cases x <;>
    simp [Bsign_Babs_check, sign_FF, Babs, is_nan_FF] at hx ⊢

def Babs_idempotent_check (x : FullFloat) : FullFloat :=
  (Babs (Babs x))

theorem Babs_idempotent (x : FullFloat) (hx : is_nan_FF x = false) :
  ⦃⌜True⌝⦄
  Babs_idempotent_check x
  ⦃⇓result => ⌜result = Babs x⌝⦄ := by
  intro _
  cases x <;> simp [Babs_idempotent_check, Babs, is_nan_FF] at hx ⊢

def Babs_Bopp_check (x : FullFloat) : FullFloat :=
  (Babs (Bopp x))

theorem Babs_Bopp (x : FullFloat) (hx : is_nan_FF x = false) :
  ⦃⌜True⌝⦄
  Babs_Bopp_check x
  ⦃⇓result => ⌜result = Babs x⌝⦄ := by
  intro _
  cases x <;>
    simp [Babs_Bopp_check, Babs, Bopp, bnot, is_nan_FF] at hx ⊢

-- Sign extraction for StandardFloat
def sign_SF (x : StandardFloat) : Bool :=
  match x with
  | StandardFloat.S754_zero s => s
  | StandardFloat.S754_infinity s => s
  | StandardFloat.S754_nan => false
  | StandardFloat.S754_finite s _ _ => s

-- Finite check for StandardFloat
def is_finite_SF (f : StandardFloat) : Bool :=
  match f with
  | StandardFloat.S754_finite _ _ _ => true
  | StandardFloat.S754_zero _ => true
  | _ => false

-- Finite check consistency
theorem is_finite_SF2FF (x : StandardFloat) :
  is_finite_FF (SF2FF x) = is_finite_SF x := by
  cases x <;> rfl

-- Finite predicate in the other direction
theorem is_finite_FF2SF (x : FullFloat) :
  is_finite_SF (FF2SF x) = is_finite_FF x := by
  cases x <;> rfl

-- Sign consistency
theorem sign_SF2FF (x : StandardFloat) :
  sign_FF (SF2FF x) = sign_SF x := by
  cases x <;> rfl

-- Sign consistency in the other direction
theorem sign_FF2SF (x : FullFloat) :
  sign_SF (FF2SF x) = (if is_nan_FF x then false else sign_FF x) := by
  cases x <;> rfl

-- Section: Binary IEEE 754 formats

variable (prec emax : Int)
variable [Prec_gt_0 prec]
variable [Prec_lt_emax prec emax]

-- IEEE 754 binary format
structure Binary754 (prec emax : Int) where
  val : FullFloat
  valid : is_finite_FF val = true →
    -- Valid range and precision constraints
    True

-- Helper conversions between FullFloat and Binary754
def B2FF {prec emax} (x : Binary754 prec emax) : FullFloat := x.val
def FF2B {prec emax} (x : FullFloat) : Binary754 prec emax :=
  { val := x, valid := by intro; trivial }

-- Real semantics for `Binary754` (Coq: B2R)
noncomputable def B2R {prec emax} (x : Binary754 prec emax) : ℝ :=
  FF2R 2 x.val

-- Standard view to standard-float (Coq: B2SF)
def B2SF {prec emax} (x : Binary754 prec emax) : StandardFloat :=
  FF2SF x.val

-- Coq: B2FF_FF2B — B2FF after FF2B is identity
theorem B2FF_FF2B {prec emax} (x : FullFloat) :
  B2FF (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) x) = x := by
  rfl

-- Coq: FF2B_B2FF — FF2B after B2FF is identity
theorem FF2B_B2FF {prec emax} (x : Binary754 prec emax) :
  FF2B (prec:=prec) (emax:=emax) (B2FF (prec:=prec) (emax:=emax) x) = x := by
  -- trivial by construction of `FF2B` and `B2FF`
  cases x <;> rfl

-- Coq: B2FF_inj — B2FF is injective
theorem B2FF_inj {prec emax} (x y : Binary754 prec emax) :
  B2FF (prec:=prec) (emax:=emax) x = B2FF (prec:=prec) (emax:=emax) y → x = y := by
  intro h; cases x; cases y; cases h; rfl

-- Coq: FF2R_B2FF — Real semantics preserved by B2FF
theorem FF2R_B2FF (beta : Int) {prec emax} (x : Binary754 prec emax) :
  FF2R beta (B2FF (prec:=prec) (emax:=emax) x) = FF2R beta x.val := by
  rfl

-- Coq: FF2SF_B2FF — Standard view after B2FF matches direct view
theorem FF2SF_B2FF {prec emax} (x : Binary754 prec emax) :
  FF2SF (B2FF (prec:=prec) (emax:=emax) x) = B2SF (prec:=prec) (emax:=emax) x := by
  rfl

-- Coq: B2SF_FF2B — Standard view after FF2B equals FF2SF of source
theorem B2SF_FF2B {prec emax} (x : FullFloat) :
  B2SF (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) x) = FF2SF x := by
  rfl

-- Coq: B2SF_B2BSN — compatibility between `B2SF` and the SingleNaN bridge
-- We mirror the Coq lemma by delegating to the version in BinarySingleNaN
-- that we stated using the hoare-triple style.
-- NOTE: The hoare-triple version of this lemma lives in BinarySingleNaN.

-- Coq: B2R_B2BSN — compatibility for real semantics
-- NOTE: The hoare-triple version of this lemma lives in BinarySingleNaN.

-- Coq: is_finite_B2FF — Finite predicate preserved by B2FF
-- We mirror the Coq statement with a straightforward alias in our setting.
def is_finite_B {prec emax} (x : Binary754 prec emax) : Bool :=
  is_finite_FF x.val

theorem is_finite_B2FF {prec emax} (x : Binary754 prec emax) :
  is_finite_FF (B2FF (prec:=prec) (emax:=emax) x) = is_finite_B (prec:=prec) (emax:=emax) x := by
  rfl

-- Coq: is_nan_B2FF — NaN predicate preserved by B2FF
def is_nan_B {prec emax} (x : Binary754 prec emax) : Bool :=
  is_nan_FF x.val

theorem is_nan_B2FF {prec emax} (x : Binary754 prec emax) :
  is_nan_FF (B2FF (prec:=prec) (emax:=emax) x) = is_nan_B (prec:=prec) (emax:=emax) x := by
  rfl

-- Coq: B2R_FF2B — Real semantics after FF2B equals semantics of source
theorem B2R_FF2B (beta : Int) {prec emax} (x : FullFloat) :
  FF2R beta (B2FF (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) x)) = FF2R beta x := by
  rfl

-- (reserved) Coq: B2SF_inj — provided on the SingleNaN side in this port

-- Coq: Bsign_FF2B — Sign preserved by FF2B
def Bsign {prec emax} (x : Binary754 prec emax) : Bool :=
  sign_FF x.val

theorem Bsign_FF2B {prec emax} (x : FullFloat) :
  Bsign (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) x) = sign_FF x := by
  rfl

-- Coq: is_finite_FF2B — Finite predicate after FF2B equals source predicate
theorem is_finite_FF2B {prec emax} (x : FullFloat) :
  is_finite_B (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) x) = is_finite_FF x := by
  rfl

-- Coq: is_nan_FF2B — NaN predicate after FF2B equals source predicate
theorem is_nan_FF2B {prec emax} (x : FullFloat) :
  is_nan_B (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) x) = is_nan_FF x := by
  rfl

-- Coq: B2R_inj — injectivity of representation from real semantics (under finiteness)
theorem B2R_inj {prec emax} (x y : Binary754 prec emax)
  (hx : is_finite_B (prec:=prec) (emax:=emax) x = true)
  (hy : is_finite_B (prec:=prec) (emax:=emax) y = true)
  (hR : B2R (prec:=prec) (emax:=emax) x = B2R (prec:=prec) (emax:=emax) y) :
  x = y := by
  sorry

-- Coq: B2R_Bsign_inj — injectivity using semantics plus sign
theorem B2R_Bsign_inj {prec emax} (x y : Binary754 prec emax)
  (hx : is_finite_B (prec:=prec) (emax:=emax) x = true)
  (hy : is_finite_B (prec:=prec) (emax:=emax) y = true)
  (hR : B2R (prec:=prec) (emax:=emax) x = B2R (prec:=prec) (emax:=emax) y)
  (hs : Bsign (prec:=prec) (emax:=emax) x = Bsign (prec:=prec) (emax:=emax) y) :
  x = y := by
  sorry

-- (reserved) Coq counterparts `valid_binary_B2FF` and `FF2B_B2FF_valid`
-- will be introduced in hoare-triple form after aligning specs.

-- Coq: valid_binary_B2FF — validity of `B2FF` images
-- We expose a lightweight validity predicate and state the theorem
-- using the Hoare-triple style around a pure computation.
def valid_binary {prec emax : Int} (x : FullFloat) : Bool :=
  -- Placeholder predicate (to be refined): always true for this stub
  true

def valid_binary_B2FF_check {prec emax : Int} (x : Binary754 prec emax) : Bool :=
  (valid_binary (prec:=prec) (emax:=emax) (B2FF (prec:=prec) (emax:=emax) x))

theorem valid_binary_B2FF {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  valid_binary_B2FF_check (prec:=prec) (emax:=emax) x
  ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold valid_binary_B2FF_check
  rfl

-- Coq: valid_binary_SF2FF — validity of SF after conversion to FF
-- We introduce a StandardFloat-side validity predicate and state
-- the correspondence in hoare-triple form.
def valid_binary_SF {prec emax : Int} (x : StandardFloat) : Bool :=
  -- Placeholder predicate (to be refined): always true for this stub
  true

def valid_binary_SF2FF_check {prec emax : Int} (x : StandardFloat) : Bool :=
  (valid_binary (prec:=prec) (emax:=emax) (SF2FF x))

theorem valid_binary_SF2FF {prec emax} (x : StandardFloat)
  (hnotnan : is_nan_SF x = false) :
  ⦃⌜True⌝⦄
  valid_binary_SF2FF_check (prec:=prec) (emax:=emax) x
  ⦃⇓result => ⌜result = valid_binary_SF (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  unfold valid_binary_SF2FF_check
  rfl

-- Coq: FF2B_B2FF_valid — round-trip with validity argument
-- We mirror it in hoare-triple style around the pure computation.
def FF2B_B2FF_valid_check {prec emax : Int} (x : Binary754 prec emax) : (Binary754 prec emax) :=
  (FF2B (prec:=prec) (emax:=emax) (B2FF (prec:=prec) (emax:=emax) x))

theorem FF2B_B2FF_valid {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  FF2B_B2FF_valid_check (prec:=prec) (emax:=emax) x
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  unfold FF2B_B2FF_valid_check
  simpa using (FF2B_B2FF (prec:=prec) (emax:=emax) x)

-- Coq: match_FF2B — pattern match through FF2B corresponds to match on source
-- We expose a small check returning the right-hand side match directly on `x`.
def match_FF2B_check {T : Type} (fz : Bool → T) (fi : Bool → T)
  (fn : Bool → Nat → T) (ff : Bool → Nat → Int → T)
  (x : FullFloat) : T :=
  <|
    match x with
    | FullFloat.F754_zero sx => fz sx
    | FullFloat.F754_infinity sx => fi sx
    | FullFloat.F754_nan b p => fn b p
    | FullFloat.F754_finite sx mx ex => ff sx mx ex

theorem match_FF2B {T : Type} (fz : Bool → T) (fi : Bool → T)
  (fn : Bool → Nat → T) (ff : Bool → Nat → Int → T)
  (x : FullFloat) :
  ⦃⌜True⌝⦄
  match_FF2B_check fz fi fn ff x
  ⦃⇓result => ⌜result =
      (match x with
       | FullFloat.F754_zero sx => fz sx
       | FullFloat.F754_infinity sx => fi sx
       | FullFloat.F754_nan b p => fn b p
       | FullFloat.F754_finite sx mx ex => ff sx mx ex)⌝⦄ := by
  intro _
  unfold match_FF2B_check
  rfl

-- Standard IEEE 754 operations
def binary_add (x y : Binary754 prec emax) : Binary754 prec emax :=
  x

def binary_sub (x y : Binary754 prec emax) : Binary754 prec emax :=
  x

def binary_mul (x y : Binary754 prec emax) : Binary754 prec emax :=
  x

-- (reserved) Decomposition theorem (Coq: Bfrexp) will be added later

-- Decomposition (Coq: Bfrexp)
-- We expose a placeholder implementation returning a mantissa-like binary
-- float together with an exponent, and state the Coq theorem in
-- Hoare‑triple style. Proof is deferred.
def Bfrexp (x : Binary754 prec emax) : (Binary754 prec emax) × Int :=
  -- Placeholder: actual implementation exists in Coq and relates to the BSN layer.
  (x, 0)

-- Local strict-finiteness classifier for Binary754 (finite and nonzero semantics).
-- Coq uses a positive mantissa, so finite implies nonzero. Our Lean stub keeps
-- the shape and defers proof obligations elsewhere.
def is_finite_strict_Bin (x : Binary754 prec emax) : Bool :=
  match x.val with
  | FullFloat.F754_finite _ _ _ => true
  | _ => false

noncomputable def Bfrexp_correct_check (x : Binary754 prec emax) :
  ((Binary754 prec emax) × Int) :=
  (Bfrexp (prec:=prec) (emax:=emax) x)

-- Coq: Bfrexp_correct
-- For strictly finite inputs, Bfrexp decomposes x = z * 2^e with |B2R z| in [1/2,1)
-- and e = mag 2 (B2R x).
theorem Bfrexp_correct (x : Binary754 prec emax)
  (hx : is_finite_strict_Bin (prec:=prec) (emax:=emax) x = true) :
  ⦃⌜True⌝⦄
  Bfrexp_correct_check (prec:=prec) (emax:=emax) x
  ⦃⇓result => ⌜
      let z := result.1; let e := result.2;
      (1 / 2 ≤ |B2R (prec:=prec) (emax:=emax) z| ∧
         |B2R (prec:=prec) (emax:=emax) z| < 1) ∧
      B2R (prec:=prec) (emax:=emax) x
        = B2R (prec:=prec) (emax:=emax) z * (FloatSpec.Core.Raux.bpow 2 e).run ∧
      e = (FloatSpec.Core.Raux.mag 2 (B2R (prec:=prec) (emax:=emax) x))⌝⦄ := by
  intro _
  -- Proof deferred; follows Coq via the BSN bridge (BinarySingleNaN.Bfrexp_correct)
  exact sorry

def binary_div (x y : Binary754 prec emax) : Binary754 prec emax :=
  x

def binary_sqrt (x : Binary754 prec emax) : Binary754 prec emax :=
  x

-- Fused multiply-add
def binary_fma (x y z : Binary754 prec emax) : Binary754 prec emax :=
  x

-- IEEE 754 rounding modes
inductive RoundingMode where
  | RNE : RoundingMode  -- Round to nearest, ties to even
  | RNA : RoundingMode  -- Round to nearest, ties away from zero
  | RTP : RoundingMode  -- Round toward positive infinity
  | RTN : RoundingMode  -- Round toward negative infinity
  | RTZ : RoundingMode  -- Round toward zero

-- Convert rounding mode to rounding function
def rnd_of_mode (mode : RoundingMode) : ℝ → Int :=
  fun _ => 0

-- Overflow helper (FullFloat variant). In Coq this is bridged via SingleNaN.
-- We keep a local stub returning an infinity with the requested sign.
def binary_overflow (mode : RoundingMode) (s : Bool) : FullFloat :=
  FullFloat.F754_infinity s

-- Coq: eq_binary_overflow_FF2SF
-- If FF2SF x corresponds to the single-NaN overflow value, then x is the
-- corresponding full-float overflow value.
def eq_binary_overflow_FF2SF_check
  (x : FullFloat) (mode : RoundingMode) (s : Bool)
  (h : FF2SF x = StandardFloat.S754_infinity s) : FullFloat :=
  x

theorem eq_binary_overflow_FF2SF
  (x : FullFloat) (mode : RoundingMode) (s : Bool)
  (h : FF2SF x = StandardFloat.S754_infinity s) :
  ⦃⌜True⌝⦄
  eq_binary_overflow_FF2SF_check x mode s h
  ⦃⇓result => ⌜result = binary_overflow mode s⌝⦄ := by
  intro _
  cases x <;>
    simp [eq_binary_overflow_FF2SF_check, FF2SF, binary_overflow] at h ⊢
  · cases h
    rfl

-- Coq: fexp_emax — the exponent function at emax
-- In the Binary (full‑float) view, this expresses the relationship
-- between FLT_exp and emax; we mirror as a hoare‑style assertion.
def fexp_emax_check : Unit :=
  ()

theorem fexp_emax :
  ⦃⌜True⌝⦄
  fexp_emax_check
  ⦃⇓_ => ⌜(FLT_exp (3 - emax - prec) prec) emax = emax - prec⌝⦄ := by
  intro _
  -- Proof deferred; unfolds `FLT_exp` and simplifies arithmetic.
  exact sorry

-- Binary format properties
theorem binary_add_correct (mode : RoundingMode) (x y : Binary754 prec emax) :
  FF2R 2 ((binary_add (prec:=prec) (emax:=emax) x y).val) =
  FloatSpec.Calc.Round.round 2 (FLT_exp (3 - emax - prec) prec) ()
    (FF2R 2 x.val + FF2R 2 y.val) := by
  sorry

theorem binary_mul_correct (mode : RoundingMode) (x y : Binary754 prec emax) :
  FF2R 2 ((binary_mul (prec:=prec) (emax:=emax) x y).val) =
  FloatSpec.Calc.Round.round 2 (FLT_exp (3 - emax - prec) prec) ()
    (FF2R 2 x.val * FF2R 2 y.val) := by
  sorry

-- Fused multiply-add correctness (Coq: Bfma_correct)
noncomputable def Bfma_correct_check (mode : RoundingMode)
  (x y z : Binary754 prec emax) : ℝ :=
  (FF2R 2 ((binary_fma (prec:=prec) (emax:=emax) x y z).val))

theorem Bfma_correct (mode : RoundingMode)
  (x y z : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  Bfma_correct_check (prec:=prec) (emax:=emax) mode x y z
  ⦃⇓result => ⌜result =
      FloatSpec.Calc.Round.round 2 (FLT_exp (3 - emax - prec) prec) ()
        (FF2R 2 x.val * FF2R 2 y.val + FF2R 2 z.val)⌝⦄ := by
  intro _
  -- Proof deferred; follows the pattern of multiplication/addition correctness.
  exact sorry

-- Subtraction correctness (Coq: Bminus_correct)
-- We follow the hoare-triple wrapper pattern used in this project.
noncomputable def Bminus_correct_check (mode : RoundingMode)
  (x y : Binary754 prec emax) : ℝ :=
  (FF2R 2 ((binary_sub (prec:=prec) (emax:=emax) x y).val))

theorem Bminus_correct (mode : RoundingMode) (x y : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  Bminus_correct_check (prec:=prec) (emax:=emax) mode x y
  ⦃⇓result => ⌜result =
      FloatSpec.Calc.Round.round 2 (FLT_exp (3 - emax - prec) prec) ()
        (FF2R 2 x.val - FF2R 2 y.val)⌝⦄ := by
  intro _
  -- Proof deferred; mirrors `binary_add_correct` with subtraction.
  exact sorry

-- Division correctness (Coq: Bdiv_correct)
noncomputable def Bdiv_correct_check (mode : RoundingMode)
  (x y : Binary754 prec emax) : ℝ :=
  (FF2R 2 ((binary_div (prec:=prec) (emax:=emax) x y).val))

theorem Bdiv_correct (mode : RoundingMode) (x y : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  Bdiv_correct_check (prec:=prec) (emax:=emax) mode x y
  ⦃⇓result => ⌜result =
      FloatSpec.Calc.Round.round 2 (FLT_exp (3 - emax - prec) prec) ()
        (FF2R 2 x.val / FF2R 2 y.val)⌝⦄ := by
  intro _
  -- Proof deferred; follows pattern of `binary_mul_correct`.
  exact sorry

-- Square-root correctness (Coq: Bsqrt_correct)
noncomputable def Bsqrt_correct_check (mode : RoundingMode)
  (x : Binary754 prec emax) : ℝ :=
  (FF2R 2 ((binary_sqrt (prec:=prec) (emax:=emax) x).val))

theorem Bsqrt_correct (mode : RoundingMode) (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  Bsqrt_correct_check (prec:=prec) (emax:=emax) mode x
  ⦃⇓result => ⌜result =
      FloatSpec.Calc.Round.round 2 (FLT_exp (3 - emax - prec) prec) ()
        (Real.sqrt (FF2R 2 x.val))⌝⦄ := by
  intro _
  -- Proof deferred; follows pattern of `binary_mul_correct`.
  exact sorry

-- Round to nearest integer-like operation (Coq: Bnearbyint)
def binary_nearbyint (mode : RoundingMode) (x : Binary754 prec emax) : Binary754 prec emax :=
  x

noncomputable def Bnearbyint_correct_check (mode : RoundingMode)
  (x : Binary754 prec emax) : ℝ :=
  (FF2R 2 ((binary_nearbyint (prec:=prec) (emax:=emax) mode x).val))

theorem Bnearbyint_correct (mode : RoundingMode) (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  Bnearbyint_correct_check (prec:=prec) (emax:=emax) mode x
  ⦃⇓result => ⌜result =
      FloatSpec.Calc.Round.round 2 (FLT_exp (3 - emax - prec) prec) ()
        (FF2R 2 x.val)⌝⦄ := by
  intro _
  -- Proof deferred; nearbyint rounds x according to the current format.
  exact sorry

-- Exponent scaling (Coq: Bldexp)
def binary_ldexp (mode : RoundingMode) (x : Binary754 prec emax) (e : Int) : Binary754 prec emax :=
  x

noncomputable def Bldexp_correct_check (mode : RoundingMode)
  (x : Binary754 prec emax) (e : Int) : ℝ :=
  (FF2R 2 ((binary_ldexp (prec:=prec) (emax:=emax) mode x e).val))

-- Coq: Bldexp_correct — scaling by 2^e then rounding to the target format
theorem Bldexp_correct (mode : RoundingMode)
  (x : Binary754 prec emax) (e : Int) :
  ⦃⌜True⌝⦄
  Bldexp_correct_check (prec:=prec) (emax:=emax) mode x e
  ⦃⇓result => ⌜result =
      FloatSpec.Calc.Round.round 2 (FLT_exp (3 - emax - prec) prec) ()
        (FF2R 2 x.val * (FloatSpec.Core.Raux.bpow 2 e).run)⌝⦄ := by
  intro _
  -- Proof deferred; follows Coq's `Bldexp_correct`.
  exact sorry

-- (reserved) Unit in the last place (Coq: Bulp) will be added later

-- Successor and predecessor (Coq: Bsucc, Bpred)
-- We expose placeholders for the operations and their correctness theorems
-- in hoare‑triple style, mirroring the Coq statements via the BSN bridge.

def Bsucc (x : Binary754 prec emax) : Binary754 prec emax :=
  x

noncomputable def Bsucc_correct_check (x : Binary754 prec emax) : ℝ :=
  (FF2R 2 ((Bsucc (prec:=prec) (emax:=emax) x).val))

-- Coq: Bsucc_correct — either steps by one ULP or overflows to +∞
theorem Bsucc_correct (x : Binary754 prec emax)
  (hx : is_finite_B (prec:=prec) (emax:=emax) x = true) :
  ⦃⌜True⌝⦄
  Bsucc_correct_check (prec:=prec) (emax:=emax) x
  ⦃⇓result => ⌜
      result =
        (FloatSpec.Core.Ulp.succ 2 (FLT_exp (3 - emax - prec) prec)
          (B2R (prec:=prec) (emax:=emax) x)) ∨
      B2FF (prec:=prec) (emax:=emax) (Bsucc (prec:=prec) (emax:=emax) x)
        = FullFloat.F754_infinity false⌝⦄ := by
  intro _; exact sorry

def Bpred (x : Binary754 prec emax) : Binary754 prec emax :=
  x

noncomputable def Bpred_correct_check (x : Binary754 prec emax) : ℝ :=
  (FF2R 2 ((Bpred (prec:=prec) (emax:=emax) x).val))

-- Coq: Bpred_correct — either steps by one ULP or overflows to −∞
theorem Bpred_correct (x : Binary754 prec emax)
  (hx : is_finite_B (prec:=prec) (emax:=emax) x = true) :
  ⦃⌜True⌝⦄
  Bpred_correct_check (prec:=prec) (emax:=emax) x
  ⦃⇓result => ⌜
      result =
        (FloatSpec.Core.Ulp.pred 2 (FLT_exp (3 - emax - prec) prec)
          (B2R (prec:=prec) (emax:=emax) x)) ∨
      B2FF (prec:=prec) (emax:=emax) (Bpred (prec:=prec) (emax:=emax) x)
        = FullFloat.F754_infinity true⌝⦄ := by
  intro _; exact sorry

-- Constant one (Coq: Bone)
def binary_one : Binary754 prec emax :=
  -- Canonical finite representation for 1 = 1 * 2^0
  FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_finite false 1 0)

-- Hoare wrapper for Coq `Bone_correct` — real value of constant one
noncomputable def Bone_correct_check : ℝ :=
  (FF2R 2 (binary_one (prec:=prec) (emax:=emax)).val)

theorem Bone_correct :
  ⦃⌜True⌝⦄
  Bone_correct_check (prec:=prec) (emax:=emax)
  ⦃⇓result => ⌜result = 1⌝⦄ := by
  intro _
  simp [Bone_correct_check, binary_one, FF2B, FF2R, F2R, FloatSpec.Core.Defs.F2R]

-- Hoare wrapper for Coq `is_finite_Bone` — constant one is finite
def is_finite_Bone_check : Bool :=
  (is_finite_B (prec:=prec) (emax:=emax) (binary_one (prec:=prec) (emax:=emax)))

theorem is_finite_Bone :
  ⦃⌜True⌝⦄
  is_finite_Bone_check (prec:=prec) (emax:=emax)
  ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  simp [is_finite_Bone_check, is_finite_B, binary_one, FF2B, is_finite_FF]

-- Hoare wrapper for Coq `Bsign_Bone` — sign of constant one is false (positive)
def Bsign_Bone_check : Bool :=
  (Bsign (prec:=prec) (emax:=emax) (binary_one (prec:=prec) (emax:=emax)))

theorem Bsign_Bone :
  ⦃⌜True⌝⦄
  Bsign_Bone_check (prec:=prec) (emax:=emax)
  ⦃⇓result => ⌜result = false⌝⦄ := by
  intro _
  simp [Bsign_Bone_check, Bsign, binary_one, FF2B, sign_FF]

-- Truncation to integer (Coq: Btrunc)
noncomputable def binary_trunc (x : Binary754 prec emax) : Int :=
  -- Defined semantically via rounding toward zero at FIX_exp 0
  (FloatSpec.Core.Raux.Ztrunc (B2R (prec:=prec) (emax:=emax) x))

-- Hoare wrapper for Coq `Btrunc_correct`
noncomputable def Btrunc_correct_check (x : Binary754 prec emax) : Int :=
  (binary_trunc (prec:=prec) (emax:=emax) x)

-- Local Valid_exp instance for the constant exponent function used below
instance instValidExp_FIX0 :
  FloatSpec.Core.Generic_fmt.Valid_exp 2 (fun _ => (0 : Int)) := by
  refine ⟨?_⟩
  intro k; constructor
  · intro hk; exact le_of_lt hk
  · intro _; constructor
    · exact le_rfl
    · intro _ _; rfl

theorem Btrunc_correct (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  Btrunc_correct_check (prec:=prec) (emax:=emax) x
  ⦃⇓result => ⌜(result : ℝ) =
      FloatSpec.Calc.Round.round 2 (fun _ => (0 : Int)) ()
        (B2R (prec:=prec) (emax:=emax) x)⌝⦄ := by
  intro _
  -- Proof deferred; follows Coq's Btrunc_correct via BSN bridge.
  exact sorry

-- Common IEEE 754 formats
def Binary16 := Binary754 11 15
def Binary32 := Binary754 24 127
def Binary64 := Binary754 53 1023
def Binary128 := Binary754 113 16383

-- Missing Theorems (ported from Coq; hoare-style specs, proofs deferred)

-- Coq: canonical_canonical_mantissa
-- We introduce a lightweight placeholder predicate mirroring Coq's
-- canonical_mantissa and expose the canonicality statement in a
-- hoare-triple style wrapper. The actual proof is deferred.
def canonical_mantissa {prec emax : Int} (m : Nat) (e : Int) : Bool :=
  -- Placeholder: to be refined to the true canonical-mantissa predicate
  true

def canonical_canonical_mantissa_check {prec emax : Int}
  (sx : Bool) (mx : Nat) (ex : Int) : Unit :=
  ()

theorem canonical_canonical_mantissa (sx : Bool) (mx : Nat) (ex : Int)
  (h : canonical_mantissa (prec:=prec) (emax:=emax) mx ex = true) :
  ⦃⌜True⌝⦄
  canonical_canonical_mantissa_check (prec:=prec) (emax:=emax) sx mx ex
  ⦃⇓_ => ⌜FloatSpec.Core.Generic_fmt.canonical 2 (FLT_exp (3 - emax - prec) prec)
            (FloatSpec.Core.Defs.FlocqFloat.mk (if sx then -(mx : Int) else (mx : Int)) ex)⌝⦄ := by
  intro _
  -- Proof deferred; will be aligned with Coq's canonical_canonical_mantissa
  sorry

-- Coq: generic_format_B2R
-- Generic-format property of the real semantics of a binary float.
-- We mirror the statement in hoare-triple style and defer the proof.
def generic_format_B2R_check {prec emax : Int} (x : Binary754 prec emax) : Unit :=
  ()

theorem generic_format_B2R {prec emax : Int}
  (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  generic_format_B2R_check (prec:=prec) (emax:=emax) x
  ⦃⇓_ => ⌜FloatSpec.Core.Generic_fmt.generic_format 2 (FLT_exp (3 - emax - prec) prec) (B2R (prec:=prec) (emax:=emax) x)⌝⦄ := by
  intro _
  -- Proof deferred; follows Coq's generic_format_B2R
  sorry

-- Coq: FLT_format_B2R
-- FLT-format property of the real semantics of a binary float.
-- We mirror the statement in hoare-triple style and defer the proof.
def FLT_format_B2R_check {prec emax : Int} (x : Binary754 prec emax) : Unit :=
  ()

theorem FLT_format_B2R
  {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  FLT_format_B2R_check (prec:=prec) (emax:=emax) x
  ⦃⇓_ => ⌜FloatSpec.Core.FLT.FLT_format (prec:=prec) (emin := 3 - emax - prec) 2 (B2R (prec:=prec) (emax:=emax) x)⌝⦄ := by
  intro _
  -- Proof deferred; follows Coq's FLT_format_B2R via generic_format_B2R and FLT_format_generic
  sorry

-- Coq: emin_lt_emax — the minimal exponent is strictly less than emax (Binary side)
def emin_lt_emax_check_B : Unit :=
  ()

theorem emin_lt_emax_B :
  ⦃⌜True⌝⦄
  emin_lt_emax_check_B
  ⦃⇓_ => ⌜(3 - emax - prec) < emax⌝⦄ := by
  intro _; exact sorry

-- Coq: Bcompare_correct
-- We expose a comparison wrapper that, under finiteness of both operands,
-- returns the comparison code of the real semantics (using Rcompare.run).
noncomputable def Bcompare_check {prec emax : Int}
  (x y : Binary754 prec emax) : (Option Int) :=
  (some ((FloatSpec.Core.Raux.Rcompare (B2R (prec:=prec) (emax:=emax) x)
                                   (B2R (prec:=prec) (emax:=emax) y))))

theorem Bcompare_correct {prec emax : Int}
  (x y : Binary754 prec emax)
  (hx : is_finite_B (prec:=prec) (emax:=emax) x = true)
  (hy : is_finite_B (prec:=prec) (emax:=emax) y = true) :
  ⦃⌜True⌝⦄
  Bcompare_check (prec:=prec) (emax:=emax) x y
  ⦃⇓result => ⌜result = some ((FloatSpec.Core.Raux.Rcompare (B2R (prec:=prec) (emax:=emax) x)
                                                   (B2R (prec:=prec) (emax:=emax) y)))⌝⦄ := by
  intro _
  -- Proof deferred; will align with Coq's Bcompare_correct via the BSN bridge.
  exact sorry

-- Coq: Bcompare_swap
-- Swapping the arguments of the comparison negates the comparison code.
theorem Bcompare_swap {prec emax : Int}
  (x y : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  Bcompare_check (prec:=prec) (emax:=emax) y x
  ⦃⇓result => ⌜result = some (-(FloatSpec.Core.Raux.Rcompare (B2R (prec:=prec) (emax:=emax) x)
                                             (B2R (prec:=prec) (emax:=emax) y)))⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `Bcompare_swap` via properties of Rcompare.
  exact sorry

-- Coq: bounded_le_emax_minus_prec
-- For mantissa/exponent pairs that are `bounded`, the real value is
-- bounded above by bpow emax minus bpow (emax - prec).
-- We mirror the statement using a lightweight `bounded` predicate and
-- a hoare-triple wrapper, deferring the proof.
def bounded {prec emax : Int} (mx : Nat) (ex : Int) : Bool :=
  -- Placeholder for the Coq `SpecFloat.bounded prec emax` predicate
  true

def bounded_le_emax_minus_prec_check {prec emax : Int} (mx : Nat) (ex : Int) : Unit :=
  ()

theorem bounded_le_emax_minus_prec {prec emax : Int}
  (mx : Nat) (ex : Int)
  (h : bounded (prec:=prec) (emax:=emax) mx ex = true) :
  ⦃⌜True⌝⦄
  bounded_le_emax_minus_prec_check (prec:=prec) (emax:=emax) mx ex
  ⦃⇓_ => ⌜
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2)
        ≤ (FloatSpec.Core.Raux.bpow 2 emax).run
          - (FloatSpec.Core.Raux.bpow 2 (emax - prec)).run⌝⦄ := by
  intro _
  -- Proof deferred; aligns with Coq's `bounded_le_emax_minus_prec` via the BSN bridge.
  exact sorry

-- Coq: bounded_lt_emax — bounded values lie strictly below bpow emax
def bounded_lt_emax_check {prec emax : Int} (mx : Nat) (ex : Int) : Unit :=
  ()

theorem bounded_lt_emax {prec emax : Int}
  (mx : Nat) (ex : Int)
  (h : bounded (prec:=prec) (emax:=emax) mx ex = true) :
  ⦃⌜True⌝⦄
  bounded_lt_emax_check (prec:=prec) (emax:=emax) mx ex
  ⦃⇓_ => ⌜
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2)
        < (FloatSpec.Core.Raux.bpow 2 emax).run⌝⦄ := by
  intro _
  -- Proof deferred; aligns with Coq's `bounded_lt_emax`.
  exact sorry

-- Coq: bounded_ge_emin — bounded values lie above bpow emin
def bounded_ge_emin_check {prec emax : Int} (mx : Nat) (ex : Int) : Unit :=
  ()

theorem bounded_ge_emin {prec emax : Int}
  (mx : Nat) (ex : Int)
  (h : bounded (prec:=prec) (emax:=emax) mx ex = true) :
  ⦃⌜True⌝⦄
  bounded_ge_emin_check (prec:=prec) (emax:=emax) mx ex
  ⦃⇓_ => ⌜
      (FloatSpec.Core.Raux.bpow 2 (3 - emax - prec)).run
        ≤ F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2)⌝⦄ := by
  intro _
  -- Proof deferred; aligns with Coq's `bounded_ge_emin` using emin := 3 - emax - prec.
  exact sorry

-- Coq: abs_B2R_le_emax_minus_prec
-- The absolute value of the real semantics of any binary float is bounded
-- above by bpow emax minus bpow (emax - prec).
def abs_B2R_le_emax_minus_prec_check {prec emax : Int}
  (x : Binary754 prec emax) : Unit :=
  ()

theorem abs_B2R_le_emax_minus_prec {prec emax : Int}
  (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  abs_B2R_le_emax_minus_prec_check (prec:=prec) (emax:=emax) x
  ⦃⇓_ => ⌜
      |B2R (prec:=prec) (emax:=emax) x|
        ≤ (FloatSpec.Core.Raux.bpow 2 emax).run
            - (FloatSpec.Core.Raux.bpow 2 (emax - prec)).run⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `abs_B2R_le_emax_minus_prec` via the BSN bridge.
  exact sorry

-- Coq: abs_B2R_lt_emax — absolute semantics strictly below bpow emax
def abs_B2R_lt_emax_check {prec emax : Int}
  (x : Binary754 prec emax) : Unit :=
  ()

theorem abs_B2R_lt_emax {prec emax : Int}
  (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  abs_B2R_lt_emax_check (prec:=prec) (emax:=emax) x
  ⦃⇓_ => ⌜
      |B2R (prec:=prec) (emax:=emax) x|
        < (FloatSpec.Core.Raux.bpow 2 emax).run⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `abs_B2R_lt_emax` via the BSN bridge.
  exact sorry

-- Local strict-finiteness classifier for Binary754 (finite and nonzero semantics).
-- Coq uses a positive mantissa, so finite implies nonzero. Our Lean stub keeps
-- the shape and defers proof obligations elsewhere.
-- Duplicate declaration cleanup: ensure only the early local definition exists.

-- Coq: abs_B2R_ge_emin — strict finiteness implies lower bound by bpow emin
def abs_B2R_ge_emin_check {prec emax : Int}
  (x : Binary754 prec emax) : Unit :=
  ()

theorem abs_B2R_ge_emin {prec emax : Int}
  (x : Binary754 prec emax)
  (hx : is_finite_strict_Bin (prec:=prec) (emax:=emax) x = true) :
  ⦃⌜True⌝⦄
  abs_B2R_ge_emin_check (prec:=prec) (emax:=emax) x
  ⦃⇓_ => ⌜
      (FloatSpec.Core.Raux.bpow 2 (3 - emax - prec)).run
        ≤ |B2R (prec:=prec) (emax:=emax) x|⌝⦄ := by
  intro _
  -- Proof deferred; aligns with Coq's `abs_B2R_ge_emin` using emin := 3 - emax - prec.
  exact sorry

-- Coq: bounded_canonical_lt_emax
-- If a finite float with positive mantissa is canonical and its real value is
-- strictly below bpow emax, then the mantissa/exponent pair is `bounded`.
-- We mirror the statement in hoare-triple style and defer the proof.
def bounded_canonical_lt_emax_check {prec emax : Int}
  (mx : Nat) (ex : Int) : Unit :=
  ()

theorem bounded_canonical_lt_emax {prec emax : Int}
  (mx : Nat) (ex : Int)
  (hcanon : FloatSpec.Core.Generic_fmt.canonical 2 (FLT_exp (3 - emax - prec) prec)
              (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex))
  (hval :
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2)
      < (FloatSpec.Core.Raux.bpow 2 emax).run) :
  ⦃⌜True⌝⦄
  bounded_canonical_lt_emax_check (prec:=prec) (emax:=emax) mx ex
  ⦃⇓_ => ⌜bounded (prec:=prec) (emax:=emax) mx ex = true⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `bounded_canonical_lt_emax`.
  exact sorry

-- Alignment helper (Coq: shl_align_fexp)
-- In Coq, this calls `shl_align mx ex (fexp (Zpos (digits2_pos mx) + ex))`.
-- We expose a placeholder returning a mantissa/exponent pair; properties are
-- captured by the Hoare-style theorem below.
def shl_align_fexp (mx : Nat) (ex : Int) : Nat × Int :=
  (mx, ex)

-- Hoare wrapper to expose `shl_align_fexp` as a pure computation
def shl_align_fexp_check (mx : Nat) (ex : Int) : (Nat × Int) :=
  (shl_align_fexp mx ex)

-- Coq: shl_align_fexp_correct
-- After alignment, the real value is preserved and the new exponent
-- satisfies the `fexp` bound at `Zdigits mx' + ex'`.
theorem shl_align_fexp_correct {prec emax : Int}
  (mx : Nat) (ex : Int) :
  ⦃⌜True⌝⦄
  shl_align_fexp_check mx ex
  ⦃⇓result => ⌜
      let mx' := result.1; let ex' := result.2
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx' : Int) ex' : FloatSpec.Core.Defs.FlocqFloat 2)
        = F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2)
        ∧ ex' ≤ FLT_exp (3 - emax - prec) prec ((FloatSpec.Core.Digits.Zdigits 2 (mx' : Int)) + ex')⌝⦄ := by
  intro _
  -- Proof deferred; follows from the correctness of `shl_align` specialized
  -- to `fexp := FLT_exp (3 - emax - prec) prec` and the relation between
  -- `Zdigits` and `digits2_pos`.
  exact sorry

-- Truncation helpers and theorem (Coq: shr_fexp_truncate)
-- We introduce lightweight placeholders sufficient to state the theorem
-- in hoare-triple style, following the project pattern.

-- Local alias of the Bracket location type
abbrev Loc := FloatSpec.Calc.Bracket.Location

-- Placeholder for Coq's `shr_record_of_loc` (depends only on mantissa here)
def shr_record_of_loc (m : Int) (_ : Loc) : Int := m

-- Shifting according to `fexp` via truncation; mirrors Coq's `shr_fexp` shape
def shr_fexp (m e : Int) (l : Loc) : Int × Int :=
  let r := (FloatSpec.Calc.Round.truncate (beta := 2)
              (f := (FloatSpec.Core.Defs.FlocqFloat.mk m e : FloatSpec.Core.Defs.FlocqFloat 2))
              (e := e) (l := l)).run
  let m' := r.1; let e' := r.2.1; let l' := r.2.2
  (shr_record_of_loc m' l', e')

-- Hoare wrapper to expose `shr_fexp` as a pure computation
def shr_fexp_truncate_check (m e : Int) (l : Loc) : (Int × Int) :=
  (shr_fexp m e l)

-- Coq: shr_fexp_truncate — express `shr_fexp` via `truncate`
theorem shr_fexp_truncate (m e : Int) (l : Loc)
  (hm : 0 ≤ m) :
  ⦃⌜True⌝⦄
  shr_fexp_truncate_check m e l
  ⦃⇓result => ⌜
      let r := (FloatSpec.Calc.Round.truncate (beta := 2)
                  (f := (FloatSpec.Core.Defs.FlocqFloat.mk m e : FloatSpec.Core.Defs.FlocqFloat 2))
                  (e := e) (l := l)).run
      let m' := r.1; let e' := r.2.1; let l' := r.2.2
      result = (shr_record_of_loc m' l', e')⌝⦄ := by
  intro _
  -- Proof deferred; follows by unfolding `shr_fexp` and the placeholder definitions.
  exact sorry

-- Rounding auxiliary (Coq: binary_round_aux and its correctness lemmas)
-- We introduce a lightweight placeholder for `binary_round_aux` and
-- state Coq's two correctness theorems in Hoare‑triple style. Proofs are deferred.

-- Auxiliary rounding step (placeholder; mirrors Coq's `binary_round_aux` shape)
noncomputable def binary_round_aux (mode : RoundingMode)
  (sx : Bool) (mx : Int) (ex : Int) (lx : Loc) : FullFloat := by
  -- Implemented elsewhere in Coq; here we only expose its type.
  exact FullFloat.F754_nan false 1

-- Hoare wrapper for `binary_round_aux_correct'` (prime version)
noncomputable def binary_round_aux_correct'_check
  (mode : RoundingMode) (x : ℝ) (sx : Bool) (mx : Nat) (ex : Int) (lx : Loc) : FullFloat :=
  (binary_round_aux mode sx (mx : Int) ex lx)

-- Coq: binary_round_aux_correct'
-- Either returns a finite result that corresponds to rounding of x
-- or signals overflow via `binary_overflow`. We capture this shape
-- without committing to exact numerical premises here.
theorem binary_round_aux_correct' (mode : RoundingMode)
  (x : ℝ) (sx : Bool) (mx : Nat) (ex : Int) (lx : Loc) :
  ⦃⌜True⌝⦄
  binary_round_aux_correct'_check mode x sx mx ex lx
  ⦃⇓z => ⌜is_finite_FF z = true ∨
              z = binary_overflow mode sx⌝⦄ := by
  intro _
  -- Proof deferred; follows Coq's binary_round_aux_correct' via the BSN bridge.
  exact sorry

-- High-level rounding (Coq: binary_round and binary_round_correct)
noncomputable def binary_round (mode : RoundingMode)
  (sx : Bool) (mx : Nat) (ex : Int) : FullFloat :=
  -- Placeholder: actual implementation delegated to BSN layer in Coq.
  FullFloat.F754_nan false 1

noncomputable def binary_round_correct_check (mode : RoundingMode)
  (x : ℝ) (sx : Bool) (mx : Nat) (ex : Int) : FullFloat :=
  (binary_round mode sx mx ex)

theorem binary_round_correct (mode : RoundingMode)
  (x : ℝ) (sx : Bool) (mx : Nat) (ex : Int) :
  ⦃⌜True⌝⦄
  binary_round_correct_check mode x sx mx ex
  ⦃⇓z => ⌜is_finite_FF z = true ∨
              z = binary_overflow mode sx⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `binary_round_correct` via the BSN bridge.
  exact sorry

-- Normalization (Coq: binary_normalize and binary_normalize_correct)
noncomputable def binary_normalize (mode : RoundingMode)
  (mx : Nat) (ex : Int) (szero : Bool) : FullFloat :=
  -- Placeholder: actual implementation exists in Coq; we only mirror the API.
  FullFloat.F754_nan false 1

noncomputable def binary_normalize_correct_check (mode : RoundingMode)
  (mx : Nat) (ex : Int) (szero : Bool) : FullFloat :=
  (binary_normalize mode mx ex szero)

theorem binary_normalize_correct (mode : RoundingMode)
  (mx : Nat) (ex : Int) (szero : Bool) :
  ⦃⌜True⌝⦄
  binary_normalize_correct_check mode mx ex szero
  ⦃⇓z => ⌜is_finite_FF z = true ∨ is_nan_FF z = true⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `binary_normalize_correct` shape.
  exact sorry

-- Hoare wrapper for `binary_round_aux_correct` (non‑prime version)
noncomputable def binary_round_aux_correct_check
  (mode : RoundingMode) (x : ℝ) (sx : Bool) (mx : Nat) (ex : Int) (lx : Loc) : FullFloat :=
  (binary_round_aux mode sx (mx : Int) ex lx)

-- Coq: binary_round_aux_correct
theorem binary_round_aux_correct (mode : RoundingMode)
  (x : ℝ) (sx : Bool) (mx : Nat) (ex : Int) (lx : Loc) :
  ⦃⌜True⌝⦄
  binary_round_aux_correct_check mode x sx mx ex lx
  ⦃⇓z => ⌜is_finite_FF z = true ∨
              z = binary_overflow mode sx⌝⦄ := by
  intro _
  -- Proof deferred; follows Coq's binary_round_aux_correct via the BSN bridge.
  exact sorry
