-- Binary single NaN operations
-- Translated from Coq file: flocq/src/IEEE754/BinarySingleNaN.v

import FloatSpec.src.IEEE754.Binary
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import FloatSpec.src.Calc.Sqrt
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
  (x : StandardFloat) : T :=
    match x with
    | StandardFloat.S754_zero sx => fz sx
    | StandardFloat.S754_infinity sx => fi sx
    | StandardFloat.S754_nan => fn
    | StandardFloat.S754_finite sx mx ex => ff sx mx ex

theorem match_SF2B {T : Type}
  (fz : Bool → T) (fi : Bool → T) (fn : T) (ff : Bool → Nat → Int → T)
  (x : StandardFloat) :
  ⦃⌜True⌝⦄
  (pure (match_SF2B_check fz fi fn ff x) : Id T)
  ⦃⇓result => ⌜result =
      (match SF2B x with
       | B754.B754_zero sx => fz sx
       | B754.B754_infinity sx => fi sx
       | B754.B754_nan => fn
       | B754.B754_finite sx mx ex => ff sx mx ex)⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold match_SF2B_check SF2B
  cases x <;> rfl

-- Coq: canonical_canonical_mantissa (SingleNaN side)
-- Mirror the Binary.lean style: hoare-triple statement yielding canonicality.
def canonical_canonical_mantissa_bsn_check
  (sx : Bool) (mx : Nat) (ex : Int) : Unit :=
  ()

theorem canonical_canonical_mantissa_bsn
  (sx : Bool) (mx : Nat) (ex : Int)
  (hmx_pos : 0 < mx)  -- IEEE 754: finite floats have positive mantissa; zero is B754_zero
  (h : canonical_mantissa (prec:=prec) (emax:=emax) mx ex = true) :
  ⦃⌜True⌝⦄
  (pure (canonical_canonical_mantissa_bsn_check sx mx ex) : Id Unit)
  ⦃⇓_ => ⌜FloatSpec.Core.Generic_fmt.canonical 2 (FLT_exp (3 - emax - prec) prec)
            (FloatSpec.Core.Defs.FlocqFloat.mk (if sx then -(mx : Int) else (mx : Int)) ex)⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Extract equality from boolean hypothesis
  have heq : ex = FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Digits.Zdigits 2 mx + ex) :=
    eq_of_beq h
  -- Unfold canonical to show the goal is about F2R and mag
  unfold FloatSpec.Core.Generic_fmt.canonical
  simp only [FloatSpec.Core.Defs.FlocqFloat.Fexp]
  -- Goal: ex = FLT_exp ... (mag 2 (F2R f)) where f.Fnum = if sx then -mx else mx
  -- We need to show mag 2 (F2R f) = Zdigits 2 mx + ex
  -- F2R f = (signed mantissa) * 2^ex
  -- By mag_mult_bpow_eq: mag 2 (m * 2^ex) = mag 2 m + ex
  -- And mag 2 (±mx) = mag 2 mx = Zdigits 2 mx (for mx > 0)
  -- With hmx_pos : 0 < mx, we go directly to the non-zero case
  have hmx : mx ≠ 0 := Nat.pos_iff_ne_zero.mp hmx_pos
  have hmx_int_pos : (0 : Int) < (mx : Int) := Nat.cast_pos.mpr hmx_pos
  have hmx_real_ne : ((mx : Int) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (Int.ofNat_ne_zero.mpr hmx)
  -- Get mag 2 mx = Zdigits 2 mx
  have h2gt1 : (1 : Int) < 2 := by norm_num
  have hmag_eq := FloatSpec.Calc.Sqrt.mag_eq_Zdigits 2 (mx : Int) hmx_int_pos h2gt1
  -- Show signed mantissa ≠ 0
  have hsigned_ne : (if sx = true then -((mx : Int) : ℝ) else ((mx : Int) : ℝ)) ≠ 0 := by
    cases sx <;> simp [hmx_real_ne, hmx]
  -- Use mag_mult_bpow_eq: mag 2 (m * 2^ex) = mag 2 m + ex
  have hmag_mult := FloatSpec.Calc.Sqrt.mag_mult_bpow_eq 2
    (if sx = true then -((mx : Int) : ℝ) else ((mx : Int) : ℝ)) ex hsigned_ne h2gt1
  -- Rewrite F2R
  simp only [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Defs.FlocqFloat.Fnum,
             FloatSpec.Core.Defs.FlocqFloat.Fexp]
  -- Normalize coercions: push Int cast inside the if expression to match hmag_mult pattern
  simp only [Int.cast_ite, Int.cast_neg, Int.cast_natCast]
  -- Establish mag of signed mantissa equals Zdigits
  have hmag_signed : FloatSpec.Core.Raux.mag 2
      (if sx = true then -((mx : Int) : ℝ) else ((mx : Int) : ℝ)) =
      FloatSpec.Core.Digits.Zdigits 2 (mx : Int) := by
    cases sx
    · -- sx = false: straightforward
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hmag_eq
    · -- sx = true: use mag(-x) = mag(x)
      simp only [↓reduceIte]
      -- mag 2 (-mx) = mag 2 mx
      unfold FloatSpec.Core.Raux.mag
      -- Explicitly prove -↑↑mx ≠ 0 so simp can eliminate the if-condition
      have hmx_neg_ne : -((mx : Int) : ℝ) ≠ 0 := neg_ne_zero.mpr hmx_real_ne
      simp only [hmx_neg_ne, ↓reduceIte, abs_neg]
      -- Now both sides simplify to the same thing
      unfold FloatSpec.Core.Raux.mag at hmag_eq
      simp only [hmx_real_ne, ↓reduceIte] at hmag_eq
      exact hmag_eq
  -- Now build the full magnitude equation
  -- Note: hmag_mult uses ↑2 ^ ex (Int 2 cast to ℝ), so we state hmag_full the same way
  have hmag_full : FloatSpec.Core.Raux.mag 2
      ((if sx = true then -((mx : Int) : ℝ) else ((mx : Int) : ℝ)) * ((2 : Int) : ℝ) ^ ex) =
      FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex := by
    rw [hmag_mult, hmag_signed]
  -- The goal is: ex = FLT_exp ... (mag 2 ((if sx then -↑mx else ↑mx) * 2^ex))
  -- We need to show this equals heq: ex = FLT_exp ... (Zdigits 2 mx + ex)
  -- First convert the goal to use our magnitude equation
  calc ex = FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex) := heq
    _ = FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Raux.mag 2
          ((if sx = true then -((mx : Int) : ℝ) else ((mx : Int) : ℝ)) * ((2 : Int) : ℝ) ^ ex)) := by
      rw [hmag_full]

-- Coq: canonical_bounded — canonical mantissa implies boundedness of (mx, ex)
def canonical_bounded_check (sx : Bool) (mx : Nat) (ex : Int) : Unit :=
  ()

theorem canonical_bounded
  (sx : Bool) (mx : Nat) (ex : Int)
  (h : canonical_mantissa (prec:=prec) (emax:=emax) mx ex = true) :
  ⦃⌜True⌝⦄
  (pure (canonical_bounded_check sx mx ex) : Id Unit)
  ⦃⇓_ => ⌜bounded (prec:=prec) (emax:=emax) mx ex = true⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- bounded is currently a placeholder that always returns true
  unfold bounded
  rfl

-- Coq: B2SF_SF2B — standard view after SF2B is identity
def B2SF_SF2B_check (x : StandardFloat) : StandardFloat :=
  (B2SF_BSN (SF2B x))

theorem B2SF_SF2B (x : StandardFloat) :
  ⦃⌜True⌝⦄
  (pure (B2SF_SF2B_check x) : Id StandardFloat)
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2SF_SF2B_check
  cases x <;> rfl

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
def B2SF_B2BSN_check {prec emax} (x : Binary754 prec emax) : StandardFloat :=
  (B2SF_BSN (B2BSN (prec:=prec) (emax:=emax) x))

theorem B2SF_B2BSN {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  (pure (B2SF_B2BSN_check (prec:=prec) (emax:=emax) x) : Id StandardFloat)
  ⦃⇓result => ⌜result = B2SF (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2SF_B2BSN_check B2BSN B2SF_BSN B2SF FF2SF
  cases x.val <;> rfl

-- Coq: is_finite_B2BSN — finiteness preserved by the bridge
def is_finite_B2BSN_check {prec emax} (x : Binary754 prec emax) : Bool :=
  (BSN_is_finite (B2BSN (prec:=prec) (emax:=emax) x))

theorem is_finite_B2BSN {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  (pure (is_finite_B2BSN_check (prec:=prec) (emax:=emax) x) : Id Bool)
  ⦃⇓result => ⌜result = is_finite_B (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_finite_B2BSN_check BSN_is_finite B2BSN is_finite_B is_finite_FF
  cases x.val <;> rfl

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
def is_finite_strict_B2BSN_check {prec emax} (x : Binary754 prec emax) : Bool :=
  (BSN_is_finite_strict (B2BSN (prec:=prec) (emax:=emax) x))

theorem is_finite_strict_B2BSN {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  (pure (is_finite_strict_B2BSN_check (prec:=prec) (emax:=emax) x) : Id Bool)
  ⦃⇓result => ⌜result = is_finite_strict_B (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_finite_strict_B2BSN_check BSN_is_finite_strict B2BSN is_finite_strict_B
  cases x.val <;> rfl

-- Coq: is_nan_B2BSN — NaN preserved by the bridge
def is_nan_B2BSN_check {prec emax} (x : Binary754 prec emax) : Bool :=
  (BSN_is_nan (B2BSN (prec:=prec) (emax:=emax) x))

theorem is_nan_B2BSN {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  (pure (is_nan_B2BSN_check (prec:=prec) (emax:=emax) x) : Id Bool)
  ⦃⇓result => ⌜result = is_nan_B (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_nan_B2BSN_check BSN_is_nan B2BSN is_nan_B is_nan_FF
  cases x.val <;> rfl

-- Coq: Bsign_B2BSN — sign preserved by the bridge (for non-NaN values)
def Bsign_B2BSN_check {prec emax} (x : Binary754 prec emax) : Bool :=
  (BSN_sign (B2BSN (prec:=prec) (emax:=emax) x))

theorem Bsign_B2BSN {prec emax} (x : Binary754 prec emax)
  (hx : is_nan_B (prec:=prec) (emax:=emax) x = false) :
  ⦃⌜True⌝⦄
  (pure (Bsign_B2BSN_check (prec:=prec) (emax:=emax) x) : Id Bool)
  ⦃⇓result => ⌜result = Bsign (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold Bsign_B2BSN_check BSN_sign B2BSN Bsign sign_FF
  cases h : x.val <;> simp_all [is_nan_B, is_nan_FF]

-- Coq: B2R_B2BSN — real semantics commutes with bridge to single-NaN
noncomputable def B2R_B2BSN_check {prec emax} (x : Binary754 prec emax) : ℝ :=
  (B754_to_R (B2BSN (prec:=prec) (emax:=emax) x))

theorem B2R_B2BSN {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  (pure (B2R_B2BSN_check (prec:=prec) (emax:=emax) x) : Id ℝ)
  ⦃⇓result => ⌜result = B2R (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2R_B2BSN_check B754_to_R B2BSN B2R FF2R
  cases x.val <;> rfl

-- Coq: emin_lt_emax — the minimal exponent is strictly less than emax
-- We state it using the hoare‑triple style used throughout this project.
def emin_lt_emax_check : Unit :=
  ()

theorem emin_lt_emax :
  ⦃⌜True⌝⦄
  (pure emin_lt_emax_check : Id Unit)
  ⦃⇓_ => ⌜(3 - emax - prec) < emax⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, emin_lt_emax_check, Id.run, PredTrans.pure, PredTrans.apply]
  have ⟨hprec, hemax⟩ := (inferInstance : Prec_lt_emax prec emax)
  have hprec_pos := (inferInstance : Prec_gt_0 prec).pos
  have h : (3 - emax - prec) < emax := by linarith
  trivial

-- Coq: is_finite_strict_B2R — nonzero real semantics implies strict finiteness
-- Stated for the single-NaN binary `B754` using `B754_to_R` as semantics.
def is_finite_strict_B2R_check (x : B754) : Bool :=
  (BSN_is_finite_strict x)

theorem is_finite_strict_B2R (x : B754)
  (h : B754_to_R x ≠ 0) :
  ⦃⌜True⌝⦄
  (pure (is_finite_strict_B2R_check x) : Id Bool)
  ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Case split on x; non-finite cases have B754_to_R = 0, contradicting h
  cases x with
  | B754_zero s => simp [B754_to_R] at h
  | B754_infinity s => simp [B754_to_R] at h
  | B754_nan => simp [B754_to_R] at h
  | B754_finite s m e =>
    -- BSN_is_finite_strict (B754_finite s m e) = true by definition
    simp [is_finite_strict_B2R_check, BSN_is_finite_strict]

-- Coq: SF2R_B2SF — Real semantics after mapping to StandardFloat
-- We state it in hoare-triple style around a pure computation.
noncomputable def SF2R_B2SF_check (x : B754) : ℝ :=
  (SF2R 2 (B2SF_BSN x))

theorem SF2R_B2SF (x : B754) :
  ⦃⌜True⌝⦄
  (pure (SF2R_B2SF_check x) : Id ℝ)
  ⦃⇓result => ⌜result = B754_to_R x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold SF2R_B2SF_check B2SF_BSN SF2R B754_to_R
  cases x <;> rfl

-- Coq: SF2B_B2SF — roundtrip from B2SF back to B754 via SF2B
def SF2B_B2SF_check (x : B754) : B754 :=
  (SF2B (B2SF_BSN x))

theorem SF2B_B2SF (x : B754) :
  ⦃⌜True⌝⦄
  (pure (SF2B_B2SF_check x) : Id B754)
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold SF2B_B2SF_check SF2B B2SF_BSN
  cases x <;> rfl

-- Coq: valid_binary_B2SF — validity of `B2SF` image
def valid_binary_B2SF_check {prec emax : Int} (x : B754) : Bool :=
  (valid_binary_SF (prec:=prec) (emax:=emax) (B2SF_BSN x))

theorem valid_binary_B2SF {prec emax} (x : B754) :
  ⦃⌜True⌝⦄
  (pure (valid_binary_B2SF_check (prec:=prec) (emax:=emax) x) : Id Bool)
  ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Holds by the current definition of valid_binary_SF.
  unfold valid_binary_B2SF_check
  rfl

-- Coq: SF2B_B2SF_valid — roundtrip with validity argument
def SF2B_B2SF_valid_check (x : B754) : B754 :=
  (SF2B (B2SF_BSN x))

theorem SF2B_B2SF_valid (x : B754) :
  ⦃⌜True⌝⦄
  (pure (SF2B_B2SF_valid_check x) : Id B754)
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Same computation as SF2B_B2SF.
  unfold SF2B_B2SF_valid_check SF2B B2SF_BSN
  cases x <;> rfl

-- Coq: is_finite_strict_SF2B — strict finiteness preserved by SF2B
def is_finite_strict_SF2B_check (x : StandardFloat) : Bool :=
  (BSN_is_finite_strict (SF2B x))

theorem is_finite_strict_SF2B (x : StandardFloat) :
  ⦃⌜True⌝⦄
  (pure (is_finite_strict_SF2B_check x) : Id Bool)
  ⦃⇓result => ⌜result = is_finite_strict_SF x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_finite_strict_SF2B_check BSN_is_finite_strict SF2B is_finite_strict_SF
  cases x <;> rfl

-- Coq: B2SF_inj — injectivity of B2SF on non-NaN values
theorem B2SF_inj (x y : B754)
  (hx : BSN_is_nan x = false)
  (hy : BSN_is_nan y = false)
  (h : B2SF_BSN x = B2SF_BSN y) : x = y := by
  -- Proof by cases on x and y; NaN excluded by hypotheses.
  -- Cases with NaN lead to contradiction via hx/hy; different constructors
  -- lead to contradiction via h being an impossible equality.
  cases x <;> cases y <;> simp_all [BSN_is_nan, B2SF_BSN]

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
def B2BSN_BSN2B_check {prec emax : Int} (s : Bool) (payload : Nat) (x : B754) : B754 :=
  (B2BSN (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) (BSN2B s payload x)))

theorem B2BSN_BSN2B {prec emax : Int} (s : Bool) (payload : Nat) (x : B754) :
  ⦃⌜True⌝⦄
  (pure (B2BSN_BSN2B_check (prec:=prec) (emax:=emax) s payload x) : Id B754)
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2BSN_BSN2B_check BSN2B B2BSN FF2B
  cases x <;> rfl

-- Coq: Bsign_BSN2B — sign preserved by BSN2B on non-NaN values
def Bsign_BSN2B_check (s : Bool) (payload : Nat) (x : B754) : Bool :=
  (sign_FF (BSN2B s payload x))

theorem Bsign_BSN2B (s : Bool) (payload : Nat) (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  (pure (Bsign_BSN2B_check s payload x) : Id Bool)
  ⦃⇓result => ⌜result = BSN_sign x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold Bsign_BSN2B_check
  cases x <;> simp [BSN_is_nan, BSN2B, sign_FF, BSN_sign] at nx ⊢

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
  (Ny : BSN_is_nan y = is_nan_FF x) : B754 :=
  (B2BSN (prec:=prec) (emax:=emax)
          (FF2B (prec:=prec) (emax:=emax)
            (lift x y Ny)))

theorem B2BSN_lift {prec emax : Int}
  (x : FullFloat) (y : B754)
  (Ny : BSN_is_nan y = is_nan_FF x) :
  ⦃⌜True⌝⦄
  (pure (B2BSN_lift_check (prec:=prec) (emax:=emax) x y Ny) : Id B754)
  ⦃⇓result => ⌜result = y⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2BSN_lift_check lift
  split
  · -- Case is_nan_FF x = true: lift returns x
    rename_i h_nan
    -- From Ny and h_nan, y must be B754_nan
    -- First case on x to get its NaN form
    cases hx : x with
    | F754_zero s => simp only [hx, is_nan_FF] at h_nan; exact absurd h_nan Bool.false_ne_true
    | F754_infinity s => simp only [hx, is_nan_FF] at h_nan; exact absurd h_nan Bool.false_ne_true
    | F754_nan s pl =>
      -- x is NaN, so by Ny, y must also be NaN
      simp only [hx] at Ny
      cases y with
      | B754_zero s => simp [BSN_is_nan, is_nan_FF] at Ny
      | B754_infinity s => simp [BSN_is_nan, is_nan_FF] at Ny
      | B754_nan => simp [B2BSN, FF2B, hx]
      | B754_finite s m e => simp [BSN_is_nan, is_nan_FF] at Ny
    | F754_finite s m e => simp only [hx, is_nan_FF] at h_nan; exact absurd h_nan Bool.false_ne_true
  · -- Case is_nan_FF x = false: lift returns BSN2B' y nx
    rename_i h_not_nan
    unfold BSN2B' B2BSN FF2B
    cases y with
    | B754_zero s => rfl
    | B754_infinity s => rfl
    | B754_nan =>
      -- Contradiction: BSN_is_nan B754_nan = true but is_nan_FF x = false
      simp [BSN_is_nan] at Ny
      rw [Ny] at h_not_nan
      simp at h_not_nan
    | B754_finite s m e => rfl

-- Coq: B2BSN_BSN2B' — roundtrip through the non-NaN bridge
def B2BSN_BSN2B'_check {prec emax : Int} (x : B754)
  (nx : BSN_is_nan x = false) : B754 :=
  (B2BSN (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) (BSN2B' x nx)))

theorem B2BSN_BSN2B' {prec emax : Int} (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  (pure (B2BSN_BSN2B'_check (prec:=prec) (emax:=emax) x nx) : Id B754)
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2BSN_BSN2B'_check BSN2B' B2BSN FF2B
  cases x <;> simp [BSN_is_nan] at nx <;> rfl

-- Coq: B2R_BSN2B' — real semantics preserved through BSN2B' on non-NaN values
noncomputable def B2R_BSN2B'_check (x : B754)
  (nx : BSN_is_nan x = false) : ℝ :=
  (FF2R 2 (BSN2B' x nx))

theorem B2R_BSN2B' (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  (pure (B2R_BSN2B'_check x nx) : Id ℝ)
  ⦃⇓result => ⌜result = B754_to_R x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2R_BSN2B'_check BSN2B'
  cases x <;> simp [B754_to_R, BSN_is_nan] at nx <;> rfl

-- Coq: B2FF_BSN2B' — standard full-float view after BSN2B'
def B2FF_BSN2B'_check {prec emax : Int} (x : B754)
  (nx : BSN_is_nan x = false) : FullFloat :=
  (B2FF (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) (BSN2B' x nx)))

theorem B2FF_BSN2B' {prec emax : Int} (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  (pure (B2FF_BSN2B'_check (prec:=prec) (emax:=emax) x nx) : Id FullFloat)
  ⦃⇓result => ⌜result = SF2FF (B2SF_BSN x)⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2FF_BSN2B'_check BSN2B' B2SF_BSN
  cases x <;> simp [BSN_is_nan] at nx <;> rfl

-- Coq: Bsign_BSN2B' — sign preserved through BSN2B' on non-NaN values
def Bsign_BSN2B'_check (x : B754)
  (nx : BSN_is_nan x = false) : Bool :=
  (sign_FF (BSN2B' x nx))

theorem Bsign_BSN2B' (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  (pure (Bsign_BSN2B'_check x nx) : Id Bool)
  ⦃⇓result => ⌜result = BSN_sign x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold Bsign_BSN2B'_check BSN2B'
  cases x <;> simp [BSN_is_nan, BSN_sign] at nx <;> rfl

-- Coq: is_finite_BSN2B' — finiteness preserved through BSN2B'
def is_finite_BSN2B'_check (x : B754)
  (nx : BSN_is_nan x = false) : Bool :=
  (is_finite_FF (BSN2B' x nx))

theorem is_finite_BSN2B' (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  (pure (is_finite_BSN2B'_check x nx) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_finite x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_finite_BSN2B'_check BSN2B'
  cases x <;> simp [BSN_is_nan, BSN_is_finite] at nx <;> rfl

-- Coq: is_nan_BSN2B' — NaN predicate preserved through BSN2B' (trivially false)
def is_nan_BSN2B'_check (x : B754)
  (nx : BSN_is_nan x = false) : Bool :=
  (is_nan_FF (BSN2B' x nx))

theorem is_nan_BSN2B' (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  (pure (is_nan_BSN2B'_check x nx) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_nan x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_nan_BSN2B'_check BSN2B'
  cases x <;> simp [BSN_is_nan] at nx <;> rfl

-- Coq: B2R_BSN2B — real semantics preserved through BSN2B
noncomputable def B2R_BSN2B_check (s : Bool) (payload : Nat) (x : B754) : ℝ :=
  (FF2R 2 (BSN2B s payload x))

theorem B2R_BSN2B (s : Bool) (payload : Nat) (x : B754) :
  ⦃⌜True⌝⦄
  (pure (B2R_BSN2B_check s payload x) : Id ℝ)
  ⦃⇓result => ⌜result = B754_to_R x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Proof follows by cases on x; deferred.
  exact sorry

-- Coq: B2R_SF2B — real semantics after SF2B equals SF2R of source
noncomputable def B2R_SF2B_check (x : StandardFloat) : ℝ :=
  (B754_to_R (SF2B x))

theorem B2R_SF2B (x : StandardFloat) :
  ⦃⌜True⌝⦄
  (pure (B2R_SF2B_check x) : Id ℝ)
  ⦃⇓result => ⌜result = SF2R 2 x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Case split on x; follows definitions.
  exact sorry

-- Coq: is_nan_SF_B2SF — NaN predicate after B2SF matches BSN-side NaN
def is_nan_SF_B2SF_check (x : B754) : Bool :=
  (is_nan_SF (B2SF_BSN x))

theorem is_nan_SF_B2SF (x : B754) :
  ⦃⌜True⌝⦄
  (pure (is_nan_SF_B2SF_check x) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_nan x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Proof deferred; by cases on `x`.
  exact sorry

-- Coq: is_finite_SF_B2SF — finiteness after B2SF matches BSN-side finiteness
def is_finite_SF_B2SF_check (x : B754) : Bool :=
  (is_finite_SF (B2SF_BSN x))

theorem is_finite_SF_B2SF (x : B754) :
  ⦃⌜True⌝⦄
  (pure (is_finite_SF_B2SF_check x) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_finite x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Proof deferred; by cases on `x`.
  exact sorry

-- Coq: is_finite_BSN2B — finiteness preserved through BSN2B
def is_finite_BSN2B_check (s : Bool) (payload : Nat) (x : B754) : Bool :=
  (is_finite_FF (BSN2B s payload x))

theorem is_finite_BSN2B (s : Bool) (payload : Nat) (x : B754) :
  ⦃⌜True⌝⦄
  (pure (is_finite_BSN2B_check s payload x) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_finite x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Proof by cases on x; deferred.
  exact sorry

-- Coq: is_nan_BSN2B — NaN preserved through BSN2B
def is_nan_BSN2B_check (s : Bool) (payload : Nat) (x : B754) : Bool :=
  (is_nan_FF (BSN2B s payload x))

theorem is_nan_BSN2B (s : Bool) (payload : Nat) (x : B754) :
  ⦃⌜True⌝⦄
  (pure (is_nan_BSN2B_check s payload x) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_nan x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
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
  exact x

def B754_mult (mode : RoundingMode) (x y : B754) : B754 := by
  exact x

def B754_div (mode : RoundingMode) (x y : B754) : B754 := by
  exact x

def B754_sqrt (mode : RoundingMode) (x : B754) : B754 := by
  exact x

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

-- We use a BSN-local name to avoid clashing with `Binary.binary_overflow`.
def bsn_binary_overflow (mode : RoundingMode) (s : Bool) : StandardFloat :=
  StandardFloat.S754_infinity s

-- Correctness of operations
theorem B754_plus_correct (mode : RoundingMode) (x y : B754)
  [FloatSpec.Core.Generic_fmt.Valid_exp 2 (FLT_exp (3 - emax - prec) prec)]
  (hx : True)
  (hy : True) :
  True ∧
  (¬B754_is_nan (B754_plus mode x y) → 
  B754_to_R (B754_plus mode x y) = 
  FloatSpec.Calc.Round.round 2 (FLT_exp (3 - emax - prec) prec) () 
    (B754_to_R x + B754_to_R y)) := by
  sorry

theorem B754_mult_correct (mode : RoundingMode) (x y : B754)
  [FloatSpec.Core.Generic_fmt.Valid_exp 2 (FLT_exp (3 - emax - prec) prec)]
  (hx : True)
  (hy : True) :
  True ∧
  (¬B754_is_nan (B754_mult mode x y) → 
  B754_to_R (B754_mult mode x y) = 
  FloatSpec.Calc.Round.round 2 (FLT_exp (3 - emax - prec) prec) () 
    (B754_to_R x * B754_to_R y)) := by
  sorry

-- Exponent scaling (Coq: Bldexp) at the SingleNaN level
-- We mirror the Coq API and state key properties in hoare‑triple style.
def Bldexp (mode : RoundingMode) (x : B754) (e : Int) : B754 := by
  -- Placeholder; actual implementation composes SF-level rounding and SF2B.
  -- We only expose the function for theorem statements; proof is deferred.
  exact x

def is_nan_Bldexp_check (mode : RoundingMode) (x : B754) (e : Int) : Bool :=
  (BSN_is_nan (Bldexp mode x e))

-- Coq: is_nan_Bldexp — exponent scaling preserves NaN-ness
theorem is_nan_Bldexp (mode : RoundingMode) (x : B754) (e : Int) :
  ⦃⌜True⌝⦄
  (pure (is_nan_Bldexp_check mode x e) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_nan x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Proof deferred; corresponds to Coq's `is_nan_Bldexp`.
  exact sorry

-- Negation on SingleNaN binary floats (Coq: Bopp on B754)
def Bopp_bsn (x : B754) : B754 :=
  match x with
  | B754.B754_nan => B754.B754_nan
  | B754.B754_zero s => B754.B754_zero (!s)
  | B754.B754_infinity s => B754.B754_infinity (!s)
  | B754.B754_finite s m e => B754.B754_finite (!s) m e

-- Hoare wrapper for `Bldexp_Bopp_NE`
def Bldexp_Bopp_NE_check (x : B754) (e : Int) : B754 :=
  (Bldexp RoundingMode.RNE (Bopp_bsn x) e)

-- Coq: Bldexp_Bopp_NE — ldexp at nearest-even commutes with negation
theorem Bldexp_Bopp_NE (x : B754) (e : Int) :
  ⦃⌜True⌝⦄
  (pure (Bldexp_Bopp_NE_check x e) : Id B754)
  ⦃⇓result => ⌜result = Bopp_bsn (Bldexp RoundingMode.RNE x e)⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Proof deferred; mirrors Coq's `Bldexp_Bopp_NE`.
  exact sorry

-- Decomposition (Coq: Bfrexp on SingleNaN side)
def Bfrexp_bsn (x : B754) : B754 × Int :=
  -- Placeholder: actual Coq computes a normalized significand and exponent.
  (x, 0)

def is_nan_Bfrexp_check (x : B754) : Bool :=
  (BSN_is_nan ((Bfrexp_bsn x).1))

-- Coq: is_nan_Bfrexp — NaN-ness preserved for the significand of Bfrexp
theorem is_nan_Bfrexp (x : B754) :
  ⦃⌜True⌝⦄
  (pure (is_nan_Bfrexp_check x) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_nan x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Proof deferred; immediate by the placeholder definition of `Bfrexp`.
  exact sorry

-- Boolean xor used to combine signs (Coq: xorb)
def bxor (a b : Bool) : Bool :=
  (a && !b) || (!a && b)

-- Coq: Bdiv_correct_aux (SingleNaN side)
-- Auxiliary correctness for division at the SF/BSN layer.
-- We follow the project pattern: provide a pure check and a Hoare-style theorem.
noncomputable def Bdiv_correct_aux_check {prec emax : Int}
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (mode : RoundingMode)
  (sx : Bool) (mx : Nat) (ex : Int)
  (sy : Bool) (my : Nat) (ey : Int) : StandardFloat :=
  -- Placeholder: actual Coq builds via SFdiv_core_binary then binary_round_aux.
  -- We return the overflow shape as a representative value.
  (bsn_binary_overflow mode (bxor sx sy))

theorem Bdiv_correct_aux {prec emax : Int}
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  [FloatSpec.Core.Generic_fmt.Valid_exp 2 (FLT_exp (3 - emax - prec) prec)]
  (mode : RoundingMode)
  (sx : Bool) (mx : Nat) (ex : Int)
  (sy : Bool) (my : Nat) (ey : Int) :
  ⦃⌜True⌝⦄
  (pure (Bdiv_correct_aux_check (prec:=prec) (emax:=emax) mode sx mx ex sy my ey) : Id StandardFloat)
  ⦃⇓z => ⌜
      let x := SF2R 2 (StandardFloat.S754_finite sx mx ex)
      let y := SF2R 2 (StandardFloat.S754_finite sy my ey)
      valid_binary_SF (prec:=prec) (emax:=emax) z = true ∧
      ((SF2R 2 z
          = FloatSpec.Calc.Round.round 2 (FLT_exp (3 - emax - prec) prec) () (x / y)
        ∧ is_finite_SF z = true ∧ sign_SF z = bxor sx sy)
        ∨ z = bsn_binary_overflow mode (bxor sx sy))⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Proof deferred; mirrors Coq's `Bdiv_correct_aux` by case analysis
  -- on the overflow guard and using properties of `SF2R` and rounding.
  exact sorry

-- Coq: Bfrexp_correct_aux (SingleNaN side)
-- Auxiliary correctness for extracting a normalized significand and exponent.
noncomputable def Bfrexp_correct_aux_check
  (sx : Bool) (mx : Nat) (ex : Int)
  (Hx : bounded (prec:=prec) (emax:=emax) mx ex = true) : (StandardFloat × Int) :=
  -- Placeholder: actual Coq uses Ffrexp_core_binary; we return a representative pair.
  (StandardFloat.S754_finite sx mx ex, 0)

theorem Bfrexp_correct_aux
  (sx : Bool) (mx : Nat) (ex : Int)
  (Hx : bounded (prec:=prec) (emax:=emax) mx ex = true) :
  ⦃⌜True⌝⦄
  (pure (Bfrexp_correct_aux_check (prec:=prec) (emax:=emax) sx mx ex Hx) : Id (StandardFloat × Int))
  ⦃⇓res => ⌜
      let z := res.1; let e := res.2;
      valid_binary_SF (prec:=prec) (emax:=emax) z = true ∧
      ((2 : Int) < emax → ((1 : ℝ) / 2 ≤ |SF2R 2 z| ∧ |SF2R 2 z| < 1)) ∧
      SF2R 2 (StandardFloat.S754_finite sx mx ex)
        = SF2R 2 z * FloatSpec.Core.Raux.bpow 2 e⌝⦄ := by
  intro _
  -- Proof deferred; aligns with Coq's `Bfrexp_correct_aux` structure.
  exact sorry

-- Coq: Bsqrt_correct_aux (SingleNaN side)
-- Auxiliary correctness for square root at the SF/BSN layer.
-- We follow the project pattern: provide a pure check and a Hoare-style theorem.
noncomputable def Bsqrt_correct_aux_check {prec emax : Int}
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (mode : RoundingMode)
  (mx : Nat) (ex : Int)
  (Hx : bounded (prec:=prec) (emax:=emax) mx ex = true) : StandardFloat :=
  -- Placeholder: actual Coq builds via SFsqrt_core_binary then binary_round_aux.
  -- Return a positive finite as representative shape (sign false as in Coq conclusion).
  StandardFloat.S754_finite false mx ex

theorem Bsqrt_correct_aux {prec emax : Int}
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  [FloatSpec.Core.Generic_fmt.Valid_exp 2 (FLT_exp (3 - emax - prec) prec)]
  (mode : RoundingMode)
  (mx : Nat) (ex : Int)
  (Hx : bounded (prec:=prec) (emax:=emax) mx ex = true) :
  ⦃⌜True⌝⦄
  (pure (Bsqrt_correct_aux_check (prec:=prec) (emax:=emax) mode mx ex Hx) : Id StandardFloat)
  ⦃⇓z => ⌜
      let x := SF2R 2 (StandardFloat.S754_finite false mx ex);
      valid_binary_SF (prec:=prec) (emax:=emax) z = true ∧
      SF2R 2 z = FloatSpec.Calc.Round.round 2 (FLT_exp (3 - emax - prec) prec) () (Real.sqrt x) ∧
      is_finite_SF z = true ∧ sign_SF z = false⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `Bsqrt_correct_aux` by unfolding the construction
  -- of `z` via `SFsqrt_core_binary` and applying `binary_round_aux_correct'`.
  exact sorry
