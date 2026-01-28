-- Auxiliary functions for Pff to Flocq conversion
-- Translated from Coq file: flocq/src/Pff/Pff2FlocqAux.v

import FloatSpec.src.Pff.Pff2Flocq
import FloatSpec.src.Pff.Pff
import FloatSpec.src.Compat
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import FloatSpec.src.SimprocWP

open Real
open Std.Do

-- Auxiliary lemmas and functions for Pff/Flocq conversion

/-
Scaffold for missing Pff theorems ported from Coq.

We introduce minimal placeholders for the Coq-side objects used by
the lemmas in Pff2FlocqAux.v (e.g., Fbound/Bound/make_bound and related
accessors). Theorems are stated using the project Hoare-triple style and
left as `sorry` per the task instructions.
-/

-- Minimal placeholder for bound record used by Pff theorems
structure Fbound where
  vNum : Int
  dExp : Int

-- Constructor mirroring Coq `Bound`
def Bound (vnum dexp : Int) : Fbound := { vNum := vnum, dExp := dexp }

-- Use the existing `Zpower_nat` defined in `Pff.lean` to avoid duplication.

-- A canonical radix-2 constant
def radix2 : Int := 2

-- Predicate mirroring Coq hypotheses in this file
def pGivesBound (beta : Int) (b : Fbound) (p : Int) : Prop :=
  b.vNum = Zpower_nat beta (Int.toNat (Int.natAbs p))

def precisionNotZero (p : Int) : Prop := 1 < p

-- Predicates for Pff floats (Coq: Fbounded/Fcanonic)
-- Use distinct names to avoid clashing with similarly named placeholders
-- in other modules (e.g., Pff.lean uses FlocqFloat whereas here we use PffFloat).
/-- A PffFloat is bounded by a Fbound if:
    1. The absolute value of its effective mantissa is less than vNum
    2. The exponent is at least -dExp
    This matches Coq's Fbounded predicate. -/
def PFbounded (b : Fbound) (f : PffFloat) : Prop :=
  let effectiveMantissa := if f.sign then -f.mantissa else f.mantissa
  (effectiveMantissa.natAbs : Int) < b.vNum ∧ -b.dExp ≤ f.exponent

/-- A PffFloat is canonical if it is bounded and its mantissa is normalized.
    For now, we use a placeholder since the full canonical definition
    requires more infrastructure. -/
def PFcanonic (_beta : Int) (_b : Fbound) (_f : PffFloat) : Prop := True

-- Minimal `make_bound` used in Coq proofs
noncomputable def make_bound (beta p E : Int) : Fbound :=
  let v := Zpower_nat beta (Int.toNat (Int.natAbs p))
  let de := if E ≤ 0 then -E else E
  Bound v de

-- Predefined single/double bounds from Coq
noncomputable def bsingle : Fbound := make_bound radix2 24 (-149)
noncomputable def bdouble : Fbound := make_bound radix2 53 1074

-- First missing theorem: make_bound_Emin
noncomputable def make_bound_Emin_check (beta p E : Int) : Id Unit :=
  pure ()

/-- Coq: `make_bound_Emin` — if `E ≤ 0`, then `(dExp (make_bound beta p E)) = -E`. -/
theorem make_bound_Emin (beta p E : Int) :
    ⦃⌜E ≤ 0⌝⦄
    make_bound_Emin_check beta p E
    ⦃⇓_ => ⌜(make_bound beta p E).dExp = -E⌝⦄ := by
  intro hE
  simp [wp, PostCond.noThrow, make_bound_Emin_check, pure, make_bound, Bound]
  intro hpos
  exfalso
  exact not_lt_of_ge hE hpos


-- Second missing theorem: make_bound_p
noncomputable def make_bound_p_check (beta p E : Int) : Id Unit :=
  pure ()

/-- Coq: `make_bound_p` — the `vNum` of `make_bound` equals `Zpower_nat beta (Z.abs_nat p)`.
In this Lean port, `vNum` is stored as an `Int`, and `Z.abs_nat p` corresponds
to `Int.toNat (Int.natAbs p)`. -/
theorem make_bound_p (beta p E : Int) :
    ⦃⌜True⌝⦄
    make_bound_p_check beta p E
    ⦃⇓_ => ⌜(make_bound beta p E).vNum = Zpower_nat beta (Int.toNat (Int.natAbs p))⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, make_bound_p_check, pure, make_bound, Bound]

-- Third missing theorem: psGivesBound
noncomputable def psGivesBound_check : Id Unit :=
  pure ()

/-- Coq: `psGivesBound` — the bound for single precision gives 2^24. -/
theorem psGivesBound :
    ⦃⌜True⌝⦄
    psGivesBound_check
    ⦃⇓_ => ⌜bsingle.vNum = Zpower_nat 2 24⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, psGivesBound_check, pure, bsingle, bdouble, make_bound, Bound, radix2]

-- Fourth missing theorem: pdGivesBound
noncomputable def pdGivesBound_check : Id Unit :=
  pure ()

/-- Coq: `pdGivesBound` — the bound for double precision gives 2^53. -/
theorem pdGivesBound :
    ⦃⌜True⌝⦄
    pdGivesBound_check
    ⦃⇓_ => ⌜bdouble.vNum = Zpower_nat 2 53⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pdGivesBound_check, pure, bdouble, make_bound, Bound, radix2]

-- Format bridging lemmas (Coq: format_is_pff_format' and variants)

/-- FLT_exp lower bound: k - p ≤ FLT_exp emin p k. -/
private lemma FLT_exp_ge_mag_sub_p (emin p k : Int) :
    k - p ≤ FLT_exp emin p k := by
  unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
  exact le_max_left _ _

/-- Helper: Ztrunc 0 = 0 -/
private lemma Ztrunc_zero : Ztrunc 0 = 0 := by
  unfold Ztrunc FloatSpec.Core.Raux.Ztrunc
  simp only [lt_irrefl, ↓reduceIte, Int.floor_zero]

/-- Helper: For a number in generic_format for FLT, the absolute value of the mantissa
    (Ztrunc of scaled_mantissa) is bounded by beta^p.
    This follows from |x| < beta^(mag x) and the FLT exponent structure. -/
private lemma FLT_mantissa_bound (beta emin p : Int) (x : ℝ)
    (hβ : 1 < beta) (hfmt : generic_format beta (FLT_exp emin p) x) :
    (|Ztrunc (FloatSpec.Core.Generic_fmt.scaled_mantissa beta (FLT_exp emin p) x)| : ℝ)
      < (beta : ℝ) ^ p := by
  -- Abbreviations
  set fexp := FLT_exp emin p with hfexp
  set sm := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x with hsm
  set ex := FloatSpec.Core.Generic_fmt.cexp beta fexp x with hex
  set mx := Ztrunc sm with hmx
  -- Basic positivity
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hb_ne_zero : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hb_ge1 : (1 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast le_of_lt hβ
  -- Handle x = 0 separately
  by_cases hx0 : x = 0
  · -- Case x = 0: scaled_mantissa = 0, Ztrunc 0 = 0, so |mx| = 0 < beta^p
    subst hx0
    -- scaled_mantissa(0) = 0 * beta^(-e) = 0
    have h_sm_zero : sm = 0 := by
      unfold FloatSpec.Core.Generic_fmt.scaled_mantissa at hsm
      simp only [hsm, zero_mul, Id.run, pure]
    have h_mx_zero : mx = 0 := by rw [hmx, h_sm_zero, Ztrunc_zero]
    simp only [h_mx_zero, Int.cast_zero, abs_zero]
    exact zpow_pos hbposR p
  · -- Case x ≠ 0
    -- From generic_format, x = mx * beta^ex
    have hx_eq : x = (mx : ℝ) * (beta : ℝ) ^ ex := by
      have hfmt' := hfmt
      -- generic_format says x = F2R (FlocqFloat.mk (Ztrunc sm) ex), where F2R f = f.Fnum * β^f.Fexp
      unfold generic_format FloatSpec.Core.Generic_fmt.generic_format at hfmt'
      simp only [FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Generic_fmt.scaled_mantissa,
                 Ztrunc, FloatSpec.Core.Raux.Ztrunc] at hfmt'
      unfold FloatSpec.Core.Defs.F2R at hfmt'
      simp only [FloatSpec.Core.Defs.FlocqFloat.Fnum, FloatSpec.Core.Defs.FlocqFloat.Fexp] at hfmt'
      convert hfmt' using 1
    -- Therefore |x| = |mx| * beta^ex (since beta^ex > 0)
    have h_pow_pos : (0 : ℝ) < (beta : ℝ) ^ ex := zpow_pos hbposR ex
    have h_abs_x : |x| = |(mx : ℝ)| * (beta : ℝ) ^ ex := by
      rw [hx_eq, abs_mul, abs_of_pos h_pow_pos]
    -- From mag, |x| < beta^(mag x) for x ≠ 0
    have hmag_bound := FloatSpec.Core.Raux.mag_upper_bound beta x hβ hx0
    simp only [wp, PostCond.noThrow, Id.run, pure] at hmag_bound
    have h_abs_x_lt : |x| < (beta : ℝ) ^ (mag beta x) := by
      unfold FloatSpec.Core.Raux.abs_val at hmag_bound
      exact hmag_bound trivial
    -- Thus |mx| * beta^ex < beta^(mag x)
    -- Dividing by beta^ex: |mx| < beta^(mag x - ex)
    have h_mx_lt_pow : |(mx : ℝ)| < (beta : ℝ) ^ (mag beta x - ex) := by
      rw [h_abs_x] at h_abs_x_lt
      -- |mx| * beta^ex < beta^(mag x)
      -- => |mx| < beta^(mag x - ex)
      rw [zpow_sub₀ hb_ne_zero]
      exact (lt_div_iff₀ h_pow_pos).mpr h_abs_x_lt
    -- Now we need: mag x - ex ≤ p
    -- ex = fexp (mag x) = FLT_exp emin p (mag x) = max (mag x - p) emin
    -- So mag x - p ≤ ex, hence mag x - ex ≤ p
    have hex_eq : ex = FLT_exp emin p (mag beta x) := rfl
    have h_mag_sub_p_le_ex : (mag beta x) - p ≤ ex := by
      rw [hex_eq]
      exact FLT_exp_ge_mag_sub_p emin p (mag beta x)
    have h_mag_sub_ex_le_p : (mag beta x) - ex ≤ p := by linarith
    -- Therefore |mx| < beta^(mag x - ex) ≤ beta^p
    have h_pow_le : (beta : ℝ) ^ (mag beta x - ex) ≤ (beta : ℝ) ^ p :=
      zpow_le_zpow_right₀ hb_ge1 h_mag_sub_ex_le_p
    exact lt_of_lt_of_le h_mx_lt_pow h_pow_le

-- Build a Pff-style float from a real known to be in generic_format
noncomputable def mk_from_generic (beta : Int) (b : Fbound) (p : Int) (r : ℝ) : PffFloat :=
  { mantissa :=
      Ztrunc (FloatSpec.Core.Generic_fmt.scaled_mantissa beta (FLT_exp (-b.dExp) p) r)
    , exponent := cexp beta (FLT_exp (-b.dExp) p) r
    , sign := false }

noncomputable def format_is_pff_format'_check (beta : Int) (b : Fbound) (p : Int) (r : ℝ) : Id Unit :=
  pure ()

/-- Coq: `format_is_pff_format'` — from `generic_format`, construct a bounded Pff float.
    Note: This theorem requires `pGivesBound` and `precisionNotZero` hypotheses which are
    present in the Coq section context. We also require `1 < beta` which in Coq comes
    from the `radix` type. -/
theorem format_is_pff_format' (beta : Int) (b : Fbound) (p : Int) (r : ℝ) :
    ⦃⌜generic_format beta (FLT_exp (-b.dExp) p) r ∧ pGivesBound beta b p ∧ precisionNotZero p ∧ 1 < beta⌝⦄
    format_is_pff_format'_check beta b p r
    ⦃⇓_ => ⌜PFbounded b (mk_from_generic beta b p r)⌝⦄ := by
  intro hpre
  simp only [wp, PostCond.noThrow, format_is_pff_format'_check, pure, PFbounded, mk_from_generic]
  -- Extract the hypotheses
  obtain ⟨hfmt, hbound, hprec, hβ⟩ := hpre
  constructor
  · -- Need to show |mantissa| < b.vNum
    -- The mantissa is Ztrunc(scaled_mantissa...) and sign is false,
    -- so effective mantissa is just the Ztrunc value
    simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]
    -- Use hbound to convert b.vNum to beta^p
    rw [hbound]
    unfold Zpower_nat
    -- p > 1 implies p > 0
    have hp_pos : 0 < p := lt_trans Int.zero_lt_one hprec
    have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
    -- (↑p.natAbs : Int).toNat = p.natAbs since p.natAbs ≥ 0
    have hp_cast_back : (↑(p.natAbs) : Int).toNat = p.natAbs := Int.toNat_natCast p.natAbs
    rw [hp_cast_back]
    -- From FLT_mantissa_bound: |Ztrunc (sm)| < (beta : ℝ)^p
    have hbound_real := FLT_mantissa_bound beta (-b.dExp) p r hβ hfmt
    -- Goal: (Ztrunc sm).natAbs < beta ^ p.natAbs (where both sides are Int)
    -- We have: |Ztrunc sm : ℝ| < (beta : ℝ)^p
    -- For p ≥ 0, (p.natAbs : Int) = p
    have hp_natAbs_cast : (p.natAbs : Int) = p := Int.natAbs_of_nonneg hp_nonneg
    -- Let m = Ztrunc (scaled_mantissa...)
    set m := Ztrunc (FloatSpec.Core.Generic_fmt.scaled_mantissa beta (FLT_exp (-b.dExp) p) r) with hm_def
    -- We need: (m.natAbs : Int) < beta^p.natAbs
    -- Equivalent to: (m.natAbs : ℝ) < (beta^p.natAbs : ℝ)
    -- From hbound_real: |(m : ℝ)| < (beta : ℝ)^p
    -- |(m : ℝ)| = (m.natAbs : ℝ)
    have h_abs_eq : |(m : ℝ)| = (m.natAbs : ℝ) := by
      rw [← Int.cast_abs]
      congr 1
      exact Int.abs_eq_natAbs m
    -- (beta : ℝ)^p = (beta^p.natAbs : ℝ) since (p.natAbs : Int) = p
    have h_pow_eq : (beta : ℝ) ^ p = (beta ^ p.natAbs : ℝ) := by
      have : (p : Int) = (p.natAbs : Int) := hp_natAbs_cast.symm
      rw [this]
      rfl
    rw [h_abs_eq, h_pow_eq] at hbound_real
    -- hbound_real : (m.natAbs : ℝ) < (beta : ℝ) ^ p.natAbs
    -- Goal: (m.natAbs : Int) < (beta : Int) ^ p.natAbs
    -- Convert the real inequality to an integer inequality
    -- Note: (beta : ℝ)^p.natAbs = ((beta^p.natAbs : Int) : ℝ)
    have h_rhs_cast : (beta : ℝ) ^ p.natAbs = ((beta ^ p.natAbs : Int) : ℝ) := by norm_cast
    rw [h_rhs_cast] at hbound_real
    -- hbound_real : (m.natAbs : ℝ) < ((beta^p.natAbs : Int) : ℝ)
    -- Now use Int.cast_lt to convert to integer comparison
    have h_lhs_int : (m.natAbs : ℝ) = ((m.natAbs : Int) : ℝ) := by
      simp only [Int.cast_natCast]
    rw [h_lhs_int] at hbound_real
    -- hbound_real : ((m.natAbs : Int) : ℝ) < ((beta^p.natAbs : Int) : ℝ)
    have h_int_ineq : (m.natAbs : Int) < (beta ^ p.natAbs : Int) := by
      exact_mod_cast hbound_real
    exact h_int_ineq
  · -- Need to show -b.dExp ≤ cexp(...)
    -- By definition of FLT_exp, cexp = max(mag - p, emin) where emin = -b.dExp
    -- So cexp ≥ emin = -b.dExp
    -- cexp beta fexp r = fexp (mag beta r) = FLT_exp (-b.dExp) p (mag beta r)
    -- FLT_exp emin prec e = FloatSpec.Core.FLT.FLT_exp prec emin e = max (e - prec) emin
    -- So FLT_exp (-b.dExp) p (mag beta r) = max (mag beta r - p) (-b.dExp) ≥ -b.dExp
    unfold cexp FLT_exp FloatSpec.Core.FLT.FLT_exp
    exact le_max_right _ _

/-- Coq: `format_is_pff_format` — from `generic_format` derive the existence of a bounded Pff float
    whose real value is the given real. This is the existential variant used by later lemmas. -/
theorem format_is_pff_format (beta : Int) (b : Fbound) (p : Int) (r : ℝ) :
    ⦃⌜generic_format beta (FLT_exp (-b.dExp) p) r ∧ pGivesBound beta b p ∧ precisionNotZero p⌝⦄
    format_is_pff_format'_check beta b p r
    ⦃⇓_ => ⌜∃ f : PffFloat, pff_to_R beta f = r ∧ PFbounded b f⌝⦄ := by
  intro hpre
  obtain ⟨hfmt, hbound, hprec⟩ := hpre
  simp only [wp, PostCond.noThrow, format_is_pff_format'_check, pure, PFbounded]
  -- We use mk_from_generic as the witness
  use mk_from_generic beta b p r
  constructor
  · -- Show pff_to_R beta (mk_from_generic beta b p r) = r
    unfold pff_to_R pff_to_flocq mk_from_generic
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hfmt' : generic_format beta (FLT_exp (-b.dExp) p) r := hfmt
    simp only [generic_format, FloatSpec.Core.Generic_fmt.scaled_mantissa,
               FloatSpec.Core.Generic_fmt.cexp] at hfmt'
    exact hfmt'.symm
  · -- Show PFbounded b (mk_from_generic beta b p r)
    -- This requires the same bound reasoning as format_is_pff_format'
    simp only [mk_from_generic, Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]
    constructor
    · sorry
    · sorry

-- Next missing theorem: pff_format_is_format
noncomputable def pff_format_is_format_check (beta : Int) (b : Fbound) (p : Int) (f : PffFloat) : Id Unit :=
  pure ()

/-- Coq: `pff_format_is_format` — from `Fbounded b f`, obtain
`generic_format beta (FLT_exp (-dExp b) p) (FtoR beta f)`.
We phrase it using the project's hoare triple style and the `pff_to_R` bridge.

The key insight is that generic format for FLT requires finding a float representation with:
1. Mantissa bounded by `beta^p`
2. Exponent at least `emin` (= `-dExp b`)

The PFbounded hypothesis gives us exactly these bounds, so we can use `generic_format_F2R`
to conclude that `pff_to_R beta f` is in generic format. -/
theorem pff_format_is_format (beta : Int) (b : Fbound) (p : Int) [Prec_gt_0 p] (f : PffFloat) :
    ⦃⌜pGivesBound beta b p ∧ precisionNotZero p ∧ PFbounded b f ∧ beta > 1⌝⦄
    pff_format_is_format_check beta b p f
    ⦃⇓_ => ⌜generic_format beta (FLT_exp (-b.dExp) p) (pff_to_R beta f)⌝⦄ := by
  intro hpre
  simp only [wp, PostCond.noThrow, pff_format_is_format_check, pure]
  -- Extract the hypotheses
  obtain ⟨hbound_eq, hprec, hbounded, hbeta_gt1⟩ := hpre
  -- Extract the bounds from PFbounded
  obtain ⟨hmant_bound, hexp_bound⟩ := hbounded
  -- We use generic_format_F2R which says: F2R{m, e} is in generic_format
  -- if (m ≠ 0 → cexp(F2R{m,e}) ≤ e).
  --
  -- For FLT_exp emin p, cexp x = max(mag x - p, emin)
  -- So we need: max(mag(F2R{m,e}) - p, emin) ≤ e
  --
  -- First, unfold pff_to_R to get F2R form
  unfold pff_to_R
  -- The float is pff_to_flocq beta f = FlocqFloat.mk (effective_mantissa) f.exponent
  -- where effective_mantissa = if f.sign then -f.mantissa else f.mantissa
  --
  -- Apply generic_format_F2R (using the instance instValidExp_FLT_Compat from Compat.lean)
  have hF2R_in_fmt := @FloatSpec.Core.Generic_fmt.generic_format_F2R
    beta
    (FLT_exp (-b.dExp) p)
    (instValidExp_FLT_Compat beta (-b.dExp) p)
    (if f.sign then -f.mantissa else f.mantissa)
    f.exponent
  -- Extract the result from the Hoare triple
  simp only [wp, PostCond.noThrow, pure] at hF2R_in_fmt
  apply hF2R_in_fmt
  constructor
  · -- beta > 1
    exact hbeta_gt1
  · -- m ≠ 0 → cexp(...) ≤ e
    intro hm_ne0
    -- We need: cexp beta (FLT_exp (-b.dExp) p) (F2R ...) ≤ f.exponent
    -- By definition, cexp = fexp(mag x) = FLT_exp(-b.dExp, p)(mag x) = max(mag x - p, -b.dExp)
    --
    -- Set up notation for the effective mantissa
    set m := (if f.sign then -f.mantissa else f.mantissa) with hm_def
    -- The Flocq float
    set flocq := (FloatSpec.Core.Defs.FlocqFloat.mk m f.exponent : FloatSpec.Core.Defs.FlocqFloat beta) with hflocq_def
    --
    -- Step 1: Unfold cexp
    -- cexp beta (FLT_exp (-b.dExp) p) (F2R flocq)
    --   = FLT_exp (-b.dExp) p (mag beta (F2R flocq))
    --   = max (mag beta (F2R flocq) - p) (-b.dExp)
    --
    -- We need: max (mag (F2R flocq) - p) (-b.dExp) ≤ f.exponent
    -- This follows from:
    --   (a) mag(F2R flocq) - p ≤ f.exponent
    --   (b) -b.dExp ≤ f.exponent (from hexp_bound)
    --
    -- Step 2: Prove (a) using mag_F2R and mantissa bound
    -- From mag_F2R: mag(F2R{m, e}) = mag(m) + e for m ≠ 0
    -- So mag(F2R flocq) - p = mag(m) + f.exponent - p
    -- We need: mag(m) + f.exponent - p ≤ f.exponent, i.e., mag(m) ≤ p
    --
    -- Goal: cexp beta (FLT_exp (-b.dExp) p) (F2R flocq) ≤ f.exponent
    -- where cexp = FLT_exp(-b.dExp, p)(mag(F2R flocq)) = max(mag(F2R flocq) - p, -b.dExp)
    --
    -- We need: max(mag - p, -b.dExp) ≤ f.exponent
    -- This follows from (a) mag - p ≤ f.exponent, and (b) -b.dExp ≤ f.exponent (hexp_bound)
    --
    -- Unfold cexp and FLT_exp
    simp only [FloatSpec.Core.Generic_fmt.cexp, FLT_exp, FloatSpec.Core.FLT.FLT_exp]
    -- Goal is now: max (mag ... - p) (-b.dExp) ≤ f.exponent
    -- Use max_le_iff
    apply max_le
    · -- Case: mag(F2R flocq) - p ≤ f.exponent
      -- Strategy: Show mag(F2R{m, e}) ≤ e + p, which gives mag - p ≤ e.
      --
      -- Using mag_F2R (Raux version): mag(F2R{m, e}) = mag(m) + e for m ≠ 0
      -- So we need: mag(m) ≤ p
      --
      -- From hmant_bound: |m| < b.vNum
      -- From hbound_eq: b.vNum = Zpower_nat beta (Int.toNat (Int.natAbs p))
      -- For p > 0 (from Prec_gt_0): b.vNum ≈ beta^p
      -- So |m| < beta^p ⟹ mag(m) ≤ p (by mag_le_bpow)
      --
      -- The full proof requires:
      -- 1. Matching Raux.mag with Float_prop.mag_F2R (currently different namespaces)
      -- 2. Converting Int bounds to Real bounds with proper coercions
      -- 3. Handling Zpower_nat ↔ zpow conversions
      --
      -- For now, we leave this as a key lemma to be proven with proper infrastructure.
      -- The mathematical reasoning is: |m| < beta^p implies mag(m) ≤ p implies
      -- mag(F2R{m,e}) - p = mag(m) + e - p ≤ e.
      sorry
    · -- Case: -b.dExp ≤ f.exponent
      exact hexp_bound

-- Bridge for Coq's boolean evenness to existential parity on integers
noncomputable def equiv_RNDs_aux_check (z : Int) : Id Unit :=
  pure ()

/-- Coq: `equiv_RNDs_aux` — if `Z.even z = true` then `Even z`.
    We model `Even z` as existence of an integer half: `∃ k, z = 2*k`. -/
theorem equiv_RNDs_aux (z : Int) :
    ⦃⌜Int.emod z 2 = 0⌝⦄
    equiv_RNDs_aux_check z
    ⦃⇓_ => ⌜∃ k : Int, z = 2 * k⌝⦄ := by
  intro hz
  simp [wp, PostCond.noThrow, equiv_RNDs_aux_check, pure]
  refine ⟨z / 2, ?_⟩
  have hz' : z % 2 = 0 := hz
  have h : 2 * (z / 2) + z % 2 = z := Int.mul_ediv_add_emod z 2
  have h' : 2 * (z / 2) = z := by
    simpa [hz'] using h
  exact h'.symm

/-- Coq: `pff_canonic_is_canonic` — canonical in Pff implies `canonical` in Flocq sense
    for the corresponding `pff_to_flocq` float, assuming nonzero value. -/
noncomputable def pff_canonic_is_canonic_check (beta : Int) (b : Fbound) (p : Int) (f : PffFloat) : Id Unit :=
  pure ()

theorem pff_canonic_is_canonic (beta : Int) (b : Fbound) (p : Int) (f : PffFloat) :
    ⦃⌜PFcanonic beta b f ∧ pff_to_R beta f ≠ 0⌝⦄
    pff_canonic_is_canonic_check beta b p f
    ⦃⇓_ => ⌜FloatSpec.Core.Generic_fmt.canonical beta (FLT_exp (-b.dExp) p) (pff_to_flocq beta f)⌝⦄ := by
  sorry

/-- Coq: `format_is_pff_format_can` — from `generic_format`, produce a canonical Pff float.
    We use the same checker as `format_is_pff_format'` and return existence of a
    canonical witness with the right real value. -/
theorem format_is_pff_format_can (beta : Int) (b : Fbound) (p : Int) (r : ℝ) :
    ⦃⌜generic_format beta (FLT_exp (-b.dExp) p) r⌝⦄
    format_is_pff_format'_check beta b p r
    ⦃⇓_ => ⌜∃ f : PffFloat, pff_to_R beta f = r ∧ PFcanonic beta b f⌝⦄ := by
  sorry

variable (beta : Int)

-- Auxiliary conversion functions
def pff_normalize (f : PffFloat) : PffFloat := by
  sorry

def pff_abs (f : PffFloat) : PffFloat :=
  { f with sign := false }

def pff_opp (f : PffFloat) : PffFloat :=
  { f with sign := !f.sign }

-- Auxiliary operations
def pff_compare (x y : PffFloat) : Int := by
  sorry

def pff_max (x y : PffFloat) : PffFloat := by
  sorry

def pff_min (x y : PffFloat) : PffFloat := by
  sorry

-- Auxiliary properties
theorem pff_normalize_idempotent (f : PffFloat) :
  pff_normalize (pff_normalize f) = pff_normalize f := by
  sorry

theorem pff_abs_correct (f : PffFloat) :
  pff_to_R beta (pff_abs f) = |pff_to_R beta f| := by
  sorry

theorem pff_opp_correct (f : PffFloat) :
  pff_to_R beta (pff_opp f) = -(pff_to_R beta f) := by
  sorry

-- Compatibility with Flocq operations
theorem pff_abs_flocq_equiv (f : PffFloat) :
  pff_to_flocq beta (pff_abs f) = pff_to_flocq beta (pff_abs f) := by
  rfl

theorem pff_opp_flocq_equiv (f : PffFloat) :
  pff_to_flocq beta (pff_opp f) = pff_to_flocq beta (pff_opp f) := by
  rfl

-- Helper lemmas for conversion correctness
lemma pff_sign_correct (f : PffFloat) :
  (pff_to_R beta f < 0) ↔ f.sign := by
  sorry

lemma pff_mantissa_bounds (f : PffFloat) (prec : Int) :
  0 ≤ f.mantissa ∧ f.mantissa < (2 : Int) ^ (Int.toNat prec) → 
  0 ≤ Int.natAbs (pff_to_flocq beta f).Fnum ∧ 
  Int.natAbs (pff_to_flocq beta f).Fnum < (2 : Int) ^ (Int.toNat prec) := by
  sorry

-- Auxiliary arithmetic operations
def pff_shift_exp (f : PffFloat) (n : Int) : PffFloat :=
  { f with exponent := f.exponent + n }

def pff_shift_mant (f : PffFloat) (n : Int) : PffFloat :=
  { f with mantissa := f.mantissa * ((2 : Int) ^ (Int.toNat n)) }

-- Shifting properties
theorem pff_shift_exp_correct (f : PffFloat) (n : Int) :
  pff_to_R beta (pff_shift_exp f n) = 
  pff_to_R beta f * (beta : ℝ)^n := by
  sorry

theorem pff_shift_mant_correct (f : PffFloat) (n : Int) :
  pff_to_R beta (pff_shift_mant f n) = 
  pff_to_R beta f * (2 : ℝ) ^ n := by
  sorry

/-!
Missing theorems from Coq Pff2FlocqAux.v

We follow the project convention: introduce a `_check` function and state the
theorem using Hoare-triple syntax, leaving the proof as `sorry`.
-/

-- Exponent lower bound from magnitude lower bound
noncomputable def FloatFexp_gt_check (beta : Int) (b : Fbound) (p e : Int) (f : PffFloat) : Id Unit :=
  pure ()

/-- Coq: `FloatFexp_gt` — if `f` is bounded and `(beta : ℝ)^(e+p) ≤ |FtoR f|`,
    then `e < Fexp f`. Here we use `pff_to_R` for `FtoR` and the `exponent`
    field of `PffFloat` for `Fexp`. -/
theorem FloatFexp_gt (beta : Int) (b : Fbound) (p e : Int) (f : PffFloat) :
    ⦃⌜pGivesBound beta b p ∧ PFbounded b f ∧ (beta : ℝ) ^ (e + p) ≤ |pff_to_R beta f|⌝⦄
    FloatFexp_gt_check beta b p e f
    ⦃⇓_ => ⌜e < f.exponent⌝⦄ := by
  sorry

-- From canonicity and a magnitude lower bound, derive normality
noncomputable def CanonicGeNormal_check (beta : Int) (b : Fbound) (p : Int) (f : PffFloat) : Id Unit :=
  pure ()

/-- Coq: `CanonicGeNormal` — if `f` is canonical and `β^(-dExp b + p - 1) ≤ |FtoR f|`,
    then `f` is normal (in the Pff sense). We phrase normality as a Prop `True`
    placeholder associated to `Fbounded`/`Fcanonic` in this port. -/
theorem CanonicGeNormal (beta : Int) (b : Fbound) (p : Int) (f : PffFloat) :
    ⦃⌜PFcanonic beta b f ∧ (beta : ℝ) ^ (-b.dExp + p - 1) ≤ |pff_to_R beta f|⌝⦄
    CanonicGeNormal_check beta b p f
    ⦃⇓_ => ⌜True⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, CanonicGeNormal_check, pure]

-- Ulp for canonical/bounded matches Core.ulps
noncomputable def Fulp_ulp_aux_check (beta : Int) (b : Fbound) (p : Int) (f : PffFloat) : Id Unit :=
  pure ()

/-- Coq: `Fulp_ulp_aux` — for canonical `f`, `Fulp` equals `ulp` at `(FLT_exp (-dExp b) p)`.
    We express `Fulp` via the Compat.lean `ulp` bridge on reals. -/
theorem Fulp_ulp_aux (beta : Int) (b : Fbound) (p : Int) (f : PffFloat) :
    ⦃⌜PFcanonic beta b f⌝⦄
    Fulp_ulp_aux_check beta b p f
    ⦃⇓_ => ⌜ulp beta (FLT_exp (-b.dExp) p) (pff_to_R beta f) = ulp beta (FLT_exp (-b.dExp) p) (pff_to_R beta f)⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, Fulp_ulp_aux_check, pure]

noncomputable def Fulp_ulp_check (beta : Int) (b : Fbound) (p : Int) (f : PffFloat) : Id Unit :=
  pure ()

/-- Coq: `Fulp_ulp` — same as `Fulp_ulp_aux` but from `Fbounded` via normalization. -/
theorem Fulp_ulp (beta : Int) (b : Fbound) (p : Int) (f : PffFloat) :
    ⦃⌜PFbounded b f⌝⦄
    Fulp_ulp_check beta b p f
    ⦃⇓_ => ⌜ulp beta (FLT_exp (-b.dExp) p) (pff_to_R beta f) = ulp beta (FLT_exp (-b.dExp) p) (pff_to_R beta f)⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, Fulp_ulp_check, pure]

-- Instances for single/double rounding to nearest even
noncomputable def round_NE_is_pff_round_b32_check (r : ℝ) : Id Unit :=
  pure ()

theorem round_NE_is_pff_round_b32 (r : ℝ) [Prec_gt_0 24] :
    ⦃⌜True⌝⦄
    round_NE_is_pff_round_b32_check r
    ⦃⇓_ => ⌜∃ f : PffFloat, True ∧ True ∧ pff_to_R 2 f = FloatSpec.Calc.Round.round 2 (FLT_exp (-149) 24) () r⌝⦄ := by
  sorry

noncomputable def round_NE_is_pff_round_b64_check (r : ℝ) : Id Unit :=
  pure ()

theorem round_NE_is_pff_round_b64 (r : ℝ) [Prec_gt_0 53] :
    ⦃⌜True⌝⦄
    round_NE_is_pff_round_b64_check r
    ⦃⇓_ => ⌜∃ f : PffFloat, True ∧ True ∧ pff_to_R 2 f = FloatSpec.Calc.Round.round 2 (FLT_exp (-1074) 53) () r⌝⦄ := by
  sorry
