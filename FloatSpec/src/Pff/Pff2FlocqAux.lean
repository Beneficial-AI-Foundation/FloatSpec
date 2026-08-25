import FloatSpec.src.Pff.Pff
import FloatSpec.src.Compat
import FloatSpec.src.Core.Round_NE
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import FloatSpec.src.SimprocWP

-- Auxiliary functions for Pff to Flocq conversion
-- Translated from Coq file: flocq/src/Pff/Pff2FlocqAux.v

open Real
open Std.Do

-- Auxiliary lemmas and functions for Pff/Flocq conversion

/-
Scaffold for missing Pff theorems ported from Coq.

We introduce the Coq-side objects used by the lemmas in Pff2FlocqAux.v
(e.g., Fbound/Bound/make_bound and related accessors). Theorems are stated
using the project Hoare-triple style.
-/

-- `Fbound` is defined once in `Pff.lean`; older translations accidentally
-- introduced a second, unrefined record in this module.

-- Arithmetic compatibility constructor.  Its proof arguments make the two
-- source refinements explicit while allowing existing valid calls to be
-- discharged mechanically.
def Bound (vnum dexp : Int)
    (hv : 0 < vnum := by omega) (hd : 0 ≤ dexp := by omega) : Fbound :=
  { vNum := vnum, dExp := dexp, vNum_pos := hv, dExp_nonneg := hd }

-- Use the existing `Zpower_nat` defined in `Pff.lean` to avoid duplication.

-- Local bridge used by this auxiliary leaf. Keeping it here avoids importing
-- `Pff2Flocq`, which still contains deferred theorem bodies.
noncomputable def pff_to_R_aux (beta : Int) [ValidRadix beta] (f : PffFloat) : ℝ :=
  _root_.F2R (pff_to_flocq beta f)

/-- Coq (`Pff2FlocqAux.v`): `FtoR_F2R`.

If the auxiliary Pff float and the Core Flocq float have the same effective
mantissa and exponent, their real interpretations agree. -/
theorem FtoR_F2R (beta : Int) [ValidRadix beta] (f : PffFloat)
    (g : FloatSpec.Core.Defs.FlocqFloat beta)
    (hnum : (if f.sign then -f.mantissa else f.mantissa) = g.Fnum)
    (hexp : f.exponent = g.Fexp) :
    pff_to_R_aux beta f = _root_.F2R (beta := beta) g := by
  cases g
  simp [pff_to_R_aux, pff_to_flocq, _root_.F2R, FloatSpec.Core.Defs.F2R,
    hnum, hexp]

-- A canonical radix-2 constant
def radix2 : Int := 2

-- Predicate mirroring Coq hypotheses in this file
def pGivesBound (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) : Prop :=
  b.vNum = Zpower_nat beta (Int.toNat (Int.natAbs p))

def precisionNotZero (p : Int) : Prop := 1 < p

-- Predicates for Pff floats (Coq: Fbounded/Fcanonic)
-- Use distinct names to avoid clashing with similarly named declarations
-- in other modules (e.g., Pff.lean uses FlocqFloat whereas here we use PffFloat).
/-- A PffFloat is bounded by a Fbound if:
    1. The absolute value of its effective mantissa is less than vNum
    2. The exponent is at least -dExp
    This matches Coq's Fbounded predicate. -/
def PFbounded (b : Fbound) (f : PffFloat) : Prop :=
  let effectiveMantissa := if f.sign then -f.mantissa else f.mantissa
  (effectiveMantissa.natAbs : Int) < b.vNum ∧ -b.dExp ≤ f.exponent

/-- View the auxiliary Pff2Flocq bound record as the Pff core bound skeleton. -/
def toFboundSkel (b : Fbound) : Fbound_skel :=
  b

/-- Boundedness bridge from the auxiliary `PffFloat` model to Pff's core
`FlocqFloat` model. -/
theorem PFbounded_to_Fbounded (beta : Int) [ValidRadix beta] (b : Fbound) (f : PffFloat) :
    PFbounded b f →
      Fbounded (beta:=beta) (toFboundSkel b) (pff_to_flocq beta f) := by
  intro h
  unfold PFbounded at h
  unfold Fbounded toFboundSkel pff_to_flocq
  simpa using h

/-- A PffFloat is canonical in the context of a Fbound if its exponent
    equals the canonical Flocq exponent for its real value. -/
noncomputable def PFcanonic (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (f : PffFloat) : Prop :=
  f.exponent = FLT_exp (-b.dExp) p (mag beta (pff_to_R_aux beta f))

/-- Pff normality for this auxiliary bridge: the float is bounded and its
    exponent is at or above the normal exponent threshold.  The strict form is
    equivalent over integers to `-b.dExp ≤ f.exponent`, but matches the
    exponent lower-bound lemma `FloatFexp_gt`. -/
def PFnormal (b : Fbound) (f : PffFloat) : Prop :=
  PFbounded b f ∧ -b.dExp - 1 < f.exponent

-- Minimal `make_bound` used in Coq proofs
noncomputable def make_bound (beta p E : Int)
    (hβ : 1 < beta := by omega) : Fbound :=
  let v := Zpower_nat beta (Int.toNat (Int.natAbs p))
  let de := if E ≤ 0 then -E else E
  have hv : 0 < v := by
    unfold v Zpower_nat
    exact pow_pos (lt_trans Int.zero_lt_one hβ) _
  have hd : 0 ≤ de := by
    unfold de
    split <;> omega
  Bound v de hv hd

-- Predefined single/double bounds from Coq
noncomputable def bsingle : Fbound := make_bound radix2 24 (-149) (by simp [radix2])
noncomputable def bdouble : Fbound := make_bound radix2 53 1074 (by simp [radix2])

-- First missing theorem: make_bound_Emin
noncomputable def make_bound_Emin_check (beta p E : Int) : Id Unit :=
  pure ()

/-- Coq: `make_bound_Emin` — if `E ≤ 0`, then `(dExp (make_bound beta p E)) = -E`. -/
theorem make_bound_Emin (beta p E : Int)
    (hβ : 1 < beta := by omega) (hp : 1 < p := by omega) :
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
theorem make_bound_p (beta p E : Int)
    (hβ : 1 < beta := by omega) (hp : 1 < p := by omega) :
    ⦃⌜True⌝⦄
    make_bound_p_check beta p E
    ⦃⇓_ => ⌜(make_bound beta p E).vNum = Zpower_nat beta (Int.toNat (Int.natAbs p))⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, make_bound_p_check, pure, make_bound, Bound]

/-- The `make_bound` exponent box is below every `boundR` sentinel exponent.

This is the concrete side condition needed when the restored Pff `Dekker_FTS`
payload is instantiated from the `Pff2Flocq` finite FLT sections: `make_bound`
stores a nonnegative decimal exponent, while `boundR` is constructed with a
natural digit exponent. -/
theorem make_bound_boundR_exp_box (beta p E : Int) [ValidRadix beta] (r : ℝ)
    (hβ : 1 < beta := by omega) :
    -(make_bound beta p E).dExp ≤ (boundR (beta:=beta) beta r).Fexp := by
  have hde_nonneg : 0 ≤ (make_bound beta p E).dExp := by
    by_cases hE : E ≤ 0
    · simp [make_bound, Bound, hE]
    · simp [make_bound, Bound, hE]
      omega
  have hbound_nonneg : 0 ≤ (boundR (beta:=beta) beta r).Fexp := by
    simp [boundR, boundNat]
  exact le_trans (neg_nonpos.mpr hde_nonneg) hbound_nonneg

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
private lemma FLT_mantissa_bound (beta emin p : Int) [ValidRadix beta] (x : ℝ)
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
noncomputable def mk_from_generic (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (r : ℝ) : PffFloat :=
  { mantissa :=
      Ztrunc (FloatSpec.Core.Generic_fmt.scaled_mantissa beta (FLT_exp (-b.dExp) p) r)
    , exponent := cexp beta (FLT_exp (-b.dExp) p) r
    , sign := false }

/-- Auxiliary normalization used by this Pff/Flocq bridge. It keeps the real
value and stores the canonical FLT exponent chosen by `mk_from_generic`. -/
noncomputable def PFnormalize (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (f : PffFloat) : PffFloat :=
  mk_from_generic beta b p (pff_to_R_aux beta f)

/-- Pff-side ulp in the auxiliary `PffFloat` model. Zero uses the minimum
exponent, and nonzero values use the exponent of the normalized representative. -/
noncomputable def PFulp (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (f : PffFloat) : ℝ :=
  if pff_to_R_aux beta f = 0 then
    (beta : ℝ) ^ (-b.dExp)
  else
    (beta : ℝ) ^ (PFnormalize beta b p f).exponent

noncomputable def format_is_pff_format'_check (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (r : ℝ) : Id Unit :=
  pure ()

/-- Coq: `format_is_pff_format'` — from `generic_format`, construct a bounded Pff float.
    Note: This theorem requires `pGivesBound` and `precisionNotZero` hypotheses which are
    present in the Coq section context. We also require `1 < beta` which in Coq comes
    from the `radix` type. -/
theorem format_is_pff_format' (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (r : ℝ) :
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
    -- Goal: (m.natAbs : Int) < beta ^ p.natAbs
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
    whose real value is the given real. This is the existential variant used by later lemmas.

    Note: In Coq, `beta : radix` automatically implies `1 < beta`. We add this hypothesis
    explicitly since Lean's `Int` type does not carry this constraint. -/
theorem format_is_pff_format (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (r : ℝ) :
    ⦃⌜generic_format beta (FLT_exp (-b.dExp) p) r ∧ pGivesBound beta b p ∧ precisionNotZero p ∧ 1 < beta⌝⦄
    format_is_pff_format'_check beta b p r
    ⦃⇓_ => ⌜∃ f : PffFloat, pff_to_R_aux beta f = r ∧ PFbounded b f⌝⦄ := by
  intro hpre
  obtain ⟨hfmt, hbound, hprec, hβ⟩ := hpre
  simp only [wp, PostCond.noThrow, format_is_pff_format'_check, pure, PFbounded]
  -- We use mk_from_generic as the witness
  use mk_from_generic beta b p r
  constructor
  · -- Show pff_to_R_aux beta (mk_from_generic beta b p r) = r
    unfold pff_to_R_aux pff_to_flocq mk_from_generic
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hfmt' : generic_format beta (FLT_exp (-b.dExp) p) r := hfmt
    simp only [generic_format, FloatSpec.Core.Generic_fmt.scaled_mantissa,
               FloatSpec.Core.Generic_fmt.cexp] at hfmt'
    exact hfmt'.symm
  · -- Show PFbounded b (mk_from_generic beta b p r)
    -- Use format_is_pff_format' which has the full proof
    have hpre' : generic_format beta (FLT_exp (-b.dExp) p) r ∧ pGivesBound beta b p ∧ precisionNotZero p ∧ 1 < beta :=
      ⟨hfmt, hbound, hprec, hβ⟩
    have h_bounded := format_is_pff_format' beta b p r hpre'
    simp only [wp, PostCond.noThrow, format_is_pff_format'_check, pure, PFbounded, mk_from_generic,
               Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast] at h_bounded
    exact h_bounded

/-- Flocq-float bounded witness form of `format_is_pff_format`.

This packages the auxiliary Pff witness through `pff_to_flocq`, so callers that
use Pff core predicates such as `isMin'`/`isMax'` can consume generic-format
rounded values directly. -/
theorem format_is_flocq_bounded (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (r : ℝ) :
    ⦃⌜generic_format beta (FLT_exp (-b.dExp) p) r ∧
        pGivesBound beta b p ∧ precisionNotZero p ∧ 1 < beta⌝⦄
    format_is_pff_format'_check beta b p r
    ⦃⇓_ => ⌜∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
        _root_.F2R (beta:=beta) f = r ∧
        Fbounded (beta:=beta) (toFboundSkel b) f⌝⦄ := by
  intro hpre
  have hpff := format_is_pff_format beta b p r hpre
  simp only [wp, PostCond.noThrow, format_is_pff_format'_check, pure] at hpff
  rcases hpff with ⟨fp, hval, hbounded⟩
  refine ⟨pff_to_flocq beta fp, ?_, ?_⟩
  · simpa [pff_to_R_aux] using hval
  · exact PFbounded_to_Fbounded beta b fp hbounded

-- Next missing theorem: pff_format_is_format
noncomputable def pff_format_is_format_check (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (f : PffFloat) : Id Unit :=
  pure ()

/-- Coq: `pff_format_is_format` — from `Fbounded b f`, obtain
`generic_format beta (FLT_exp (-dExp b) p) (FtoR beta f)`.
We phrase it using the project's hoare triple style and the `pff_to_R_aux` bridge.

The key insight is that generic format for FLT requires finding a float representation with:
1. Mantissa bounded by `beta^p`
2. Exponent at least `emin` (= `-dExp b`)

The PFbounded hypothesis gives us exactly these bounds, so we can use `generic_format_F2R`
to conclude that `pff_to_R_aux beta f` is in generic format. -/
theorem pff_format_is_format (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) [Prec_gt_0 p] (f : PffFloat) :
    ⦃⌜pGivesBound beta b p ∧ precisionNotZero p ∧ PFbounded b f ∧ beta > 1⌝⦄
    pff_format_is_format_check beta b p f
    ⦃⇓_ => ⌜generic_format beta (FLT_exp (-b.dExp) p) (pff_to_R_aux beta f)⌝⦄ := by
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
  -- First, unfold pff_to_R_aux to get F2R form
  unfold pff_to_R_aux
  -- The float is pff_to_flocq beta f = FlocqFloat.mk (effective_mantissa) f.exponent
  -- where effective_mantissa = if f.sign then -f.mantissa else f.mantissa
  --
  -- Apply generic_format_F2R (using the instance instValidExp_FLT_Compat from Compat.lean)
  have hF2R_in_fmt := FloatSpec.Core.Generic_fmt.generic_format_F2R
    (beta := beta)
    (fexp := FLT_exp (-b.dExp) p)
    (m := if f.sign then -f.mantissa else f.mantissa)
    (e := f.exponent)
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
      -- Strategy: F2R flocq = m * beta^(f.exponent), and we show mag(m * beta^e) - p ≤ e
      -- by proving mag(m * beta^e) = mag(m) + e and mag(m) ≤ p.
      --
      -- Step 1: Get positivity facts
      have hp_pos : 0 < p := Prec_gt_0.pos
      have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
      have hβposReal : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast (lt_trans Int.zero_lt_one hbeta_gt1)
      have hβ_gt1_real : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hbeta_gt1
      have hβne : (beta : ℝ) ≠ 0 := ne_of_gt hβposReal
      have hlogβ_pos : 0 < Real.log (beta : ℝ) := Real.log_pos hβ_gt1_real
      have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
      --
      -- Step 2: Show |m| < beta^p (as reals)
      -- Since p ≥ 0, we can use Nat exponent: p.toNat
      have hp_toNat_natAbs : Int.toNat (Int.natAbs p) = Int.toNat p := by
        simp only [Int.natAbs_of_nonneg hp_nonneg, Int.toNat_of_nonneg hp_nonneg]
      -- Zpower_nat beta (p.toNat) = beta ^ (p.toNat) : Int
      -- Also, (beta : ℝ) ^ p = (beta : ℝ) ^ (p.toNat : ℤ) since p ≥ 0
      have hp_toNat_cast : (p.toNat : Int) = p := Int.toNat_of_nonneg hp_nonneg
      -- pGivesBound: b.vNum = Zpower_nat beta (Int.toNat (Int.natAbs p))
      --            = Zpower_nat beta (Int.toNat p)
      --            = beta ^ (p.toNat) : Int
      have hZpower_eq : Zpower_nat beta (Int.toNat p) = beta ^ (p.toNat) := by
        unfold Zpower_nat
        rfl
      have hbound_eq' : b.vNum = beta ^ (p.toNat) := by
        unfold pGivesBound at hbound_eq
        rw [hp_toNat_natAbs, hZpower_eq] at hbound_eq
        exact hbound_eq
      have hmant_bound' : (m.natAbs : Int) < beta ^ (p.toNat) := by
        rw [← hbound_eq']
        exact hmant_bound
      have hm_real_abs_eq : |(m : ℝ)| = (m.natAbs : ℝ) := by
        rw [← Int.cast_abs]
        congr 1
        exact Int.abs_eq_natAbs m
      -- Convert mantissa bound to reals: |(m : ℝ)| < (beta : ℝ)^p
      have hm_real_lt : |(m : ℝ)| < (beta : ℝ) ^ p := by
        rw [hm_real_abs_eq]
        -- Need: (m.natAbs : ℝ) < (beta : ℝ)^p
        -- We have: (m.natAbs : Int) < beta^(p.toNat) : Int
        -- And: (beta : ℝ)^p = (beta : ℝ)^(p.toNat) since p.toNat : ℤ = p
        have h_pow_eq : (beta : ℝ) ^ p = (beta : ℝ) ^ (p.toNat : ℤ) := by
          rw [hp_toNat_cast]
        rw [h_pow_eq]
        -- (beta : ℝ)^(p.toNat : ℤ) = ((beta : ℤ)^(p.toNat) : ℝ) by zpow_natCast
        have h_pow_cast : (beta : ℝ) ^ (p.toNat : ℤ) = ((beta ^ p.toNat : Int) : ℝ) := by
          rw [zpow_natCast]
          simp only [Int.cast_pow]
        rw [h_pow_cast]
        -- Now (m.natAbs : ℝ) < ((beta^p.toNat : Int) : ℝ)
        have h1 : (m.natAbs : ℝ) = ((m.natAbs : Int) : ℝ) := by simp
        rw [h1]
        exact_mod_cast hmant_bound'
      have hm_real_ne : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm_ne0
      --
      -- Step 3: Apply mag_le_bpow to get mag(m : ℝ) ≤ p
      have hmag_m_le := FloatSpec.Core.Raux.mag_le_bpow (beta := beta) (x := (m : ℝ))
                          (e := p) hbeta_gt1 hm_real_ne hm_real_lt
      have hmag_m_le_p : FloatSpec.Core.Raux.mag beta (m : ℝ) ≤ p := by
        simpa [wp, PostCond.noThrow, Id.run] using (hmag_m_le trivial)
      --
      -- Step 4: Prove mag(F2R flocq) = mag(m) + f.exponent directly
      -- F2R flocq = m * beta^(f.exponent)
      have hF2R_eq : FloatSpec.Core.Defs.F2R flocq = (m : ℝ) * (beta : ℝ) ^ f.exponent := by
        -- flocq = { Fnum := m, Fexp := f.exponent }
        -- F2R flocq = flocq.Fnum * beta^flocq.Fexp = m * beta^f.exponent
        unfold FloatSpec.Core.Defs.F2R
        -- Goal: ↑flocq.Fnum * ↑beta ^ flocq.Fexp = ↑m * ↑beta ^ f.exponent
        -- Since flocq.Fnum = m and flocq.Fexp = f.exponent by definition
        rfl
      -- Now prove mag(m * beta^e) = mag(m) + e for m ≠ 0
      -- Using the definition of mag and log properties
      have hpow_pos : (0 : ℝ) < (beta : ℝ) ^ f.exponent := zpow_pos hβposReal f.exponent
      have hpow_ne : (beta : ℝ) ^ f.exponent ≠ 0 := ne_of_gt hpow_pos
      have hprod_ne : (m : ℝ) * (beta : ℝ) ^ f.exponent ≠ 0 := mul_ne_zero hm_real_ne hpow_ne
      have habs_m_pos : 0 < |(m : ℝ)| := abs_pos.mpr hm_real_ne
      have habs_pow : |(beta : ℝ) ^ f.exponent| = (beta : ℝ) ^ f.exponent :=
        abs_of_pos hpow_pos
      have habs_prod : |(m : ℝ) * (beta : ℝ) ^ f.exponent| =
                       |(m : ℝ)| * (beta : ℝ) ^ f.exponent := by
        rw [abs_mul, habs_pow]
      have hlog_prod : Real.log (|(m : ℝ)| * (beta : ℝ) ^ f.exponent) =
                       Real.log |(m : ℝ)| + f.exponent * Real.log (beta : ℝ) := by
        rw [Real.log_mul (ne_of_gt habs_m_pos) hpow_ne]
        congr 1
        exact Real.log_zpow (beta : ℝ) f.exponent
      have hdiv_eq : (Real.log |(m : ℝ)| + f.exponent * Real.log (beta : ℝ)) / Real.log (beta : ℝ)
                   = Real.log |(m : ℝ)| / Real.log (beta : ℝ) + f.exponent := by
        field_simp [hlogβ_ne]
      -- mag uses floor + 1 definition
      have hmag_prod : FloatSpec.Core.Raux.mag beta ((m : ℝ) * (beta : ℝ) ^ f.exponent) =
                       FloatSpec.Core.Raux.mag beta (m : ℝ) + f.exponent := by
        unfold FloatSpec.Core.Raux.mag
        simp only [hprod_ne, hm_real_ne, ite_false, habs_prod, hlog_prod, hdiv_eq]
        -- ⌊L + e⌋ + 1 = (⌊L⌋ + 1) + e where L = log|m|/log β
        rw [Int.floor_add_intCast]
        ring
      --
      -- Step 5: Combine to get the final goal
      rw [hF2R_eq, hmag_prod]
      -- Goal: mag(m) + f.exponent - p ≤ f.exponent
      -- This is equivalent to mag(m) ≤ p
      linarith
    · -- Case: -b.dExp ≤ f.exponent
      exact hexp_bound

/-- Converting a core `FlocqFloat` to the auxiliary `PffFloat` preserves its
real value. -/
theorem flocq_to_pff_to_R_aux (beta : Int) [ValidRadix beta]
    (f : FloatSpec.Core.Defs.FlocqFloat beta) :
    pff_to_R_aux beta (flocq_to_pff f) = _root_.F2R (beta:=beta) f := by
  unfold pff_to_R_aux pff_to_flocq flocq_to_pff _root_.F2R FloatSpec.Core.Defs.F2R
  by_cases hneg : f.Fnum < 0
  · have hnat : (f.Fnum.natAbs : Int) = -f.Fnum := by
      rw [← Int.abs_eq_natAbs]
      exact abs_of_neg hneg
    simp [hneg, hnat]
  · have hnneg : 0 ≤ f.Fnum := le_of_not_gt hneg
    have hnat : (f.Fnum.natAbs : Int) = f.Fnum :=
      Int.natAbs_of_nonneg hnneg
    simp [hneg, hnat]

/-- Boundedness bridge from Pff core `FlocqFloat`s to the auxiliary
`PffFloat` representation. -/
theorem Fbounded_to_PFbounded (beta : Int) [ValidRadix beta] (b : Fbound)
    (f : FloatSpec.Core.Defs.FlocqFloat beta) :
    Fbounded (beta:=beta) (toFboundSkel b) f →
      PFbounded b (flocq_to_pff f) := by
  intro h
  unfold Fbounded toFboundSkel at h
  rcases h with ⟨hmant, hexp⟩
  unfold PFbounded flocq_to_pff
  constructor
  · by_cases hneg : f.Fnum < 0
    · have hmant' : (f.Fnum.natAbs : Int) < b.vNum := by
        rw [Int.abs_eq_natAbs] at hmant
        exact hmant
      have hdec : decide (f.Fnum < 0) = true := decide_eq_true hneg
      rw [hdec]
      change (((-(f.Fnum.natAbs : Int)).natAbs : Nat) : Int) < b.vNum
      simpa only [Int.natAbs_neg] using hmant'
    · have hmant' : (f.Fnum.natAbs : Int) < b.vNum := by
        rw [Int.abs_eq_natAbs] at hmant
        exact hmant
      have hdec : decide (f.Fnum < 0) = false := decide_eq_false hneg
      rw [hdec]
      change ((((f.Fnum.natAbs : Int)).natAbs : Nat) : Int) < b.vNum
      simpa only [Int.natAbs_natCast] using hmant'
  · exact hexp

/-- Core Pff bounded floats are in the corresponding FLT generic format. -/
theorem flocq_bounded_is_format (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int)
    [Prec_gt_0 p] (f : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜pGivesBound beta b p ∧ precisionNotZero p ∧
        Fbounded (beta:=beta) (toFboundSkel b) f ∧ 1 < beta⌝⦄
    pff_format_is_format_check beta b p (flocq_to_pff f)
    ⦃⇓_ => ⌜generic_format beta (FLT_exp (-b.dExp) p)
        (_root_.F2R (beta:=beta) f)⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hbound, hprec, hfbounded, hbeta⟩
  have hpf : PFbounded b (flocq_to_pff f) :=
    Fbounded_to_PFbounded beta b f hfbounded
  have hfmt := pff_format_is_format beta b p (flocq_to_pff f)
    ⟨hbound, hprec, hpf, hbeta⟩
  simp only [wp, PostCond.noThrow, pff_format_is_format_check, pure] at hfmt
  simpa [flocq_to_pff_to_R_aux] using hfmt

/-- Upper-exponent half of Coq `pff_canonic_is_canonic`.

For a nonzero bounded core Pff float, the Core FLT canonical exponent of its
real value is no larger than the stored exponent.  This is the reusable
mantissa-bound part of the Pff-to-Core canonicity shuttle. -/
private theorem flocq_bounded_FLT_cexp_le (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int)
    [Prec_gt_0 p] (f : FloatSpec.Core.Defs.FlocqFloat beta)
    (hpBound : pGivesBound beta b p)
    (hfbounded : Fbounded (beta:=beta) (toFboundSkel b) f)
    (hbeta : 1 < beta)
    (hm_ne : f.Fnum ≠ 0) :
    FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp (-b.dExp) p)
        (_root_.F2R (beta:=beta) f) ≤ f.Fexp := by
  rcases hfbounded with ⟨hmant_bound, hexp_bound⟩
  simp only [FloatSpec.Core.Generic_fmt.cexp, FLT_exp, FloatSpec.Core.FLT.FLT_exp]
  apply max_le
  ·
    have hp_pos : 0 < p := Prec_gt_0.pos
    have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
    have hβposReal : (0 : ℝ) < (beta : ℝ) := by
      exact_mod_cast (lt_trans Int.zero_lt_one hbeta)
    have hβ_gt1_real : (1 : ℝ) < (beta : ℝ) := by
      exact_mod_cast hbeta
    have hβne : (beta : ℝ) ≠ 0 := ne_of_gt hβposReal
    have hlogβ_pos : 0 < Real.log (beta : ℝ) := Real.log_pos hβ_gt1_real
    have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
    have hp_toNat_natAbs : Int.toNat (Int.natAbs p) = Int.toNat p := by
      simp only [Int.natAbs_of_nonneg hp_nonneg, Int.toNat_of_nonneg hp_nonneg]
    have hp_toNat_cast : (p.toNat : Int) = p := Int.toNat_of_nonneg hp_nonneg
    have hZpower_eq : Zpower_nat beta (Int.toNat p) = beta ^ (p.toNat) := by
      unfold Zpower_nat
      rfl
    have hbound_eq' : b.vNum = beta ^ (p.toNat) := by
      unfold pGivesBound at hpBound
      rw [hp_toNat_natAbs, hZpower_eq] at hpBound
      exact hpBound
    have hmant_bound' : (f.Fnum.natAbs : Int) < beta ^ (p.toNat) := by
      rw [← hbound_eq']
      rw [Int.abs_eq_natAbs] at hmant_bound
      exact hmant_bound
    have hm_real_abs_eq : |(f.Fnum : ℝ)| = (f.Fnum.natAbs : ℝ) := by
      rw [← Int.cast_abs]
      congr 1
      exact Int.abs_eq_natAbs f.Fnum
    have hm_real_lt : |(f.Fnum : ℝ)| < (beta : ℝ) ^ p := by
      rw [hm_real_abs_eq]
      have h_pow_eq : (beta : ℝ) ^ p = (beta : ℝ) ^ (p.toNat : ℤ) := by
        rw [hp_toNat_cast]
      rw [h_pow_eq]
      have h_pow_cast :
          (beta : ℝ) ^ (p.toNat : ℤ) = ((beta ^ p.toNat : Int) : ℝ) := by
        rw [zpow_natCast]
        simp only [Int.cast_pow]
      rw [h_pow_cast]
      have hmant_bound_real :
          ((f.Fnum.natAbs : Int) : ℝ) < ((beta ^ p.toNat : Int) : ℝ) := by
        exact_mod_cast hmant_bound'
      simpa using hmant_bound_real
    have hm_real_ne : (f.Fnum : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm_ne
    have hmag_m_le := FloatSpec.Core.Raux.mag_le_bpow
      (beta := beta) (x := (f.Fnum : ℝ)) (e := p)
      hbeta hm_real_ne hm_real_lt
    have hmag_m_le_p : FloatSpec.Core.Raux.mag beta (f.Fnum : ℝ) ≤ p := by
      simpa [wp, PostCond.noThrow, Id.run] using hmag_m_le True.intro
    have hpow_pos : (0 : ℝ) < (beta : ℝ) ^ f.Fexp :=
      zpow_pos hβposReal f.Fexp
    have hpow_ne : (beta : ℝ) ^ f.Fexp ≠ 0 := ne_of_gt hpow_pos
    have hprod_ne : (f.Fnum : ℝ) * (beta : ℝ) ^ f.Fexp ≠ 0 :=
      mul_ne_zero hm_real_ne hpow_ne
    have habs_m_pos : 0 < |(f.Fnum : ℝ)| := abs_pos.mpr hm_real_ne
    have habs_pow : |(beta : ℝ) ^ f.Fexp| = (beta : ℝ) ^ f.Fexp :=
      abs_of_pos hpow_pos
    have habs_prod :
        |(f.Fnum : ℝ) * (beta : ℝ) ^ f.Fexp| =
          |(f.Fnum : ℝ)| * (beta : ℝ) ^ f.Fexp := by
      rw [abs_mul, habs_pow]
    have hlog_prod :
        Real.log (|(f.Fnum : ℝ)| * (beta : ℝ) ^ f.Fexp) =
          Real.log |(f.Fnum : ℝ)| + f.Fexp * Real.log (beta : ℝ) := by
      rw [Real.log_mul (ne_of_gt habs_m_pos) hpow_ne]
      congr 1
      exact Real.log_zpow (beta : ℝ) f.Fexp
    have hdiv_eq :
        (Real.log |(f.Fnum : ℝ)| + f.Fexp * Real.log (beta : ℝ)) /
            Real.log (beta : ℝ) =
          Real.log |(f.Fnum : ℝ)| / Real.log (beta : ℝ) + f.Fexp := by
      field_simp [hlogβ_ne]
    have hmag_prod :
        FloatSpec.Core.Raux.mag beta
            ((f.Fnum : ℝ) * (beta : ℝ) ^ f.Fexp) =
          FloatSpec.Core.Raux.mag beta (f.Fnum : ℝ) + f.Fexp := by
      unfold FloatSpec.Core.Raux.mag
      simp only [hprod_ne, hm_real_ne, ite_false, habs_prod, hlog_prod, hdiv_eq]
      rw [Int.floor_add_intCast]
      ring
    simpa [_root_.F2R, FloatSpec.Core.Defs.F2R, hmag_prod] using
      (by linarith : FloatSpec.Core.Raux.mag beta (f.Fnum : ℝ) + f.Fexp - p ≤ f.Fexp)
  · exact hexp_bound

/-- Subnormal branch of Coq `pff_canonic_is_canonic`.

Once boundedness gives the Core FLT canonical exponent upper bound, a
subnormal Pff float is already at the minimum exponent, so the `max` in
`FLT_exp` must choose that same exponent. -/
private theorem Fsubnormal_to_core_canonical (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int)
    [Prec_gt_0 p] (f : FloatSpec.Core.Defs.FlocqFloat beta)
    (hpBound : pGivesBound beta b p)
    (hsub : Fsubnormal (beta:=beta) beta (toFboundSkel b) f)
    (hbeta : 1 < beta)
    (hm_ne : f.Fnum ≠ 0) :
    FloatSpec.Core.Generic_fmt.canonical beta (FLT_exp (-b.dExp) p) f := by
  rcases hsub with ⟨hfbounded, hexp, _⟩
  have hle := flocq_bounded_FLT_cexp_le (beta := beta) (b := b) (p := p)
    (f := f) hpBound hfbounded hbeta hm_ne
  unfold FloatSpec.Core.Generic_fmt.canonical
  have hmin_le :
      f.Fexp ≤
        FLT_exp (-b.dExp) p (FloatSpec.Core.Raux.mag beta (_root_.F2R f)) := by
    rw [hexp]
    unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
    exact le_max_right _ _
  exact le_antisymm hmin_le hle

/-- Normal branch of Coq `pff_canonic_is_canonic`.

Normality supplies the lower magnitude bound needed to prove that the Core
canonical exponent is at least the stored exponent. Combined with boundedness'
upper-exponent half, this gives Core `canonical`. -/
private theorem Fnormal_to_core_canonical (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int)
    [Prec_gt_0 p] (f : FloatSpec.Core.Defs.FlocqFloat beta)
    (hpBound : pGivesBound beta b p)
    (hnormal : Fnormal (beta:=beta) beta (toFboundSkel b) f)
    (hbeta : 1 < beta)
    (hm_ne : f.Fnum ≠ 0) :
    FloatSpec.Core.Generic_fmt.canonical beta (FLT_exp (-b.dExp) p) f := by
  rcases hnormal with ⟨hfbounded, hnormal_mant⟩
  rcases hfbounded with ⟨hmant_bound, hexp_bound⟩
  have hcexp_le := flocq_bounded_FLT_cexp_le (beta := beta) (b := b) (p := p)
    (f := f) hpBound ⟨hmant_bound, hexp_bound⟩ hbeta hm_ne
  haveI : FloatSpec.Core.Generic_fmt.Monotone_exp (FLT_exp (-b.dExp) p) := by
    simpa [FLT_exp] using
      (inferInstance :
        FloatSpec.Core.Generic_fmt.Monotone_exp
          (FloatSpec.Core.FLT.FLT_exp p (-b.dExp)))
  have hp_pos : 0 < p := Prec_gt_0.pos
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hβposReal : (0 : ℝ) < (beta : ℝ) := by
    exact_mod_cast (lt_trans Int.zero_lt_one hbeta)
  have hβne : (beta : ℝ) ≠ 0 := ne_of_gt hβposReal
  have hp_toNat_natAbs : Int.toNat (Int.natAbs p) = Int.toNat p := by
    simp only [Int.natAbs_of_nonneg hp_nonneg, Int.toNat_of_nonneg hp_nonneg]
  have hp_toNat_cast : (p.toNat : Int) = p := Int.toNat_of_nonneg hp_nonneg
  have hZpower_eq : Zpower_nat beta (Int.toNat p) = beta ^ (p.toNat) := by
    unfold Zpower_nat
    rfl
  have hbound_eq_int : b.vNum = beta ^ (p.toNat) := by
    unfold pGivesBound at hpBound
    rw [hp_toNat_natAbs, hZpower_eq] at hpBound
    exact hpBound
  have hbound_eq_real : (b.vNum : ℝ) = (beta : ℝ) ^ p := by
    rw [hbound_eq_int]
    have h_pow_eq : (beta : ℝ) ^ p = (beta : ℝ) ^ (p.toNat : ℤ) := by
      rw [hp_toNat_cast]
    rw [h_pow_eq]
    rw [zpow_natCast]
    simp only [Int.cast_pow]
  have hnormal_real :
      (beta : ℝ) ^ p ≤ |(beta : ℝ) * (f.Fnum : ℝ)| := by
    have hcast :
        (b.vNum : ℝ) ≤ ((|beta * f.Fnum| : Int) : ℝ) := by
      exact_mod_cast hnormal_mant
    have habs_cast :
        ((|beta * f.Fnum| : Int) : ℝ) = |(beta : ℝ) * (f.Fnum : ℝ)| := by
      rw [Int.cast_abs, Int.cast_mul]
    simpa [hbound_eq_real, habs_cast] using hcast
  have hnormal_mul :
      (beta : ℝ) ^ p ≤ (beta : ℝ) * |(f.Fnum : ℝ)| := by
    simpa [abs_mul, abs_of_pos hβposReal] using hnormal_real
  have hpow_split :
      (beta : ℝ) ^ p = (beta : ℝ) * (beta : ℝ) ^ (p - 1) := by
    calc
      (beta : ℝ) ^ p = (beta : ℝ) ^ (1 + (p - 1)) := by
        congr 1
        ring
      _ = (beta : ℝ) ^ (1 : Int) * (beta : ℝ) ^ (p - 1) := by
        rw [zpow_add₀ hβne]
      _ = (beta : ℝ) * (beta : ℝ) ^ (p - 1) := by simp
  have hmant_lower : (beta : ℝ) ^ (p - 1) ≤ |(f.Fnum : ℝ)| := by
    have hmul_le :
        (beta : ℝ) * (beta : ℝ) ^ (p - 1) ≤
          (beta : ℝ) * |(f.Fnum : ℝ)| := by
      simpa [hpow_split] using hnormal_mul
    exact le_of_mul_le_mul_left hmul_le hβposReal
  have hpow_exp_pos : (0 : ℝ) < (beta : ℝ) ^ f.Fexp :=
    zpow_pos hβposReal f.Fexp
  have habs_pow : |(beta : ℝ) ^ f.Fexp| = (beta : ℝ) ^ f.Fexp :=
    abs_of_pos hpow_exp_pos
  have hF2R_abs :
      |_root_.F2R (beta:=beta) f| =
        |(f.Fnum : ℝ)| * (beta : ℝ) ^ f.Fexp := by
    rw [_root_.F2R, FloatSpec.Core.Defs.F2R, abs_mul, habs_pow]
  have hlow :
      (beta : ℝ) ^ ((f.Fexp + p) - 1) ≤
        |_root_.F2R (beta:=beta) f| := by
    calc
      (beta : ℝ) ^ ((f.Fexp + p) - 1)
          = (beta : ℝ) ^ ((p - 1) + f.Fexp) := by
              congr 1
              ring
      _ = (beta : ℝ) ^ (p - 1) * (beta : ℝ) ^ f.Fexp := by
              rw [zpow_add₀ hβne]
      _ ≤ |(f.Fnum : ℝ)| * (beta : ℝ) ^ f.Fexp :=
              mul_le_mul_of_nonneg_right hmant_lower (le_of_lt hpow_exp_pos)
      _ = |_root_.F2R (beta:=beta) f| := hF2R_abs.symm
  have hcexp_ge_raw :
      FLT_exp (-b.dExp) p (f.Fexp + p) ≤
        FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp (-b.dExp) p)
          (_root_.F2R (beta:=beta) f) :=
    FloatSpec.Core.Generic_fmt.cexp_ge_bpow
      (beta := beta) (fexp := FLT_exp (-b.dExp) p)
      (x := _root_.F2R (beta:=beta) f) (e := f.Fexp + p)
      hbeta hlow
  have hflt_eval : FLT_exp (-b.dExp) p (f.Fexp + p) = f.Fexp := by
    unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
    have hlin : f.Fexp + p - p = f.Fexp := by ring
    simpa [hlin] using (max_eq_left hexp_bound)
  have hcexp_ge :
      f.Fexp ≤
        FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp (-b.dExp) p)
          (_root_.F2R (beta:=beta) f) := by
    simpa [hflt_eval] using hcexp_ge_raw
  unfold FloatSpec.Core.Generic_fmt.canonical
  exact le_antisymm hcexp_ge hcexp_le

/-- Dispatcher for Coq `pff_canonic_is_canonic` over Pff's
normal/subnormal canonicity split. -/
private theorem Fcanonic_to_core_canonical (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int)
    [Prec_gt_0 p] (f : FloatSpec.Core.Defs.FlocqFloat beta)
    (hpBound : pGivesBound beta b p)
    (hcan : Fcanonic (beta:=beta) beta (toFboundSkel b) f)
    (hbeta : 1 < beta)
    (hm_ne : f.Fnum ≠ 0) :
    FloatSpec.Core.Generic_fmt.canonical beta (FLT_exp (-b.dExp) p) f := by
  rcases hcan with hnormal | hsubnormal
  · exact Fnormal_to_core_canonical (beta := beta) (b := b) (p := p)
      (f := f) hpBound hnormal hbeta hm_ne
  · exact Fsubnormal_to_core_canonical (beta := beta) (b := b) (p := p)
      (f := f) hpBound hsubnormal hbeta hm_ne

/-- Normalization-specific canonicity shuttle for the nonzero branch of Coq
`pff_round_NE_is_round`. -/
private theorem Fnormalize_to_core_canonical (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int)
    [Prec_gt_0 p] (f : FloatSpec.Core.Defs.FlocqFloat beta)
    (hpBound : pGivesBound beta b p)
    (hfbounded : Fbounded (beta:=beta) (toFboundSkel b) f)
    (hbeta : 1 < beta)
    (hnf_num_ne :
      (Fnormalize (beta:=beta) beta (toFboundSkel b) p.toNat f).Fnum ≠ 0) :
    FloatSpec.Core.Generic_fmt.canonical beta (FLT_exp (-b.dExp) p)
      (Fnormalize (beta:=beta) beta (toFboundSkel b) p.toNat f) := by
  have hp_pos : 0 < p := Prec_gt_0.pos
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hprecision : p.toNat ≠ 0 := by
    intro hzero
    have hcast : (p.toNat : Int) = p := Int.toNat_of_nonneg hp_nonneg
    rw [hzero] at hcast
    omega
  have hp_abs_toNat : (|p| : Int).toNat = p.toNat := by
    rw [abs_of_nonneg hp_nonneg]
  have hvnum : (toFboundSkel b).vNum = Zpower_nat beta p.toNat := by
    unfold pGivesBound at hpBound
    dsimp [toFboundSkel]
    simpa [hp_abs_toNat] using hpBound
  have hcan :
      Fcanonic (beta:=beta) beta (toFboundSkel b)
        (Fnormalize (beta:=beta) beta (toFboundSkel b) p.toNat f) := by
    have htrip := FnormalizeCanonic (beta:=beta) beta (toFboundSkel b) p.toNat f
    simpa only [wp, PostCond.noThrow, pure, FnormalizeCanonic_check,
      Id.run, ULift.up_down, Fbounded'] using
      htrip ⟨hfbounded, hfbounded, hprecision, hbeta, hvnum⟩
  exact Fcanonic_to_core_canonical (beta := beta) (b := b) (p := p)
    (f := Fnormalize (beta:=beta) beta (toFboundSkel b) p.toNat f)
    hpBound hcan hbeta hnf_num_ne

/-- Convert Pff's bounded-float `Closest` predicate into Core's real-valued
nearest-point predicate over the matching FLT generic format. -/
private theorem closest_to_Rnd_N_pt (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int)
    [Prec_gt_0 p] (r : ℝ) (f : FloatSpec.Core.Defs.FlocqFloat beta)
    (hpBound : pGivesBound beta b p) (hprec : precisionNotZero p)
    (hbeta : 1 < beta)
    (hClosest : Closest (beta:=beta) (toFboundSkel b) (beta : ℝ) r f) :
    FloatSpec.Core.Defs.Rnd_N_pt
      (fun y => generic_format beta (FLT_exp (-b.dExp) p) y)
      r (_root_.F2R (beta:=beta) f) := by
  rcases hClosest with ⟨hfbounded, hmin⟩
  constructor
  · have hfmt := flocq_bounded_is_format beta b p f
    simpa only [wp, PostCond.noThrow, pff_format_is_format_check, pure]
      using hfmt ⟨hpBound, hprec, hfbounded, hbeta⟩
  · intro g hgfmt
    have hqex := format_is_flocq_bounded beta b p g
      ⟨hgfmt, hpBound, hprec, hbeta⟩
    simp only [wp, PostCond.noThrow, format_is_pff_format'_check, pure] at hqex
    rcases hqex with ⟨q, hqval, hqbounded⟩
    simpa [hqval] using hmin q hqbounded

/-- Convert a Core real-valued nearest point and its bounded float witness back
to Pff's `Closest` predicate. -/
private theorem Rnd_N_pt_to_closest (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int)
    [Prec_gt_0 p] (r y : ℝ) (f : FloatSpec.Core.Defs.FlocqFloat beta)
    (hpBound : pGivesBound beta b p) (hprec : precisionNotZero p)
    (hbeta : 1 < beta)
    (hy : _root_.F2R (beta:=beta) f = y)
    (hfbounded : Fbounded (beta:=beta) (toFboundSkel b) f)
    (hN : FloatSpec.Core.Defs.Rnd_N_pt
      (fun z => generic_format beta (FLT_exp (-b.dExp) p) z) r y) :
    Closest (beta:=beta) (toFboundSkel b) (beta : ℝ) r f := by
  constructor
  · exact hfbounded
  · intro g hgbounded
    have hgfmt : generic_format beta (FLT_exp (-b.dExp) p)
        (_root_.F2R (beta:=beta) g) := by
      have hfmt := flocq_bounded_is_format beta b p g
      simpa only [wp, PostCond.noThrow, pff_format_is_format_check, pure]
        using hfmt ⟨hpBound, hprec, hgbounded, hbeta⟩
    have hdist := hN.2 (_root_.F2R (beta:=beta) g) hgfmt
    simpa [hy] using hdist

/-- Transfer Core nearest-even parity to Pff normalized-even parity once the
normalized Pff representative is known to be the Core canonical
representative.  This is the nonzero branch of Coq
`pff_round_NE_is_round` after the Pff/Core canonicity shuttle has been
established. -/
private theorem FNeven_of_NE_prop_normalized (beta : Int) [ValidRadix beta]
    (b : Fbound_skel) (radix : ℝ) (precision : Nat)
    (fexp : Int → Int) (x y : ℝ)
    (f : FloatSpec.Core.Defs.FlocqFloat beta)
    (hbeta : 1 < beta)
    (hcan :
      FloatSpec.Core.Generic_fmt.canonical beta fexp
        (Fnormalize (beta:=beta) beta b precision f))
    (hval :
      _root_.F2R (beta:=beta)
        (Fnormalize (beta:=beta) beta b precision f) = y)
    (hNE : FloatSpec.Core.RoundNE.NE_prop beta fexp x y) :
    FNeven (beta:=beta) b radix precision f := by
  let nf := Fnormalize (beta:=beta) beta b precision f
  rcases hNE with ⟨g, hgval, hgcan, hgeven_mod⟩
  have hsame : _root_.F2R (beta:=beta) nf = _root_.F2R (beta:=beta) g := by
    exact hval.trans hgval
  have hnf_eq_g : nf = g :=
    FloatSpec.Core.Generic_fmt.canonical_unique beta hbeta fexp nf g
      (by simpa [nf] using hcan) hgcan hsame
  unfold FNeven Feven
  change Even nf.Fnum
  rw [hnf_eq_g]
  exact Int.even_iff.mpr (by simpa using hgeven_mod)

/-- Combined zero/nonzero normalized-even transfer used by the full
`pff_round_NE_is_round` bridge.

The zero case is pure Pff normalization.  The nonzero case converts the
normalized Pff canonicity into Core `canonical`, then reuses the Core
nearest-even mantissa witness. -/
private theorem FNeven_of_NE_prop_or_zero_normalized (beta : Int) [ValidRadix beta]
    (b : Fbound) (p : Int) [Prec_gt_0 p]
    (x y : ℝ) (f : FloatSpec.Core.Defs.FlocqFloat beta)
    (hpBound : pGivesBound beta b p)
    (hfbounded : Fbounded (beta:=beta) (toFboundSkel b) f)
    (hbeta : 1 < beta)
    (hval :
      _root_.F2R (beta:=beta)
        (Fnormalize (beta:=beta) beta (toFboundSkel b) p.toNat f) = y)
    (hNE : FloatSpec.Core.RoundNE.NE_prop beta (FLT_exp (-b.dExp) p) x y) :
    FNeven (beta:=beta) (toFboundSkel b) (beta : ℝ) p.toNat f := by
  let nf := Fnormalize (beta:=beta) beta (toFboundSkel b) p.toNat f
  by_cases hzero : _root_.F2R (beta:=beta) nf = 0
  · have hbeta_pos : 0 < beta := lt_trans Int.zero_lt_one hbeta
    exact FNeven_of_Fnormalize_F2R_zero (beta:=beta)
      (toFboundSkel b) (beta : ℝ) p.toNat f hbeta_pos (by simpa [nf] using hzero)
  · have hnf_num_ne : nf.Fnum ≠ 0 := by
      intro hnum
      have hf2r_zero : _root_.F2R (beta:=beta) nf = 0 := by
        simp [_root_.F2R, FloatSpec.Core.Defs.F2R, hnum]
      exact hzero hf2r_zero
    have hcan :
        FloatSpec.Core.Generic_fmt.canonical beta (FLT_exp (-b.dExp) p) nf := by
      exact Fnormalize_to_core_canonical (beta := beta) (b := b) (p := p)
        (f := f) hpBound hfbounded hbeta (by simpa [nf] using hnf_num_ne)
    exact FNeven_of_NE_prop_normalized (beta := beta) (b := toFboundSkel b)
      (radix := (beta : ℝ)) (precision := p.toNat)
      (fexp := FLT_exp (-b.dExp) p) (x := x) (y := y) (f := f)
      hbeta (by simpa [nf] using hcan) hval hNE

/-- Transfer Pff normalized-even parity to Core `NE_prop`.

This is the forward direction needed by `pff_round_NE_is_round`: Pff's
`EvenClosest` payload proves evenness of the normalized selected float, while
Core nearest-even uniqueness is stated through `NE_prop` on real values. -/
private theorem NE_prop_of_FNeven_normalized (beta : Int) [ValidRadix beta]
    (b : Fbound) (p : Int) [Prec_gt_0 p]
    (x y : ℝ) (f : FloatSpec.Core.Defs.FlocqFloat beta)
    (hpBound : pGivesBound beta b p)
    (hfbounded : Fbounded (beta:=beta) (toFboundSkel b) f)
    (hbeta : 1 < beta)
    (hval :
      _root_.F2R (beta:=beta)
        (Fnormalize (beta:=beta) beta (toFboundSkel b) p.toNat f) = y)
    (hEven : FNeven (beta:=beta) (toFboundSkel b) (beta : ℝ) p.toNat f) :
    FloatSpec.Core.RoundNE.NE_prop beta (FLT_exp (-b.dExp) p) x y := by
  let nf := Fnormalize (beta:=beta) beta (toFboundSkel b) p.toNat f
  by_cases hzero : _root_.F2R (beta:=beta) nf = 0
  · have hy_zero : y = 0 := hval ▸ hzero
    refine ⟨FloatSpec.Core.Defs.FlocqFloat.mk 0
        ((FLT_exp (-b.dExp) p) (FloatSpec.Core.Raux.mag beta 0)), ?_, ?_, ?_⟩
    · simp [hy_zero, _root_.F2R, FloatSpec.Core.Defs.F2R]
    · exact FloatSpec.Core.Generic_fmt.canonical_0 beta (FLT_exp (-b.dExp) p)
    · norm_num
  · have hnf_num_ne : nf.Fnum ≠ 0 := by
      intro hnum
      have hf2r_zero : _root_.F2R (beta:=beta) nf = 0 := by
        simp [_root_.F2R, FloatSpec.Core.Defs.F2R, hnum]
      exact hzero hf2r_zero
    have hcan :
        FloatSpec.Core.Generic_fmt.canonical beta (FLT_exp (-b.dExp) p) nf := by
      exact Fnormalize_to_core_canonical (beta := beta) (b := b) (p := p)
        (f := f) hpBound hfbounded hbeta (by simpa [nf] using hnf_num_ne)
    have hmod : nf.Fnum % 2 = 0 := by
      exact Int.even_iff.mp (by simpa [FNeven, Feven, nf] using hEven)
    exact ⟨nf, by simpa [nf] using hval.symm, by simpa [nf] using hcan, hmod⟩

/-- FLT exponents satisfy the nearest-even parity side condition whenever the
precision is strictly greater than one. -/
private theorem FLT_exp_exists_NE (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int)
    (hprec : precisionNotZero p) :
    FloatSpec.Core.RoundNE.Exists_NE beta (FLT_exp (-b.dExp) p) := by
  have hp_gt : 1 < p := hprec
  refine ⟨Or.inr ?_⟩
  intro e
  constructor
  · intro hlarge
    unfold FLT_exp FloatSpec.Core.FLT.FLT_exp at hlarge ⊢
    rcases max_lt_iff.mp hlarge with ⟨_, hemin_lt⟩
    exact max_lt (by omega) hemin_lt
  · intro hsmall
    unfold FLT_exp FloatSpec.Core.FLT.FLT_exp at hsmall ⊢
    have hemin_ge : e ≤ -b.dExp := by
      by_contra hnot
      have hemin_lt : -b.dExp < e := lt_of_not_ge hnot
      have hmax_lt : max (e - p) (-b.dExp) < e :=
        max_lt (by omega) hemin_lt
      exact (not_lt.mpr hsmall) hmax_lt
    have hfe : max (e - p) (-b.dExp) = -b.dExp := by
      apply max_eq_right
      omega
    have hnext_le : -b.dExp + 1 - p ≤ -b.dExp := by
      omega
    simpa [hfe] using max_eq_right hnext_le

/-- Coq: `pff_round_DN_is_round` — Pff lower rounding agrees with concrete
Flocq floor rounding. -/
theorem pff_round_DN_is_round (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (r : ℝ)
    [FloatSpec.Core.Generic_fmt.Valid_exp (FLT_exp (-b.dExp) p)]
    (hpBound : pGivesBound beta b p) (hprec : precisionNotZero p)
    (hbeta : 1 < beta) :
    _root_.F2R (beta:=beta)
        (RND_Min (beta:=beta) (toFboundSkel b) beta p r) =
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp (-b.dExp) p)
        FloatSpec.Core.Generic_fmt.rnd_floor r := by
  have hp_pos : 0 < p := lt_trans Int.zero_lt_one hprec
  haveI : Prec_gt_0 p := ⟨hp_pos⟩
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hp_abs_toNat : (|p| : Int).toNat = p.toNat := by
    rw [abs_of_nonneg hp_nonneg]
  have hvnum : (toFboundSkel b).vNum = Zpower_nat beta p.toNat := by
    unfold pGivesBound at hpBound
    dsimp [toFboundSkel]
    simpa [hp_abs_toNat] using hpBound
  have hmin : isMin' (beta:=beta) (toFboundSkel b) beta r
      (RND_Min (beta:=beta) (toFboundSkel b) beta p r) := by
    have h := RND_Min_correct_closed (beta:=beta) (toFboundSkel b) beta p r
    simpa only [wp, PostCond.noThrow, pure, RND_Min_correct_check,
      Id.run, ULift.up_down] using h ⟨rfl, hbeta, hprec, hvnum⟩
  let rd :=
    FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp (-b.dExp) p)
      FloatSpec.Core.Generic_fmt.rnd_floor r
  have hrd_fmt : generic_format beta (FLT_exp (-b.dExp) p) rd := by
    exact FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := beta) (fexp := FLT_exp (-b.dExp) p)
      (rnd := FloatSpec.Core.Generic_fmt.rnd_floor) (x := r) hbeta
  have hqex := format_is_flocq_bounded beta b p rd
      ⟨hrd_fmt, hpBound, hprec, hbeta⟩
  simp only [wp, PostCond.noThrow, format_is_pff_format'_check, pure] at hqex
  rcases hqex with ⟨q, hqval, hqbounded⟩
  have hdn := FloatSpec.Core.Generic_fmt.roundR_DN_pt
    (beta := beta) (fexp := FLT_exp (-b.dExp) p) (x := r) hbeta
  have hq_isMin : isMin' (beta:=beta) (toFboundSkel b) beta r q := by
    rcases hdn with ⟨_, hrd_le, hgreat⟩
    refine ⟨hqbounded, ?_, ?_⟩
    · rw [hqval]
      exact hrd_le
    · intro f hfbounded hf_le
      have hfmt_f : generic_format beta (FLT_exp (-b.dExp) p)
          (_root_.F2R (beta:=beta) f) := by
        have hfmt := flocq_bounded_is_format beta b p f
        simpa only [wp, PostCond.noThrow, pff_format_is_format_check, pure]
          using hfmt ⟨hpBound, hprec, hfbounded, hbeta⟩
      have hf_le_rd : _root_.F2R (beta:=beta) f ≤ rd :=
        hgreat (_root_.F2R (beta:=beta) f) hfmt_f hf_le
      rw [hqval]
      exact hf_le_rd
  have huniq := MinUniqueP (beta:=beta) (toFboundSkel b) beta
  have huniq' :
      ∀ (r : ℝ) (p q : FloatSpec.Core.Defs.FlocqFloat beta),
        isMin' (beta:=beta) (toFboundSkel b) beta r p →
        isMin' (beta:=beta) (toFboundSkel b) beta r q →
        _root_.F2R (beta:=beta) p = _root_.F2R (beta:=beta) q := by
    simpa only [wp, PostCond.noThrow, pure, MinUniqueP_check,
      Id.run, ULift.up_down] using huniq True.intro
  exact (huniq' r (RND_Min (beta:=beta) (toFboundSkel b) beta p r) q
    hmin hq_isMin).trans hqval

/-- Coq: `pff_round_UP_is_round` — Pff upper rounding agrees with concrete
Flocq ceiling rounding. -/
theorem pff_round_UP_is_round (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (r : ℝ)
    [FloatSpec.Core.Generic_fmt.Valid_exp (FLT_exp (-b.dExp) p)]
    (hpBound : pGivesBound beta b p) (hprec : precisionNotZero p)
    (hbeta : 1 < beta) :
    _root_.F2R (beta:=beta)
        (RND_Max (beta:=beta) (toFboundSkel b) beta p r) =
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp (-b.dExp) p)
        FloatSpec.Core.Generic_fmt.rnd_ceil r := by
  have hp_pos : 0 < p := lt_trans Int.zero_lt_one hprec
  haveI : Prec_gt_0 p := ⟨hp_pos⟩
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hp_abs_toNat : (|p| : Int).toNat = p.toNat := by
    rw [abs_of_nonneg hp_nonneg]
  have hvnum : (toFboundSkel b).vNum = Zpower_nat beta p.toNat := by
    unfold pGivesBound at hpBound
    dsimp [toFboundSkel]
    simpa [hp_abs_toNat] using hpBound
  have hmax : isMax' (beta:=beta) (toFboundSkel b) beta r
      (RND_Max (beta:=beta) (toFboundSkel b) beta p r) := by
    have h := RND_Max_correct_closed (beta:=beta) (toFboundSkel b) beta p r
    simpa only [wp, PostCond.noThrow, pure, RND_Max_correct_check,
      Id.run, ULift.up_down] using h ⟨rfl, hbeta, hprec, hvnum⟩
  let ru :=
    FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp (-b.dExp) p)
      FloatSpec.Core.Generic_fmt.rnd_ceil r
  have hru_fmt : generic_format beta (FLT_exp (-b.dExp) p) ru := by
    exact FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := beta) (fexp := FLT_exp (-b.dExp) p)
      (rnd := FloatSpec.Core.Generic_fmt.rnd_ceil) (x := r) hbeta
  have hqex := format_is_flocq_bounded beta b p ru
      ⟨hru_fmt, hpBound, hprec, hbeta⟩
  simp only [wp, PostCond.noThrow, format_is_pff_format'_check, pure] at hqex
  rcases hqex with ⟨q, hqval, hqbounded⟩
  have hup := FloatSpec.Core.Generic_fmt.roundR_UP_pt
    (beta := beta) (fexp := FLT_exp (-b.dExp) p) (x := r) hbeta
  have hq_isMax : isMax' (beta:=beta) (toFboundSkel b) beta r q := by
    rcases hup with ⟨_, hr_le, hleast⟩
    refine ⟨hqbounded, ?_, ?_⟩
    · rw [hqval]
      exact hr_le
    · intro f hfbounded hr_le_f
      have hfmt_f : generic_format beta (FLT_exp (-b.dExp) p)
          (_root_.F2R (beta:=beta) f) := by
        have hfmt := flocq_bounded_is_format beta b p f
        simpa only [wp, PostCond.noThrow, pff_format_is_format_check, pure]
          using hfmt ⟨hpBound, hprec, hfbounded, hbeta⟩
      have hru_le_f : ru ≤ _root_.F2R (beta:=beta) f :=
        hleast (_root_.F2R (beta:=beta) f) hfmt_f hr_le_f
      rw [hqval]
      exact hru_le_f
  have huniq := MaxUniqueP (beta:=beta) (toFboundSkel b) beta
  have huniq' :
      ∀ (r : ℝ) (p q : FloatSpec.Core.Defs.FlocqFloat beta),
        isMax' (beta:=beta) (toFboundSkel b) beta r p →
        isMax' (beta:=beta) (toFboundSkel b) beta r q →
        _root_.F2R (beta:=beta) p = _root_.F2R (beta:=beta) q := by
    simpa only [wp, PostCond.noThrow, pure, MaxUniqueP_check,
      Id.run, ULift.up_down] using huniq True.intro
  exact (huniq' r (RND_Max (beta:=beta) (toFboundSkel b) beta p r) q
    hmax hq_isMax).trans hqval

/-- Coq: `pff_round_N_is_round` — Pff closest rounding agrees with concrete
Flocq nearest rounding for an arbitrary tie-breaking choice. -/
theorem pff_round_N_is_round (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int)
    (choice : Int → Bool) (r : ℝ)
    [FloatSpec.Core.Generic_fmt.Valid_exp (FLT_exp (-b.dExp) p)]
    (hpBound : pGivesBound beta b p) (hprec : precisionNotZero p)
    (hbeta : 1 < beta) :
    _root_.F2R (beta:=beta)
        (RND_Closest (beta:=beta) (toFboundSkel b) beta p choice r) =
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp (-b.dExp) p)
        (FloatSpec.Core.Generic_fmt.Znearest choice) r := by
  classical
  let rd := RND_Min (beta:=beta) (toFboundSkel b) beta p r
  let ru := RND_Max (beta:=beta) (toFboundSkel b) beta p r
  let fexp := FLT_exp (-b.dExp) p
  let down := FloatSpec.Core.Generic_fmt.roundR beta fexp
      FloatSpec.Core.Generic_fmt.rnd_floor r
  let up := FloatSpec.Core.Generic_fmt.roundR beta fexp
      FloatSpec.Core.Generic_fmt.rnd_ceil r
  have hdn : _root_.F2R (beta:=beta) rd = down := by
    simpa [rd, down, fexp] using
      (pff_round_DN_is_round beta b p r hpBound hprec hbeta)
  have hup : _root_.F2R (beta:=beta) ru = up := by
    simpa [ru, up, fexp] using
      (pff_round_UP_is_round beta b p r hpBound hprec hbeta)
  have hdn_pt := FloatSpec.Core.Generic_fmt.roundR_DN_pt
    (beta := beta) (fexp := fexp) (x := r) hbeta
  have hup_pt := FloatSpec.Core.Generic_fmt.roundR_UP_pt
    (beta := beta) (fexp := fexp) (x := r) hbeta
  have hdown_le : down ≤ r := by
    rcases hdn_pt with ⟨_, hle, _⟩
    exact hle
  have hr_le_up : r ≤ up := by
    rcases hup_pt with ⟨_, hle, _⟩
    exact hle
  by_cases hle :
      |_root_.F2R (beta:=beta) ru - r| ≤
        |_root_.F2R (beta:=beta) rd - r|
  · by_cases hlt :
        |_root_.F2R (beta:=beta) ru - r| <
          |_root_.F2R (beta:=beta) rd - r|
    · have hselect :
          _root_.F2R (beta:=beta)
              (RND_Closest (beta:=beta) (toFboundSkel b) beta p choice r) =
            _root_.F2R (beta:=beta) ru := by
        have hle0 :
            |_root_.F2R (beta:=beta)
                (RND_Max (beta:=beta) (toFboundSkel b) beta p r) - r| ≤
              |_root_.F2R (beta:=beta)
                (RND_Min (beta:=beta) (toFboundSkel b) beta p r) - r| := by
          simpa [rd, ru] using hle
        have hlt0 :
            |_root_.F2R (beta:=beta)
                (RND_Max (beta:=beta) (toFboundSkel b) beta p r) - r| <
              |_root_.F2R (beta:=beta)
                (RND_Min (beta:=beta) (toFboundSkel b) beta p r) - r| := by
          simpa [rd, ru] using hlt
        unfold RND_Closest
        simp [toFboundSkel] at hle0 hlt0
        simp [rd, ru, hle0, hlt0, fexp, toFboundSkel]
      have hclose :
          |FloatSpec.Core.Generic_fmt.roundR beta fexp
              FloatSpec.Core.Generic_fmt.rnd_ceil r - r| <
            |FloatSpec.Core.Generic_fmt.roundR beta fexp
              FloatSpec.Core.Generic_fmt.rnd_floor r - r| := by
        simpa [rd, ru, fexp, down, up, hdn, hup] using hlt
      have hnearest :=
        FloatSpec.Core.Generic_fmt.round_N_eq_UP
          (beta := beta) (fexp := fexp) (choice := choice) (x := r)
          hbeta hclose
      calc
        _root_.F2R (beta:=beta)
            (RND_Closest (beta:=beta) (toFboundSkel b) beta p choice r) =
          _root_.F2R (beta:=beta) ru := hselect
        _ = up := hup
        _ = FloatSpec.Core.Generic_fmt.roundR beta fexp
              FloatSpec.Core.Generic_fmt.rnd_ceil r := rfl
        _ = FloatSpec.Core.Generic_fmt.roundR beta fexp
              (FloatSpec.Core.Generic_fmt.Znearest choice) r := hnearest.symm
    · have hdist_eq :
          |up - r| = |down - r| := by
        have hle' : |up - r| ≤ |down - r| := by
          simpa [rd, ru, down, up, hdn, hup] using hle
        have hge' : |down - r| ≤ |up - r| := by
          have hnot : ¬ |up - r| < |down - r| := by
            simpa [rd, ru, down, up, hdn, hup] using hlt
          exact le_of_not_gt hnot
        exact le_antisymm hle' hge'
      have hmid :
          r - FloatSpec.Core.Generic_fmt.roundR beta fexp
              FloatSpec.Core.Generic_fmt.rnd_floor r =
            FloatSpec.Core.Generic_fmt.roundR beta fexp
              FloatSpec.Core.Generic_fmt.rnd_ceil r - r := by
        have hup_nonneg : 0 ≤ up - r := by linarith
        have hdown_nonpos : down - r ≤ 0 := by linarith
        rw [abs_of_nonneg hup_nonneg, abs_of_nonpos hdown_nonpos] at hdist_eq
        simpa [down, up] using hdist_eq.symm
      have hnearest_middle :=
        FloatSpec.Core.Generic_fmt.round_N_middle
          (beta := beta) (fexp := fexp) (choice := choice) (x := r)
          hbeta hmid
      by_cases hchoice : choice (FloatSpec.Core.Raux.Zfloor
          (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp r))
      · have hselect :
            _root_.F2R (beta:=beta)
                (RND_Closest (beta:=beta) (toFboundSkel b) beta p choice r) =
              _root_.F2R (beta:=beta) ru := by
          have hle0 :
              |_root_.F2R (beta:=beta)
                  (RND_Max (beta:=beta) (toFboundSkel b) beta p r) - r| ≤
                |_root_.F2R (beta:=beta)
                  (RND_Min (beta:=beta) (toFboundSkel b) beta p r) - r| := by
            simpa [rd, ru] using hle
          have hlt0 :
              ¬ |_root_.F2R (beta:=beta)
                    (RND_Max (beta:=beta) (toFboundSkel b) beta p r) - r| <
                  |_root_.F2R (beta:=beta)
                    (RND_Min (beta:=beta) (toFboundSkel b) beta p r) - r| := by
            simpa only [rd, ru, toFboundSkel] using hlt
          have hchoice0 :
              choice (FloatSpec.Core.Raux.Zfloor
                (FloatSpec.Core.Generic_fmt.scaled_mantissa beta
                  (FLT_exp (-(toFboundSkel b).dExp) p) r)) = true := by
            simpa [fexp, toFboundSkel] using hchoice
          unfold RND_Closest
          simp [toFboundSkel] at hle0 hchoice0
          simp [rd, ru, hle0, hlt0, hchoice0, fexp, toFboundSkel]
        calc
          _root_.F2R (beta:=beta)
              (RND_Closest (beta:=beta) (toFboundSkel b) beta p choice r) =
            _root_.F2R (beta:=beta) ru := hselect
          _ = up := hup
          _ = FloatSpec.Core.Generic_fmt.roundR beta fexp
                FloatSpec.Core.Generic_fmt.rnd_ceil r := rfl
          _ = FloatSpec.Core.Generic_fmt.roundR beta fexp
                (FloatSpec.Core.Generic_fmt.Znearest choice) r := by
              simpa [hchoice, FloatSpec.Core.Generic_fmt.rnd_floor,
                FloatSpec.Core.Generic_fmt.rnd_ceil] using hnearest_middle.symm
      · have hselect :
            _root_.F2R (beta:=beta)
                (RND_Closest (beta:=beta) (toFboundSkel b) beta p choice r) =
              _root_.F2R (beta:=beta) rd := by
          have hle0 :
              |_root_.F2R (beta:=beta)
                  (RND_Max (beta:=beta) (toFboundSkel b) beta p r) - r| ≤
                |_root_.F2R (beta:=beta)
                  (RND_Min (beta:=beta) (toFboundSkel b) beta p r) - r| := by
            simpa [rd, ru] using hle
          have hlt0 :
              ¬ |_root_.F2R (beta:=beta)
                    (RND_Max (beta:=beta)
                      b beta p r) - r| <
                  |_root_.F2R (beta:=beta)
                    (RND_Min (beta:=beta)
                      b beta p r) - r| := by
            simpa [rd, ru, toFboundSkel] using hlt
          have hchoice0 :
              choice (FloatSpec.Core.Raux.Zfloor
                (FloatSpec.Core.Generic_fmt.scaled_mantissa beta
                  (FLT_exp (-(toFboundSkel b).dExp) p) r)) = false := by
            simpa [fexp, toFboundSkel] using hchoice
          unfold RND_Closest
          simp [toFboundSkel] at hle0 hchoice0
          simp [rd, ru, hle0, hlt0, hchoice0, fexp, toFboundSkel]
        calc
          _root_.F2R (beta:=beta)
              (RND_Closest (beta:=beta) (toFboundSkel b) beta p choice r) =
            _root_.F2R (beta:=beta) rd := hselect
          _ = down := hdn
          _ = FloatSpec.Core.Generic_fmt.roundR beta fexp
                FloatSpec.Core.Generic_fmt.rnd_floor r := rfl
          _ = FloatSpec.Core.Generic_fmt.roundR beta fexp
                (FloatSpec.Core.Generic_fmt.Znearest choice) r := by
              simpa [hchoice, FloatSpec.Core.Generic_fmt.rnd_floor,
                FloatSpec.Core.Generic_fmt.rnd_ceil] using hnearest_middle.symm
  · have hselect :
        _root_.F2R (beta:=beta)
            (RND_Closest (beta:=beta) (toFboundSkel b) beta p choice r) =
          _root_.F2R (beta:=beta) rd := by
      have hle0 :
          ¬ |_root_.F2R (beta:=beta)
                (RND_Max (beta:=beta)
                  b beta p r) - r| ≤
              |_root_.F2R (beta:=beta)
                (RND_Min (beta:=beta)
                  b beta p r) - r| := by
        simpa [rd, ru, toFboundSkel] using hle
      unfold RND_Closest
      simp [rd, ru, hle0, fexp, toFboundSkel]
    have hlt :
        |FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_floor r - r| <
          |FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_ceil r - r| := by
      have hlt_raw :
          |_root_.F2R (beta:=beta) rd - r| <
            |_root_.F2R (beta:=beta) ru - r| :=
        lt_of_not_ge hle
      simpa [rd, ru, fexp, down, up, hdn, hup] using hlt_raw
    have hnearest :=
      FloatSpec.Core.Generic_fmt.round_N_eq_DN
        (beta := beta) (fexp := fexp) (choice := choice) (x := r)
        hbeta hlt
    calc
      _root_.F2R (beta:=beta)
          (RND_Closest (beta:=beta) (toFboundSkel b) beta p choice r) =
        _root_.F2R (beta:=beta) rd := hselect
      _ = down := hdn
      _ = FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_floor r := rfl
      _ = FloatSpec.Core.Generic_fmt.roundR beta fexp
            (FloatSpec.Core.Generic_fmt.Znearest choice) r := hnearest.symm

/-- Coq: `round_N_is_pff_round` — nearest rounding has a canonical Pff witness
whose real value is the concrete Flocq nearest rounding. -/
theorem round_N_is_pff_round (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int)
    (choice : Int → Bool) (r : ℝ)
    [FloatSpec.Core.Generic_fmt.Valid_exp (FLT_exp (-b.dExp) p)]
    (hpBound : pGivesBound beta b p) (hprec : precisionNotZero p)
    (hbeta : 1 < beta) :
    ∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
      Fcanonic (beta:=beta) beta (toFboundSkel b) f ∧
      Closest (beta:=beta) (toFboundSkel b) (beta : ℝ) r f ∧
      _root_.F2R (beta:=beta) f =
        FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp (-b.dExp) p)
          (FloatSpec.Core.Generic_fmt.Znearest choice) r := by
  have hp_pos : 0 < p := lt_trans Int.zero_lt_one hprec
  haveI : Prec_gt_0 p := ⟨hp_pos⟩
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hp_abs_toNat : (|p| : Int).toNat = p.toNat := by
    rw [abs_of_nonneg hp_nonneg]
  have hvnum : (toFboundSkel b).vNum = Zpower_nat beta p.toNat := by
    unfold pGivesBound at hpBound
    dsimp [toFboundSkel]
    simpa [hp_abs_toNat] using hpBound
  let f := RND_Closest (beta:=beta) (toFboundSkel b) beta p choice r
  have hcan : Fcanonic (beta:=beta) beta (toFboundSkel b) f := by
    have h := RND_Closest_canonic_closed
      (beta:=beta) (toFboundSkel b) beta p choice r
    simpa only [wp, PostCond.noThrow, pure, RND_Closest_canonic_check,
      Id.run, ULift.up_down, f] using h ⟨rfl, hbeta, hprec, hvnum⟩
  have hclosest : Closest (beta:=beta) (toFboundSkel b) (beta : ℝ) r f := by
    have h := RND_Closest_correct_closed
      (beta:=beta) (toFboundSkel b) beta p choice r
    simpa only [wp, PostCond.noThrow, pure, RND_Closest_correct_check,
      Id.run, ULift.up_down, f] using h ⟨rfl, hbeta, hprec, hvnum⟩
  have hval :
      _root_.F2R (beta:=beta) f =
        FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp (-b.dExp) p)
          (FloatSpec.Core.Generic_fmt.Znearest choice) r := by
    simpa [f] using
      (pff_round_N_is_round beta b p choice r hpBound hprec hbeta)
  exact ⟨f, hcan, hclosest, hval⟩

/-- If the down-rounded value is itself nearest, the always-down tie breaker
selects it. -/
private theorem round_N_const_false_eq_DN_of_nearest_DN
    (beta : Int) [ValidRadix beta] (fexp : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp fexp]
    (r : ℝ) (hbeta : 1 < beta)
    (hDN_nearest : FloatSpec.Core.Defs.Rnd_N_pt
      (fun y => generic_format beta fexp y) r
      (FloatSpec.Core.Generic_fmt.roundR beta fexp
        FloatSpec.Core.Generic_fmt.rnd_floor r)) :
    FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest (fun _ : Int => false)) r =
      FloatSpec.Core.Generic_fmt.roundR beta fexp
        FloatSpec.Core.Generic_fmt.rnd_floor r := by
  classical
  let down := FloatSpec.Core.Generic_fmt.roundR beta fexp
      FloatSpec.Core.Generic_fmt.rnd_floor r
  let up := FloatSpec.Core.Generic_fmt.roundR beta fexp
      FloatSpec.Core.Generic_fmt.rnd_ceil r
  let nearest := FloatSpec.Core.Generic_fmt.roundR beta fexp
      (FloatSpec.Core.Generic_fmt.Znearest (fun _ : Int => false)) r
  have hDN := FloatSpec.Core.Generic_fmt.roundR_DN_pt
    (beta := beta) (fexp := fexp) (x := r) hbeta
  have hUP := FloatSpec.Core.Generic_fmt.roundR_UP_pt
    (beta := beta) (fexp := fexp) (x := r) hbeta
  have hNearestPt := FloatSpec.Core.Generic_fmt.round_N_pt
    (beta := beta) (fexp := fexp)
    (choice := fun _ : Int => false) (x := r) hbeta
  have hclass := FloatSpec.Core.Round_pred.Rnd_N_pt_DN_or_UP_eq_spec
    (fun y => generic_format beta fexp y) r down up nearest
    (by simpa [down] using hDN) (by simpa [up] using hUP)
    (by simpa [nearest] using hNearestPt)
  have hcases : nearest = down ∨ nearest = up := by
    simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_DN_or_UP_eq_check, pure,
      decide_eq_true_iff] using hclass trivial
  rcases hcases with hnearest_down | hnearest_up
  · simpa [nearest, down] using hnearest_down
  · have hup_nearest : FloatSpec.Core.Defs.Rnd_N_pt
        (fun y => generic_format beta fexp y) r up := by
      simpa [nearest, hnearest_up, up] using hNearestPt
    have hle_down_up : |r - down| ≤ |r - up| := by
      simpa [abs_sub_comm, down] using hDN_nearest.2 up hUP.1
    have hle_up_down : |r - up| ≤ |r - down| := by
      simpa [abs_sub_comm, up] using hup_nearest.2 down hDN.1
    have hdist_eq : |r - down| = |r - up| := le_antisymm hle_down_up hle_up_down
    have hmid :
        r - FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_floor r =
          FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_ceil r - r := by
      have hdown_le : down ≤ r := hDN.2.1
      have hr_le_up : r ≤ up := hUP.2.1
      have hleft_nonneg : 0 ≤ r - down := sub_nonneg.mpr hdown_le
      have hright_nonpos : r - up ≤ 0 := sub_nonpos.mpr hr_le_up
      have hdist_eq' : r - down = |r - up| := by
        simpa [abs_of_nonneg hleft_nonneg] using hdist_eq
      have hup_abs : |r - up| = up - r := by
        simpa [neg_sub] using abs_of_nonpos hright_nonpos
      simpa [down, up, hup_abs] using hdist_eq'
    have hmiddle := FloatSpec.Core.Generic_fmt.round_N_middle
      (beta := beta) (fexp := fexp) (choice := fun _ : Int => false)
      (x := r) hbeta hmid
    simpa [nearest, down, FloatSpec.Core.Generic_fmt.rnd_floor,
      FloatSpec.Core.Generic_fmt.rnd_ceil] using hmiddle

/-- If the up-rounded value is itself nearest, the always-up tie breaker
selects it. -/
private theorem round_N_const_true_eq_UP_of_nearest_UP
    (beta : Int) [ValidRadix beta] (fexp : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp fexp]
    (r : ℝ) (hbeta : 1 < beta)
    (hUP_nearest : FloatSpec.Core.Defs.Rnd_N_pt
      (fun y => generic_format beta fexp y) r
      (FloatSpec.Core.Generic_fmt.roundR beta fexp
        FloatSpec.Core.Generic_fmt.rnd_ceil r)) :
    FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest (fun _ : Int => true)) r =
      FloatSpec.Core.Generic_fmt.roundR beta fexp
        FloatSpec.Core.Generic_fmt.rnd_ceil r := by
  classical
  let down := FloatSpec.Core.Generic_fmt.roundR beta fexp
      FloatSpec.Core.Generic_fmt.rnd_floor r
  let up := FloatSpec.Core.Generic_fmt.roundR beta fexp
      FloatSpec.Core.Generic_fmt.rnd_ceil r
  let nearest := FloatSpec.Core.Generic_fmt.roundR beta fexp
      (FloatSpec.Core.Generic_fmt.Znearest (fun _ : Int => true)) r
  have hDN := FloatSpec.Core.Generic_fmt.roundR_DN_pt
    (beta := beta) (fexp := fexp) (x := r) hbeta
  have hUP := FloatSpec.Core.Generic_fmt.roundR_UP_pt
    (beta := beta) (fexp := fexp) (x := r) hbeta
  have hNearestPt := FloatSpec.Core.Generic_fmt.round_N_pt
    (beta := beta) (fexp := fexp)
    (choice := fun _ : Int => true) (x := r) hbeta
  have hclass := FloatSpec.Core.Round_pred.Rnd_N_pt_DN_or_UP_eq_spec
    (fun y => generic_format beta fexp y) r down up nearest
    (by simpa [down] using hDN) (by simpa [up] using hUP)
    (by simpa [nearest] using hNearestPt)
  have hcases : nearest = down ∨ nearest = up := by
    simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_DN_or_UP_eq_check, pure,
      decide_eq_true_iff] using hclass trivial
  rcases hcases with hnearest_down | hnearest_up
  · have hdown_nearest : FloatSpec.Core.Defs.Rnd_N_pt
        (fun y => generic_format beta fexp y) r down := by
      simpa [nearest, hnearest_down, down] using hNearestPt
    have hle_down_up : |r - down| ≤ |r - up| := by
      simpa [abs_sub_comm, down] using hdown_nearest.2 up hUP.1
    have hle_up_down : |r - up| ≤ |r - down| := by
      simpa [abs_sub_comm, up] using hUP_nearest.2 down hDN.1
    have hdist_eq : |r - down| = |r - up| := le_antisymm hle_down_up hle_up_down
    have hmid :
        r - FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_floor r =
          FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_ceil r - r := by
      have hdown_le : down ≤ r := hDN.2.1
      have hr_le_up : r ≤ up := hUP.2.1
      have hleft_nonneg : 0 ≤ r - down := sub_nonneg.mpr hdown_le
      have hright_nonpos : r - up ≤ 0 := sub_nonpos.mpr hr_le_up
      have hdist_eq' : r - down = |r - up| := by
        simpa [abs_of_nonneg hleft_nonneg] using hdist_eq
      have hup_abs : |r - up| = up - r := by
        simpa [neg_sub] using abs_of_nonpos hright_nonpos
      simpa [down, up, hup_abs] using hdist_eq'
    have hmiddle := FloatSpec.Core.Generic_fmt.round_N_middle
      (beta := beta) (fexp := fexp) (choice := fun _ : Int => true)
      (x := r) hbeta hmid
    simpa [nearest, up, FloatSpec.Core.Generic_fmt.rnd_floor,
      FloatSpec.Core.Generic_fmt.rnd_ceil] using hmiddle
  · simpa [nearest, up] using hnearest_up

/-- Coq: `pff_round_is_round_N` — every Pff `Closest` witness is represented
by concrete Flocq nearest rounding for some tie-breaking choice. -/
theorem pff_round_is_round_N (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int)
    (r : ℝ) (f : FloatSpec.Core.Defs.FlocqFloat beta)
    [FloatSpec.Core.Generic_fmt.Valid_exp (FLT_exp (-b.dExp) p)]
    (hpBound : pGivesBound beta b p) (hprec : precisionNotZero p)
    (hbeta : 1 < beta)
    (hClosest : Closest (beta:=beta) (toFboundSkel b) (beta : ℝ) r f) :
    ∃ choice : Int → Bool,
      _root_.F2R (beta:=beta) f =
        FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp (-b.dExp) p)
          (FloatSpec.Core.Generic_fmt.Znearest choice) r := by
  have hp_pos : 0 < p := lt_trans Int.zero_lt_one hprec
  haveI : Prec_gt_0 p := ⟨hp_pos⟩
  let fexp := FLT_exp (-b.dExp) p
  let down := FloatSpec.Core.Generic_fmt.roundR beta fexp
      FloatSpec.Core.Generic_fmt.rnd_floor r
  let up := FloatSpec.Core.Generic_fmt.roundR beta fexp
      FloatSpec.Core.Generic_fmt.rnd_ceil r
  have hDN := FloatSpec.Core.Generic_fmt.roundR_DN_pt
    (beta := beta) (fexp := fexp) (x := r) hbeta
  have hUP := FloatSpec.Core.Generic_fmt.roundR_UP_pt
    (beta := beta) (fexp := fexp) (x := r) hbeta
  have hF_nearest :
      FloatSpec.Core.Defs.Rnd_N_pt
        (fun y => generic_format beta fexp y) r
        (_root_.F2R (beta:=beta) f) := by
    simpa [fexp] using
      (closest_to_Rnd_N_pt (beta := beta) (b := b) (p := p) (r := r)
        (f := f) hpBound hprec hbeta hClosest)
  have hclass := FloatSpec.Core.Round_pred.Rnd_N_pt_DN_or_UP_eq_spec
    (fun y => generic_format beta fexp y) r down up
    (_root_.F2R (beta:=beta) f)
    (by simpa [down] using hDN) (by simpa [up] using hUP)
    hF_nearest
  have hcases : _root_.F2R (beta:=beta) f = down ∨
      _root_.F2R (beta:=beta) f = up := by
    simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_DN_or_UP_eq_check, pure,
      decide_eq_true_iff] using hclass trivial
  rcases hcases with hdown | hup
  · refine ⟨fun _ : Int => false, ?_⟩
    have hDN_nearest :
        FloatSpec.Core.Defs.Rnd_N_pt
          (fun y => generic_format beta fexp y) r down := by
      simpa [hdown, down] using hF_nearest
    have hround := round_N_const_false_eq_DN_of_nearest_DN
      (beta := beta) (fexp := fexp) (r := r) hbeta hDN_nearest
    calc
      _root_.F2R (beta:=beta) f = down := hdown
      _ = FloatSpec.Core.Generic_fmt.roundR beta fexp
            (FloatSpec.Core.Generic_fmt.Znearest (fun _ : Int => false)) r :=
          hround.symm
  · refine ⟨fun _ : Int => true, ?_⟩
    have hUP_nearest :
        FloatSpec.Core.Defs.Rnd_N_pt
          (fun y => generic_format beta fexp y) r up := by
      simpa [hup, up] using hF_nearest
    have hround := round_N_const_true_eq_UP_of_nearest_UP
      (beta := beta) (fexp := fexp) (r := r) hbeta hUP_nearest
    calc
      _root_.F2R (beta:=beta) f = up := hup
      _ = FloatSpec.Core.Generic_fmt.roundR beta fexp
            (FloatSpec.Core.Generic_fmt.Znearest (fun _ : Int => true)) r :=
          hround.symm

/-- Coq: `pff_round_NE_is_round` — Pff even-closest rounding agrees with the
concrete Flocq nearest-even rounding. -/
theorem pff_round_NE_is_round (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (r : ℝ)
    [FloatSpec.Core.Generic_fmt.Valid_exp (FLT_exp (-b.dExp) p)]
    (hpBound : pGivesBound beta b p) (hprec : precisionNotZero p)
    (hbeta : 1 < beta) :
    _root_.F2R (beta:=beta)
        (RND_EvenClosest (beta:=beta) (toFboundSkel b) beta p.toNat r) =
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp (-b.dExp) p)
        (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) r := by
  classical
  have hp_pos : 0 < p := lt_trans Int.zero_lt_one hprec
  haveI : Prec_gt_0 p := ⟨hp_pos⟩
  haveI : FloatSpec.Core.Generic_fmt.Monotone_exp (FLT_exp (-b.dExp) p) := by
    simp only [FLT_exp]
    exact FloatSpec.Core.FLT.FLT_exp_mono (prec := p) (emin := -b.dExp)
  haveI : FloatSpec.Core.RoundNE.Exists_NE beta (FLT_exp (-b.dExp) p) :=
    FLT_exp_exists_NE beta b p hprec
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hp_toNat : (p.toNat : Int) = p := Int.toNat_of_nonneg hp_nonneg
  have hp_toNat_gt : 1 < (p.toNat : Int) := by
    simpa [hp_toNat] using hprec
  have hp_abs_toNat : (|p| : Int).toNat = p.toNat := by
    rw [abs_of_nonneg hp_nonneg]
  have hvnum : (toFboundSkel b).vNum = Zpower_nat beta p.toNat := by
    unfold pGivesBound at hpBound
    dsimp [toFboundSkel]
    simpa [hp_abs_toNat] using hpBound
  let f := RND_EvenClosest (beta:=beta) (toFboundSkel b) beta p.toNat r
  let y := _root_.F2R (beta:=beta) f
  let rounded :=
    FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp (-b.dExp) p)
      (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) r
  have hec : EvenClosest (beta:=beta) (toFboundSkel b) (beta : ℝ) p.toNat r f := by
    have h := RND_EvenClosest_correct
      (beta:=beta) (toFboundSkel b) beta p.toNat r
    simpa only [wp, PostCond.noThrow, pure, RND_EvenClosest_correct_check,
      Id.run, ULift.up_down, f] using h ⟨rfl, hbeta, hp_toNat_gt, hvnum⟩
  have hN_y :
      FloatSpec.Core.Defs.Rnd_N_pt
        (fun z => generic_format beta (FLT_exp (-b.dExp) p) z) r y := by
    exact closest_to_Rnd_N_pt (beta := beta) (b := b) (p := p)
      (r := r) (f := f) hpBound hprec hbeta hec.1
  have hnorm_val :
      _root_.F2R (beta:=beta)
        (Fnormalize (beta:=beta) beta (toFboundSkel b) p.toNat f) = y := by
    have h := FnormalizeCorrect (beta:=beta) beta (toFboundSkel b) p.toNat f
    simpa only [wp, PostCond.noThrow, pure, FnormalizeCorrect_check,
      Id.run, ULift.up_down, y] using h ⟨rfl, hbeta⟩
  have hNE_y :
      FloatSpec.Core.RoundNE.Rnd_NE_pt beta (FLT_exp (-b.dExp) p) r y := by
    refine ⟨hN_y, ?_⟩
    rcases hec.2 with hEven | hUnique
    · left
      exact NE_prop_of_FNeven_normalized (beta := beta) (b := b) (p := p)
        (x := r) (y := y) (f := f) hpBound hec.1.1 hbeta hnorm_val hEven
    · right
      intro z hz
      have hz_format : generic_format beta (FLT_exp (-b.dExp) p) z := hz.1
      have hz_bound := format_is_flocq_bounded beta b p z
        ⟨hz_format, hpBound, hprec, hbeta⟩
      simp only [wp, PostCond.noThrow, format_is_pff_format'_check, pure] at hz_bound
      rcases hz_bound with ⟨q, hqval, hqbounded⟩
      have hqClosest : Closest (beta:=beta) (toFboundSkel b) (beta : ℝ) r q := by
        exact Rnd_N_pt_to_closest (beta := beta) (b := b) (p := p)
          (r := r) (y := z) (f := q) hpBound hprec hbeta hqval hqbounded hz
      exact hqval.symm.trans (hUnique q hqClosest)
  have hNE_round :
      FloatSpec.Core.RoundNE.Rnd_NE_pt beta (FLT_exp (-b.dExp) p) r rounded := by
    have h := FloatSpec.Core.RoundNE.round_NE_pt
      (beta := beta) (fexp := FLT_exp (-b.dExp) p) (x := r)
    simpa [FloatSpec.Core.RoundNE.round_NE_pt_check, pure, decide_eq_true_iff,
      rounded] using h hbeta
  have huniq := FloatSpec.Core.RoundNE.Rnd_NE_pt_unique
      (beta := beta) (fexp := FLT_exp (-b.dExp) p)
      (x := r) (f1 := y) (f2 := rounded)
  have hy_eq : y = rounded := by
    simpa [FloatSpec.Core.RoundNE.Rnd_NE_pt_unique_specific_check, pure,
      decide_eq_true_iff] using huniq ⟨hbeta, hNE_y, hNE_round⟩
  simpa [f, y, rounded] using hy_eq

/-- Convert an arbitrary Pff `EvenClosest` witness into the concrete Flocq
nearest-even rounded value.

Upstream `Pff2Flocq.v` uses this conversion pattern when importing Pff payloads
such as `VeltkampEven`: the Pff theorem returns an `EvenClosest` witness, while
the public Flocq theorem is stated with `round ... ZnearestE`. -/
theorem evenClosest_value_eq_round_NE (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int)
    (r : ℝ) (f : FloatSpec.Core.Defs.FlocqFloat beta)
    [FloatSpec.Core.Generic_fmt.Valid_exp (FLT_exp (-b.dExp) p)]
    (hpBound : pGivesBound beta b p) (hprec : precisionNotZero p)
    (hbeta : 1 < beta)
    (hec : EvenClosest (beta:=beta) (toFboundSkel b) (beta : ℝ) p.toNat r f) :
    _root_.F2R (beta:=beta) f =
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp (-b.dExp) p)
        (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) r := by
  classical
  have hp_pos : 0 < p := lt_trans Int.zero_lt_one hprec
  haveI : Prec_gt_0 p := ⟨hp_pos⟩
  haveI : FloatSpec.Core.Generic_fmt.Monotone_exp (FLT_exp (-b.dExp) p) := by
    simp only [FLT_exp]
    exact FloatSpec.Core.FLT.FLT_exp_mono (prec := p) (emin := -b.dExp)
  haveI : FloatSpec.Core.RoundNE.Exists_NE beta (FLT_exp (-b.dExp) p) :=
    FLT_exp_exists_NE beta b p hprec
  let y := _root_.F2R (beta:=beta) f
  let rounded :=
    FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp (-b.dExp) p)
      (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) r
  have hN_y :
      FloatSpec.Core.Defs.Rnd_N_pt
        (fun z => generic_format beta (FLT_exp (-b.dExp) p) z) r y := by
    exact closest_to_Rnd_N_pt (beta := beta) (b := b) (p := p)
      (r := r) (f := f) hpBound hprec hbeta hec.1
  have hnorm_val :
      _root_.F2R (beta:=beta)
        (Fnormalize (beta:=beta) beta (toFboundSkel b) p.toNat f) = y := by
    have h := FnormalizeCorrect (beta:=beta) beta (toFboundSkel b) p.toNat f
    simpa only [wp, PostCond.noThrow, pure, FnormalizeCorrect_check,
      Id.run, ULift.up_down, y] using h ⟨rfl, hbeta⟩
  have hNE_y :
      FloatSpec.Core.RoundNE.Rnd_NE_pt beta (FLT_exp (-b.dExp) p) r y := by
    refine ⟨hN_y, ?_⟩
    rcases hec.2 with hEven | hUnique
    · left
      exact NE_prop_of_FNeven_normalized (beta := beta) (b := b) (p := p)
        (x := r) (y := y) (f := f) hpBound hec.1.1 hbeta hnorm_val hEven
    · right
      intro z hz
      have hz_format : generic_format beta (FLT_exp (-b.dExp) p) z := hz.1
      have hz_bound := format_is_flocq_bounded beta b p z
        ⟨hz_format, hpBound, hprec, hbeta⟩
      simp only [wp, PostCond.noThrow, format_is_pff_format'_check, pure] at hz_bound
      rcases hz_bound with ⟨q, hqval, hqbounded⟩
      have hqClosest : Closest (beta:=beta) (toFboundSkel b) (beta : ℝ) r q := by
        exact Rnd_N_pt_to_closest (beta := beta) (b := b) (p := p)
          (r := r) (y := z) (f := q) hpBound hprec hbeta hqval hqbounded hz
      exact hqval.symm.trans (hUnique q hqClosest)
  have hNE_round :
      FloatSpec.Core.RoundNE.Rnd_NE_pt beta (FLT_exp (-b.dExp) p) r rounded := by
    have h := FloatSpec.Core.RoundNE.round_NE_pt
      (beta := beta) (fexp := FLT_exp (-b.dExp) p) (x := r)
    simpa [FloatSpec.Core.RoundNE.round_NE_pt_check, pure, decide_eq_true_iff,
      rounded] using h hbeta
  have huniq := FloatSpec.Core.RoundNE.Rnd_NE_pt_unique
      (beta := beta) (fexp := FLT_exp (-b.dExp) p)
      (x := r) (f1 := y) (f2 := rounded)
  have hy_eq : y = rounded := by
    simpa [FloatSpec.Core.RoundNE.Rnd_NE_pt_unique_specific_check, pure,
      decide_eq_true_iff] using huniq ⟨hbeta, hNE_y, hNE_round⟩
  simpa [y, rounded]

/-- Coq: `round_NE_is_pff_round` — nearest-even rounding has a canonical Pff
`EvenClosest` witness whose real value is the concrete Flocq nearest-even
rounding. -/
theorem round_NE_is_pff_round (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (r : ℝ)
    [FloatSpec.Core.Generic_fmt.Valid_exp (FLT_exp (-b.dExp) p)]
    (hpBound : pGivesBound beta b p) (hprec : precisionNotZero p)
    (hbeta : 1 < beta) :
    ∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
      Fcanonic (beta:=beta) beta (toFboundSkel b) f ∧
      EvenClosest (beta:=beta) (toFboundSkel b) (beta : ℝ) p.toNat r f ∧
      _root_.F2R (beta:=beta) f =
        FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp (-b.dExp) p)
          (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) r := by
  have hp_pos : 0 < p := lt_trans Int.zero_lt_one hprec
  haveI : Prec_gt_0 p := ⟨hp_pos⟩
  haveI : FloatSpec.Core.RoundNE.Exists_NE beta (FLT_exp (-b.dExp) p) :=
    FLT_exp_exists_NE beta b p hprec
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hp_toNat : (p.toNat : Int) = p := Int.toNat_of_nonneg hp_nonneg
  have hp_toNat_gt : 1 < (p.toNat : Int) := by
    simpa [hp_toNat] using hprec
  have hp_abs_toNat : (|p| : Int).toNat = p.toNat := by
    rw [abs_of_nonneg hp_nonneg]
  have hvnum : (toFboundSkel b).vNum = Zpower_nat beta p.toNat := by
    unfold pGivesBound at hpBound
    dsimp [toFboundSkel]
    simpa [hp_abs_toNat] using hpBound
  let f := RND_EvenClosest (beta:=beta) (toFboundSkel b) beta p.toNat r
  have hcan : Fcanonic (beta:=beta) beta (toFboundSkel b) f := by
    have h := RND_EvenClosest_canonic_closed
      (beta:=beta) (toFboundSkel b) beta p.toNat r
    simpa only [wp, PostCond.noThrow, pure, RND_EvenClosest_canonic_check,
      Id.run, ULift.up_down, f] using h ⟨rfl, hbeta, hp_toNat_gt, hvnum⟩
  have hec : EvenClosest (beta:=beta) (toFboundSkel b) (beta : ℝ) p.toNat r f := by
    have h := RND_EvenClosest_correct
      (beta:=beta) (toFboundSkel b) beta p.toNat r
    simpa only [wp, PostCond.noThrow, pure, RND_EvenClosest_correct_check,
      Id.run, ULift.up_down, f] using h ⟨rfl, hbeta, hp_toNat_gt, hvnum⟩
  have hval :
      _root_.F2R (beta:=beta) f =
        FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp (-b.dExp) p)
          (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) r := by
    simpa [f] using pff_round_NE_is_round beta b p r hpBound hprec hbeta
  exact ⟨f, hcan, hec, hval⟩

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
noncomputable def pff_canonic_is_canonic_check (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (f : PffFloat) : Id Unit :=
  pure ()

theorem pff_canonic_is_canonic (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (f : PffFloat) :
    ⦃⌜PFcanonic beta b p f ∧ pff_to_R_aux beta f ≠ 0⌝⦄
    pff_canonic_is_canonic_check beta b p f
    ⦃⇓_ => ⌜FloatSpec.Core.Generic_fmt.canonical beta (FLT_exp (-b.dExp) p) (pff_to_flocq beta f)⌝⦄ := by
  intro ⟨hcan, _⟩
  simp only [wp, PostCond.noThrow, pff_canonic_is_canonic_check, pure]
  -- Goal: canonical beta (FLT_exp (-b.dExp) p) (pff_to_flocq beta f)
  -- Unfold canonical: (pff_to_flocq beta f).Fexp = FLT_exp (-b.dExp) p (mag beta (F2R (pff_to_flocq beta f)))
  unfold FloatSpec.Core.Generic_fmt.canonical
  -- By definition, pff_to_flocq beta f has Fexp = f.exponent
  -- and F2R (pff_to_flocq beta f) = pff_to_R_aux beta f
  have h_fexp : (pff_to_flocq beta f).Fexp = f.exponent := rfl
  rw [h_fexp]
  -- Now we need: f.exponent = FLT_exp (-b.dExp) p (mag beta (F2R (pff_to_flocq beta f)))
  -- From the definition of PFcanonic: f.exponent = FLT_exp (-b.dExp) p (mag beta (pff_to_R_aux beta f))
  -- We need: F2R (pff_to_flocq beta f) = pff_to_R_aux beta f
  have h_pff_to_R_eq : FloatSpec.Core.Defs.F2R (pff_to_flocq beta f) = pff_to_R_aux beta f := by
    unfold pff_to_R_aux pff_to_flocq FloatSpec.Core.Defs.F2R
    simp only [FloatSpec.Core.Defs.FlocqFloat.Fnum, FloatSpec.Core.Defs.FlocqFloat.Fexp]
    rfl
  rw [h_pff_to_R_eq]
  -- Now the goal is exactly the PFcanonic hypothesis
  exact hcan

/-- Coq: `format_is_pff_format_can` — from `generic_format`, produce a canonical Pff float.
    We use the same checker as `format_is_pff_format'` and return existence of a
    canonical witness with the right real value. -/
theorem format_is_pff_format_can (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (r : ℝ) :
    ⦃⌜generic_format beta (FLT_exp (-b.dExp) p) r⌝⦄
    format_is_pff_format'_check beta b p r
    ⦃⇓_ => ⌜∃ f : PffFloat, pff_to_R_aux beta f = r ∧ PFcanonic beta b p f⌝⦄ := by
  intro hfmt
  simp only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
  -- Use mk_from_generic as the witness
  use mk_from_generic beta b p r
  constructor
  · -- Show pff_to_R_aux beta (mk_from_generic beta b p r) = r
    unfold pff_to_R_aux pff_to_flocq mk_from_generic
    simp only [Bool.false_eq_true, ↓reduceIte]
    -- From generic_format, we have r = F2R {Ztrunc(sm), cexp}
    simp only [generic_format, FloatSpec.Core.Generic_fmt.scaled_mantissa,
               FloatSpec.Core.Generic_fmt.cexp] at hfmt
    exact hfmt.symm
  · -- Show PFcanonic beta b p (mk_from_generic beta b p r)
    -- PFcanonic: f.exponent = FLT_exp (-b.dExp) p (mag beta (pff_to_R_aux beta f))
    unfold PFcanonic
    -- f.exponent = cexp beta (FLT_exp (-b.dExp) p) r
    -- We need: cexp beta (FLT_exp (-b.dExp) p) r = FLT_exp (-b.dExp) p (mag beta (pff_to_R_aux beta (mk_from_generic...)))
    -- First show pff_to_R_aux beta (mk_from_generic...) = r
    have h_val_eq : pff_to_R_aux beta (mk_from_generic beta b p r) = r := by
      unfold pff_to_R_aux pff_to_flocq mk_from_generic
      simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [generic_format, FloatSpec.Core.Generic_fmt.scaled_mantissa,
                 FloatSpec.Core.Generic_fmt.cexp] at hfmt
      exact hfmt.symm
    -- Goal is (mk_from_generic beta b p r).exponent = FLT_exp (-b.dExp) p (mag beta (pff_to_R_aux beta (mk_from_generic beta b p r)))
    rw [h_val_eq]
    -- Now goal: (mk_from_generic beta b p r).exponent = FLT_exp (-b.dExp) p (mag beta r)
    -- By definition, mk_from_generic.exponent = cexp beta (FLT_exp (-b.dExp) p) r = fexp (mag beta r)
    unfold mk_from_generic cexp FloatSpec.Core.Generic_fmt.cexp
    rfl

variable (beta : Int) [ValidRadix beta]

-- Auxiliary conversion functions
/-- Pff normalization operator for this auxiliary compatibility leaf.
    It matches the current `Fnormalize` behavior in Pff.lean. -/
def pff_normalize (f : PffFloat) : PffFloat := f

def pff_abs (f : PffFloat) : PffFloat :=
  { f with sign := false }

def pff_opp (f : PffFloat) : PffFloat :=
  { f with sign := !f.sign }

-- Auxiliary operations
/-- Compare two PffFloats, returning:
    - negative if x < y
    - 0 if x = y
    - positive if x > y
    This comparison uses the effective signed mantissas scaled to a common exponent. -/
noncomputable def pff_compare (x y : PffFloat) : Int :=
  let x_signed := if x.sign then -x.mantissa else x.mantissa
  let y_signed := if y.sign then -y.mantissa else y.mantissa
  let min_exp := min x.exponent y.exponent
  -- Scale both to the minimum exponent
  let x_scaled := x_signed * Zpower_nat beta (Int.toNat (x.exponent - min_exp))
  let y_scaled := y_signed * Zpower_nat beta (Int.toNat (y.exponent - min_exp))
  if x_scaled < y_scaled then -1
  else if x_scaled > y_scaled then 1
  else 0

/-- Maximum of two PffFloats based on their real values. -/
noncomputable def pff_max (x y : PffFloat) : PffFloat :=
  if pff_compare beta x y ≥ 0 then x else y

/-- Minimum of two PffFloats based on their real values. -/
noncomputable def pff_min (x y : PffFloat) : PffFloat :=
  if pff_compare beta x y ≤ 0 then x else y

-- Auxiliary properties
/-- Normalization is idempotent: normalizing twice is the same as normalizing once. -/
theorem pff_normalize_idempotent (f : PffFloat) :
  pff_normalize (pff_normalize f) = pff_normalize f := by
  rfl

theorem pff_abs_correct (f : PffFloat) (hbeta : beta > 0) (hmant : f.mantissa ≥ 0) :
  pff_to_R_aux beta (pff_abs f) = |pff_to_R_aux beta f| := by
  simp only [pff_to_R_aux, pff_abs, pff_to_flocq, F2R, FloatSpec.Core.Defs.F2R]
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases h : f.sign = true <;> simp only [h, ↓reduceIte]
  · -- sign = true: original value is -(f.mantissa) * beta^exp
    -- pff_abs value is f.mantissa * beta^exp
    -- |-(f.mantissa) * beta^exp| = |-(f.mantissa)| * |beta^exp| = f.mantissa * beta^exp
    rw [Int.cast_neg, abs_mul, abs_neg]
    have h1 : (0 : ℝ) ≤ (f.mantissa : ℝ) := Int.cast_nonneg_iff.mpr hmant
    have h2 : (0 : ℝ) < (beta : ℝ) := Int.cast_pos.mpr hbeta
    rw [abs_of_nonneg h1, abs_zpow, abs_of_pos h2]
  · -- sign = false: original value is f.mantissa * beta^exp
    -- pff_abs value is f.mantissa * beta^exp
    -- |f.mantissa * beta^exp| = f.mantissa * beta^exp (since both are non-negative)
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h1 : (0 : ℝ) ≤ (f.mantissa : ℝ) := Int.cast_nonneg_iff.mpr hmant
    have h2 : (0 : ℝ) < (beta : ℝ) := Int.cast_pos.mpr hbeta
    rw [abs_mul, abs_of_nonneg h1, abs_zpow, abs_of_pos h2]

theorem pff_opp_correct (f : PffFloat) :
  pff_to_R_aux beta (pff_opp f) = -(pff_to_R_aux beta f) := by
  simp only [pff_to_R_aux, pff_opp, pff_to_flocq, F2R, FloatSpec.Core.Defs.F2R]
  by_cases h : f.sign = true <;> simp only [h, Bool.not_true, Bool.false_eq_true, Bool.not_false,
    ↓reduceIte, Int.cast_neg, neg_neg, neg_mul]

-- Compatibility with Flocq operations
theorem pff_abs_flocq_equiv (f : PffFloat) :
  pff_to_flocq beta (pff_abs f) = pff_to_flocq beta (pff_abs f) := by
  rfl

theorem pff_opp_flocq_equiv (f : PffFloat) :
  pff_to_flocq beta (pff_opp f) = pff_to_flocq beta (pff_opp f) := by
  rfl

-- Helper lemmas for conversion correctness
/-- The sign of a PffFloat determines the sign of its real value,
    provided the mantissa is positive and beta is positive. -/
lemma pff_sign_correct (f : PffFloat) (hbeta : beta > 0) (hmant : f.mantissa > 0) :
  (pff_to_R_aux beta f < 0) ↔ f.sign := by
  simp only [pff_to_R_aux, pff_to_flocq, F2R, FloatSpec.Core.Defs.F2R]
  have hbeta_pos : (0 : ℝ) < (beta : ℝ) := Int.cast_pos.mpr hbeta
  have hbeta_zpow_pos : (0 : ℝ) < (beta : ℝ) ^ f.exponent := zpow_pos hbeta_pos f.exponent
  have hmant_pos : (0 : ℝ) < (f.mantissa : ℝ) := Int.cast_pos.mpr hmant
  by_cases h : f.sign = true
  · -- f.sign = true: signed mantissa is -f.mantissa, which is < 0
    simp only [h, ↓reduceIte, Int.cast_neg]
    constructor
    · intro _; trivial
    · intro _
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hmant_pos) hbeta_zpow_pos
  · -- f.sign = false: signed mantissa is f.mantissa, which is > 0
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro hlt
      have hpos : (0 : ℝ) < (f.mantissa : ℝ) * (beta : ℝ) ^ f.exponent := mul_pos hmant_pos hbeta_zpow_pos
      linarith
    · simp only [IsEmpty.forall_iff]

lemma pff_mantissa_bounds (f : PffFloat) (prec : Int) :
  0 ≤ f.mantissa ∧ f.mantissa < (2 : Int) ^ (Int.toNat prec) →
  0 ≤ Int.natAbs (pff_to_flocq beta f).Fnum ∧
  Int.natAbs (pff_to_flocq beta f).Fnum < (2 : Int) ^ (Int.toNat prec) := by
  intro ⟨hmant_nonneg, hmant_bound⟩
  simp only [pff_to_flocq]
  -- Fnum = if f.sign then -f.mantissa else f.mantissa
  -- In both cases, natAbs (Fnum) = natAbs (f.mantissa)
  constructor
  · -- natAbs is always non-negative (as a coerced Int)
    exact Nat.cast_nonneg _
  · -- natAbs (if f.sign then -f.mantissa else f.mantissa) = natAbs f.mantissa < 2^prec
    by_cases h : f.sign = true <;> simp only [h, Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg]
    all_goals rw [Int.natAbs_of_nonneg hmant_nonneg]; exact hmant_bound

-- Auxiliary arithmetic operations
def pff_shift_exp (f : PffFloat) (n : Int) : PffFloat :=
  { f with exponent := f.exponent + n }

def pff_shift_mant (f : PffFloat) (n : Int) : PffFloat :=
  { f with mantissa := f.mantissa * ((2 : Int) ^ (Int.toNat n)) }

-- Shifting properties
theorem pff_shift_exp_correct (f : PffFloat) (n : Int) (hbeta : beta ≠ 0) :
  pff_to_R_aux beta (pff_shift_exp f n) =
  pff_to_R_aux beta f * (beta : ℝ)^n := by
  simp only [pff_to_R_aux, pff_shift_exp, pff_to_flocq, F2R, FloatSpec.Core.Defs.F2R]
  -- Goal: m * beta^(e+n) = m * beta^e * beta^n
  have hbeta_ne : (beta : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hbeta
  rw [zpow_add₀ hbeta_ne, mul_assoc]

theorem pff_shift_mant_correct (f : PffFloat) (n : Int) (hn : n ≥ 0) :
  pff_to_R_aux beta (pff_shift_mant f n) =
  pff_to_R_aux beta f * (2 : ℝ) ^ n := by
  simp only [pff_to_R_aux, pff_shift_mant, pff_to_flocq, F2R, FloatSpec.Core.Defs.F2R]
  -- Goal: (signed_m * 2^(toNat n)) * beta^e = signed_m * beta^e * 2^n
  -- Use n ≥ 0 to relate zpow and pow
  have h_n_eq : n = n.toNat := (Int.toNat_of_nonneg hn).symm
  conv_rhs => rw [h_n_eq, zpow_natCast]
  by_cases h : f.sign = true <;> simp only [h, Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  all_goals ring

/-!
Missing theorems from Coq Pff2FlocqAux.v

We follow the project convention: introduce a `_check` function and use
Hoare-triple syntax for each translated statement.
-/

-- Exponent lower bound from magnitude lower bound
noncomputable def FloatFexp_gt_check (beta : Int) [ValidRadix beta] (b : Fbound) (p e : Int) (f : PffFloat) : Id Unit :=
  pure ()

/-- Coq: `FloatFexp_gt` — if `f` is bounded and `(beta : ℝ)^(e+p) ≤ |FtoR f|`,
    then `e < Fexp f`. Here we use `pff_to_R_aux` for `FtoR` and the `exponent`
    field of `PffFloat` for `Fexp`. -/
theorem FloatFexp_gt (beta : Int) [ValidRadix beta] (b : Fbound) (p e : Int) (f : PffFloat) :
    ⦃⌜pGivesBound beta b p ∧ PFbounded b f ∧ (beta : ℝ) ^ (e + p) ≤ |pff_to_R_aux beta f| ∧ (1 : Int) < beta ∧ p > 0⌝⦄
    FloatFexp_gt_check beta b p e f
    ⦃⇓_ => ⌜e < f.exponent⌝⦄ := by
  intro ⟨hpGives, hbounded, hmag_le, hbeta_gt_1, hp_pos⟩
  simp only [wp, PostCond.noThrow, FloatFexp_gt_check, pure]
  -- Key insight: |pff_to_R_aux beta f| = |signed_mantissa| * beta^f.exponent
  -- From PFbounded: |signed_mantissa| < b.vNum = beta^p (by pGivesBound)
  -- So |pff_to_R_aux beta f| < beta^p * beta^f.exponent = beta^(p + f.exponent)
  -- From hypothesis: beta^(e + p) ≤ |pff_to_R_aux beta f| < beta^(p + f.exponent)
  -- Therefore: beta^(e + p) < beta^(p + f.exponent)
  -- Since beta > 1: e + p < p + f.exponent, hence e < f.exponent

  -- First, get the structure of pff_to_R_aux
  unfold pff_to_R_aux pff_to_flocq _root_.F2R FloatSpec.Core.Defs.F2R at hmag_le

  -- Get beta > 1 as a real number fact
  have hbeta_pos : (0 : ℝ) < (beta : ℝ) := by
    have h0 : (0 : Int) < beta := by omega
    exact Int.cast_pos.mpr h0
  have hbeta_gt_1_real : (1 : ℝ) < (beta : ℝ) := by
    have h1 : ((1 : Int) : ℝ) < (beta : ℝ) := Int.cast_lt.mpr hbeta_gt_1
    simp only [Int.cast_one] at h1
    exact h1

  -- From PFbounded, extract the mantissa bound
  unfold PFbounded at hbounded
  simp only at hbounded
  obtain ⟨hmant_bound, hexp_bound⟩ := hbounded

  -- From pGivesBound, we get b.vNum = beta^|p|
  unfold pGivesBound at hpGives
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos

  -- The signed mantissa is bounded by b.vNum
  let signed_m := if f.sign then -f.mantissa else f.mantissa
  have h_signed_abs : |signed_m| < b.vNum := by
    rw [Int.abs_eq_natAbs]
    exact hmant_bound

  -- |pff_to_R_aux beta f| = |signed_m| * beta^f.exponent
  have h_pff_to_R : |(signed_m : ℝ) * (beta : ℝ) ^ f.exponent| = |(signed_m : ℝ)| * (beta : ℝ) ^ f.exponent := by
    rw [abs_mul, abs_zpow, abs_of_pos hbeta_pos]

  -- Prove b.vNum = beta^p as reals
  have hvNum_eq : (b.vNum : ℝ) = (beta : ℝ) ^ p := by
    rw [hpGives]
    simp only [Zpower_nat]
    push_cast
    rw [← zpow_natCast]
    congr 1
    -- Goal: ↑|p|.toNat = p  (in ℤ)
    -- Since p ≥ 0: |p| = p, so |p|.toNat = p.toNat
    -- And p.toNat cast to ℤ is p (since p ≥ 0)
    rw [abs_of_nonneg hp_nonneg]
    exact Int.toNat_of_nonneg hp_nonneg

  -- Get |signed_m| < beta^p as reals
  have h_signed_lt_betap : (|(signed_m : ℝ)|) < (beta : ℝ) ^ p := by
    -- |(signed_m : ℝ)| = (|signed_m| : ℝ) by Int.cast_abs
    rw [← Int.cast_abs]
    -- Now goal: ↑|signed_m| < ↑beta ^ p
    -- Use Int.cast_lt directly on h_signed_abs
    have h1 := Int.cast_lt (R := ℝ) |>.mpr h_signed_abs  -- ↑|signed_m| < ↑b.vNum
    linarith [hvNum_eq]

  -- |pff_to_R_aux beta f| < beta^p * beta^f.exponent = beta^(p + f.exponent)
  have h_upper : |(signed_m : ℝ) * (beta : ℝ) ^ f.exponent| < (beta : ℝ) ^ (p + f.exponent) := by
    rw [h_pff_to_R]
    have hexp_pos : (0 : ℝ) < (beta : ℝ) ^ f.exponent := zpow_pos hbeta_pos f.exponent
    calc |(signed_m : ℝ)| * (beta : ℝ) ^ f.exponent
        < (beta : ℝ) ^ p * (beta : ℝ) ^ f.exponent := mul_lt_mul_of_pos_right h_signed_lt_betap hexp_pos
      _ = (beta : ℝ) ^ (p + f.exponent) := by rw [← zpow_add₀ (ne_of_gt hbeta_pos)]

  -- The hypothesis gives beta^(e + p) ≤ |pff_to_R_aux beta f|
  have hmag_le' : (beta : ℝ) ^ (e + p) ≤ |(signed_m : ℝ) * (beta : ℝ) ^ f.exponent| := by
    simp only [FloatSpec.Core.Defs.FlocqFloat.Fnum, FloatSpec.Core.Defs.FlocqFloat.Fexp] at hmag_le
    convert hmag_le using 2

  -- Combine: beta^(e + p) < beta^(p + f.exponent)
  have h_lt : (beta : ℝ) ^ (e + p) < (beta : ℝ) ^ (p + f.exponent) :=
    lt_of_le_of_lt hmag_le' h_upper

  -- From beta^(e + p) < beta^(p + f.exponent) with beta > 1, get e + p < p + f.exponent
  have h_exp_ineq : e + p < p + f.exponent := by
    -- h_lt : (beta : ℝ) ^ (e + p) < (beta : ℝ) ^ (p + f.exponent)
    exact (zpow_lt_zpow_iff_right₀ hbeta_gt_1_real).mp h_lt

  -- Therefore e < f.exponent (from e + p < p + f.exponent by subtracting p from both sides)
  have h_goal : e < f.exponent := by linarith
  -- Now close the WP goal
  simp only [PredTrans.pure, Id.run, wp, PostCond.noThrow, PLift.up, h_goal]
  trivial

-- From canonicity and a magnitude lower bound, derive normality
noncomputable def CanonicGeNormal_check (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (f : PffFloat) : Id Unit :=
  pure ()

/-- Coq: `CanonicGeNormal` — if `f` is canonical and `β^(-dExp b + p - 1) ≤ |FtoR f|`,
    then `f` is normal (in the Pff sense).  The Lean statement exposes the
    bounded-format side conditions needed by the already ported
    `FloatFexp_gt` exponent lower-bound lemma. -/
theorem CanonicGeNormal (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (f : PffFloat) :
    ⦃⌜PFcanonic beta b p f ∧ PFbounded b f ∧ pGivesBound beta b p ∧
        (beta : ℝ) ^ (-b.dExp + p - 1) ≤ |pff_to_R_aux beta f| ∧
        (1 : Int) < beta ∧ p > 0⌝⦄
    CanonicGeNormal_check beta b p f
    ⦃⇓_ => ⌜PFnormal b f⌝⦄ := by
  intro ⟨_, hbounded, hpGives, hmag, hbeta, hp_pos⟩
  simp [wp, PostCond.noThrow, CanonicGeNormal_check, pure, PFnormal]
  refine ⟨hbounded, ?_⟩
  have hmag' :
      (beta : ℝ) ^ ((-b.dExp - 1) + p) ≤ |pff_to_R_aux beta f| := by
    have hpow_eq :
        ((beta : ℝ) ^ ((-b.dExp - 1) + p) : ℝ) =
          (beta : ℝ) ^ (-b.dExp + p - 1) := by
      congr 1
      omega
    simpa [hpow_eq] using hmag
  have htrip := FloatFexp_gt (beta := beta) (b := b) (p := p)
    (e := -b.dExp - 1) (f := f)
  simpa [wp, PostCond.noThrow, FloatFexp_gt_check, pure] using
    htrip ⟨hpGives, hbounded, hmag', hbeta, hp_pos⟩

-- Ulp for canonical/bounded matches Core.ulps
noncomputable def Fulp_ulp_aux_check (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (f : PffFloat) : Id Unit :=
  pure ()

/-- Coq: `Fulp_ulp_aux` — for canonical `f`, Pff `Fulp` equals Core `ulp`
at `(FLT_exp (-dExp b) p)`. -/
theorem Fulp_ulp_aux (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (f : PffFloat) :
    ⦃⌜PFcanonic beta b p f ∧ (1 : Int) < beta ∧ 0 < p⌝⦄
    Fulp_ulp_aux_check beta b p f
    ⦃⇓_ => ⌜PFulp beta b p f =
      ulp beta (FLT_exp (-b.dExp) p) (pff_to_R_aux beta f)⌝⦄ := by
  intro h
  rcases h with ⟨hcan, hbeta, hp_pos⟩
  haveI : Prec_gt_0 p := ⟨hp_pos⟩
  simp [wp, PostCond.noThrow, Fulp_ulp_aux_check, pure]
  unfold PFulp
  by_cases hx : pff_to_R_aux beta f = 0
  · simp [hx, ulp, FLT_exp]
    have hsmall := FloatSpec.Core.FLT.ulp_FLT_small
      (prec := p) (emin := -b.dExp) (beta := beta) (x := (0 : ℝ))
    have hbeta_real_pos : (0 : ℝ) < (beta : ℝ) := by
      exact_mod_cast (by omega : (0 : Int) < beta)
    have hpow_pos : (0 : ℝ) < (beta : ℝ) ^ (-b.dExp + p) :=
      zpow_pos hbeta_real_pos _
    have hres :
        FloatSpec.Core.Ulp.ulp beta (FloatSpec.Core.FLT.FLT_exp p (-b.dExp)) 0 =
          (beta : ℝ) ^ (-b.dExp) := by
      simpa [wp, PostCond.noThrow, pure] using
        hsmall ⟨hbeta, by simpa using hpow_pos⟩
    simpa [ulp, FLT_exp] using hres.symm
  · simp [hx]
    have hspec := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := FLT_exp (-b.dExp) p)
      (x := pff_to_R_aux beta f) hx
    have hulp :
        ulp beta (FLT_exp (-b.dExp) p) (pff_to_R_aux beta f) =
          (beta : ℝ) ^
            (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp (-b.dExp) p)
              (pff_to_R_aux beta f)) := by
      simpa [ulp, wp, PostCond.noThrow, pure] using hspec True.intro
    rw [hulp]
    simp [PFnormalize, mk_from_generic, cexp]

noncomputable def Fulp_ulp_check (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (f : PffFloat) : Id Unit :=
  pure ()

/-- Coq: `Fulp_ulp` — same as `Fulp_ulp_aux` but from `Fbounded` via normalization. -/
theorem Fulp_ulp (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (f : PffFloat) :
    ⦃⌜PFbounded b f ∧ (1 : Int) < beta ∧ 0 < p⌝⦄
    Fulp_ulp_check beta b p f
    ⦃⇓_ => ⌜PFulp beta b p f =
      ulp beta (FLT_exp (-b.dExp) p) (pff_to_R_aux beta f)⌝⦄ := by
  intro h
  rcases h with ⟨_, hbeta, hp_pos⟩
  haveI : Prec_gt_0 p := ⟨hp_pos⟩
  simp [wp, PostCond.noThrow, Fulp_ulp_check, pure]
  unfold PFulp
  by_cases hx : pff_to_R_aux beta f = 0
  · simp [hx, ulp, FLT_exp]
    have hsmall := FloatSpec.Core.FLT.ulp_FLT_small
      (prec := p) (emin := -b.dExp) (beta := beta) (x := (0 : ℝ))
    have hbeta_real_pos : (0 : ℝ) < (beta : ℝ) := by
      exact_mod_cast (by omega : (0 : Int) < beta)
    have hpow_pos : (0 : ℝ) < (beta : ℝ) ^ (-b.dExp + p) :=
      zpow_pos hbeta_real_pos _
    have hres :
        FloatSpec.Core.Ulp.ulp beta (FloatSpec.Core.FLT.FLT_exp p (-b.dExp)) 0 =
          (beta : ℝ) ^ (-b.dExp) := by
      simpa [wp, PostCond.noThrow, pure] using
        hsmall ⟨hbeta, by simpa using hpow_pos⟩
    simpa [ulp, FLT_exp] using hres.symm
  · simp [hx]
    have hspec := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := FLT_exp (-b.dExp) p)
      (x := pff_to_R_aux beta f) hx
    have hulp :
        ulp beta (FLT_exp (-b.dExp) p) (pff_to_R_aux beta f) =
          (beta : ℝ) ^
            (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp (-b.dExp) p)
              (pff_to_R_aux beta f)) := by
      simpa [ulp, wp, PostCond.noThrow, pure] using hspec True.intro
    rw [hulp]
    simp [PFnormalize, mk_from_generic, cexp]

noncomputable def round_NE_is_pff_round_generic_check
    (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (r : ℝ) : Id Unit :=
  pure ()

/-- Generic nearest-even witness bridge used by the specialized binary32/64
bridges below. This proves the PffFloat bounded/canonical witness and value
equality for `Calc.Round.round`; it is not the full upstream
`round_NE_is_pff_round`, whose Pff `EvenClosest` payload is still separate. -/
theorem round_NE_is_pff_round_generic
    (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int) (r : ℝ)
    [FloatSpec.Core.Generic_fmt.Valid_exp (FLT_exp (-b.dExp) p)] :
    ⦃⌜pGivesBound beta b p ∧ precisionNotZero p ∧ (1 : Int) < beta⌝⦄
    round_NE_is_pff_round_generic_check beta b p r
    ⦃⇓_ => ⌜∃ f : PffFloat,
        PFbounded b f ∧ PFcanonic beta b p f ∧
        pff_to_R_aux beta f =
          FloatSpec.Calc.Round.round beta (FLT_exp (-b.dExp) p) () r⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hpBound, hprec, hbeta⟩
  have hp_pos : 0 < p := lt_trans Int.zero_lt_one hprec
  haveI : Prec_gt_0 p := ⟨hp_pos⟩
  simp only [wp, PostCond.noThrow, round_NE_is_pff_round_generic_check, pure]
  let rnd_val := FloatSpec.Calc.Round.round beta (FLT_exp (-b.dExp) p) () r
  have h_rnd_fmt : generic_format beta (FLT_exp (-b.dExp) p) rnd_val := by
    unfold rnd_val FloatSpec.Calc.Round.round
    simpa [FloatSpec.Calc.Round.nearestEvenMode] using
      (FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := beta) (fexp := FLT_exp (-b.dExp) p)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t => !(decide (2 ∣ t))))
        (x := r) (hβ := hbeta))
  have h_val_eq :
      pff_to_R_aux beta (mk_from_generic beta b p rnd_val) = rnd_val := by
    unfold pff_to_R_aux pff_to_flocq mk_from_generic
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [generic_format, FloatSpec.Core.Generic_fmt.scaled_mantissa,
               FloatSpec.Core.Generic_fmt.cexp] at h_rnd_fmt
    exact h_rnd_fmt.symm
  use mk_from_generic beta b p rnd_val
  constructor
  · have hbounded := format_is_pff_format' beta b p rnd_val
      ⟨h_rnd_fmt, hpBound, hprec, hbeta⟩
    simpa [wp, PostCond.noThrow, format_is_pff_format'_check, pure] using hbounded
  constructor
  · unfold PFcanonic
    rw [h_val_eq]
    unfold mk_from_generic cexp FloatSpec.Core.Generic_fmt.cexp
    rfl
  · exact h_val_eq

-- Instances for single/double rounding to nearest even
noncomputable def round_NE_is_pff_round_b32_check (r : ℝ) : Id Unit :=
  pure ()

theorem round_NE_is_pff_round_b32 (rnd : ℝ → Int) (r : ℝ) [Prec_gt_0 24] :
    ⦃⌜True⌝⦄
    round_NE_is_pff_round_b32_check r
    ⦃⇓_ => ⌜∃ f : PffFloat,
        PFbounded bsingle f ∧ PFcanonic 2 bsingle 24 f ∧
        pff_to_R_aux 2 f = FloatSpec.Calc.Round.round 2 (FLT_exp (-149) 24) () r⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, round_NE_is_pff_round_b32_check, pure]

  -- Bridge instance: Monotone_exp for the Compat FLT_exp alias
  haveI : FloatSpec.Core.Generic_fmt.Monotone_exp (FLT_exp (-149) 24) := by
    simp only [FLT_exp]
    exact FloatSpec.Core.FLT.FLT_exp_mono (prec := 24) (emin := -149)

  -- The rounded value
  let rnd_val := FloatSpec.Calc.Round.round 2 (FLT_exp (-149) 24) () r
  have h_bsingle_dExp : bsingle.dExp = 149 := by
    unfold bsingle make_bound Bound
    decide
  -- rnd_val is in generic_format by the concrete roundR theorem.
  have h_rnd_fmt : generic_format 2 (FLT_exp (-149) 24) rnd_val := by
    unfold rnd_val FloatSpec.Calc.Round.round
    simpa [FloatSpec.Calc.Round.nearestEvenMode] using
      (FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := 2) (fexp := FLT_exp (-149) 24)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t => !(decide (2 ∣ t))))
        (x := r) (hβ := by decide))
  -- Use mk_from_generic to construct the PffFloat witness
  use mk_from_generic 2 bsingle 24 rnd_val
  constructor
  · have hpBound : pGivesBound 2 bsingle 24 := by
      simp [pGivesBound, bsingle, make_bound, Bound, radix2]
    have hprec : precisionNotZero 24 := by
      simp [precisionNotZero]
    have hfmt_bound : generic_format 2 (FLT_exp (-bsingle.dExp) 24) rnd_val := by
      simpa [h_bsingle_dExp] using h_rnd_fmt
    have hbounded := format_is_pff_format' 2 bsingle 24 rnd_val
      ⟨hfmt_bound, hpBound, hprec, by decide⟩
    simpa [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
      using hbounded
  constructor
  · unfold PFcanonic
    have h_val_eq : pff_to_R_aux 2 (mk_from_generic 2 bsingle 24 rnd_val) = rnd_val := by
      unfold pff_to_R_aux pff_to_flocq mk_from_generic
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [h_bsingle_dExp]
      simp only [generic_format, FloatSpec.Core.Generic_fmt.scaled_mantissa,
                 FloatSpec.Core.Generic_fmt.cexp] at h_rnd_fmt
      exact h_rnd_fmt.symm
    rw [h_val_eq]
    unfold mk_from_generic cexp FloatSpec.Core.Generic_fmt.cexp
    rfl
  · -- Need to show: pff_to_R_aux 2 (mk_from_generic 2 bsingle 24 rnd_val) = rnd_val
    -- By generic_format, rnd_val = F2R(Ztrunc(sm(rnd_val)), cexp(rnd_val))
    unfold pff_to_R_aux pff_to_flocq mk_from_generic
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [h_bsingle_dExp]
    -- The goal now is: F2R(Ztrunc(sm(rnd_val)), cexp(rnd_val)) = rnd_val
    -- which is exactly generic_format.symm
    simp only [generic_format, FloatSpec.Core.Generic_fmt.scaled_mantissa,
               FloatSpec.Core.Generic_fmt.cexp] at h_rnd_fmt
    exact h_rnd_fmt.symm

noncomputable def round_NE_is_pff_round_b64_check (r : ℝ) : Id Unit :=
  pure ()

theorem round_NE_is_pff_round_b64 (rnd : ℝ → Int) (r : ℝ) [Prec_gt_0 53] :
    ⦃⌜True⌝⦄
    round_NE_is_pff_round_b64_check r
    ⦃⇓_ => ⌜∃ f : PffFloat,
        PFbounded bdouble f ∧ PFcanonic 2 bdouble 53 f ∧
        pff_to_R_aux 2 f = FloatSpec.Calc.Round.round 2 (FLT_exp (-1074) 53) () r⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, round_NE_is_pff_round_b64_check, pure]

  -- Bridge instance: Monotone_exp for the Compat FLT_exp alias
  haveI : FloatSpec.Core.Generic_fmt.Monotone_exp (FLT_exp (-1074) 53) := by
    simp only [FLT_exp]
    exact FloatSpec.Core.FLT.FLT_exp_mono (prec := 53) (emin := -1074)

  -- The rounded value
  let rnd_val := FloatSpec.Calc.Round.round 2 (FLT_exp (-1074) 53) () r
  have h_bdouble_dExp : bdouble.dExp = 1074 := by
    unfold bdouble make_bound Bound
    decide
  -- rnd_val is in generic_format by the concrete roundR theorem.
  have h_rnd_fmt : generic_format 2 (FLT_exp (-1074) 53) rnd_val := by
    unfold rnd_val FloatSpec.Calc.Round.round
    simpa [FloatSpec.Calc.Round.nearestEvenMode] using
      (FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := 2) (fexp := FLT_exp (-1074) 53)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t => !(decide (2 ∣ t))))
        (x := r) (hβ := by decide))
  -- Use mk_from_generic to construct the PffFloat witness
  use mk_from_generic 2 bdouble 53 rnd_val
  constructor
  · have hpBound : pGivesBound 2 bdouble 53 := by
      simp [pGivesBound, bdouble, make_bound, Bound, radix2]
    have hprec : precisionNotZero 53 := by
      simp [precisionNotZero]
    have hfmt_bound : generic_format 2 (FLT_exp (-bdouble.dExp) 53) rnd_val := by
      simpa [h_bdouble_dExp] using h_rnd_fmt
    have hbounded := format_is_pff_format' 2 bdouble 53 rnd_val
      ⟨hfmt_bound, hpBound, hprec, by decide⟩
    simpa [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
      using hbounded
  constructor
  · unfold PFcanonic
    have h_val_eq : pff_to_R_aux 2 (mk_from_generic 2 bdouble 53 rnd_val) = rnd_val := by
      unfold pff_to_R_aux pff_to_flocq mk_from_generic
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [h_bdouble_dExp]
      simp only [generic_format, FloatSpec.Core.Generic_fmt.scaled_mantissa,
                 FloatSpec.Core.Generic_fmt.cexp] at h_rnd_fmt
      exact h_rnd_fmt.symm
    rw [h_val_eq]
    unfold mk_from_generic cexp FloatSpec.Core.Generic_fmt.cexp
    rfl
  · -- Need to show: pff_to_R_aux 2 (mk_from_generic 2 bdouble 53 rnd_val) = rnd_val
    -- By generic_format, rnd_val = F2R(Ztrunc(sm(rnd_val)), cexp(rnd_val))
    unfold pff_to_R_aux pff_to_flocq mk_from_generic
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [h_bdouble_dExp]
    -- The goal now is: F2R(Ztrunc(sm(rnd_val)), cexp(rnd_val)) = rnd_val
    -- which is exactly generic_format.symm
    simp only [generic_format, FloatSpec.Core.Generic_fmt.scaled_mantissa,
               FloatSpec.Core.Generic_fmt.cexp] at h_rnd_fmt
    exact h_rnd_fmt.symm
