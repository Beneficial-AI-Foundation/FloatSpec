import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Pff.Pff
import FloatSpec.src.Prop.Mult_error
import FloatSpec.src.Prop.Plus_error
import FloatSpec.src.Prop.Sterbenz
import Mathlib.Data.Real.Basic
import Std.Do.Triple

-- Conversion from Pff to Flocq formats
-- Translated from Coq file: flocq/src/Pff/Pff2Flocq.v

open Real
open FloatSpec.Core.Defs
open Std.Do

-- Conversion functions between Pff and Flocq representations

variable (beta : Int)

-- Convert Pff float to Flocq float
def pff_to_float (f : PffFloat) : FloatSpec.Core.Defs.FlocqFloat beta :=
  pff_to_flocq beta f

-- Convert Flocq float to real number via Pff
noncomputable def pff_to_R (f : PffFloat) : ℝ :=
  _root_.F2R (pff_to_flocq beta f)

-- Conversion preserves value
theorem pff_flocq_equiv (f : PffFloat) :
  pff_to_R beta f = _root_.F2R (pff_to_flocq beta f) := by
  rfl

-- Conversion is bijective for valid inputs
theorem pff_flocq_bijection (f : FloatSpec.Core.Defs.FlocqFloat beta) :
  pff_to_flocq beta (flocq_to_pff f) = f := by
  cases f with
  | mk Fnum Fexp =>
    simp only [flocq_to_pff, pff_to_flocq, FloatSpec.Core.Defs.FlocqFloat.mk.injEq]
    constructor
    · -- Fnum part
      by_cases h : Fnum < 0
      · -- Fnum < 0 case: sign = true, so we negate |Fnum| = -Fnum back to Fnum
        simp only [h, decide_true, ↓reduceIte]
        omega
      · -- Fnum ≥ 0 case: sign = false, so |Fnum| = Fnum
        simp only [h, decide_false, ↓reduceIte]
        push Not at h
        exact Int.natAbs_of_nonneg h
    · -- Fexp part is trivially equal
      trivial

/-- A well-formed PffFloat has non-negative mantissa and consistent sign:
    - mantissa ≥ 0 (sign-magnitude representation uses absolute value)
    - if sign is true (negative), mantissa must be positive (no negative zero ambiguity) -/
def PffFloat.wellFormed (f : PffFloat) : Prop :=
  f.mantissa ≥ 0 ∧ (f.sign = true → f.mantissa > 0)

theorem flocq_pff_bijection (f : PffFloat) (hwf : f.wellFormed) :
  flocq_to_pff (pff_to_flocq beta f) = f := by
  -- Extract wellFormed conditions
  obtain ⟨h_mant_nonneg, h_sign_pos⟩ := hwf
  -- Unfold the conversion functions
  simp only [flocq_to_pff, pff_to_flocq]
  -- We need to show three field equalities
  cases f with
  | mk mantissa exponent sign =>
    simp only [PffFloat.mk.injEq]
    -- Goal: ↑(if sign = true then -mantissa else mantissa).natAbs = mantissa ∧
    --       True ∧ decide ((if sign = true then -mantissa else mantissa) < 0) = sign
    -- Simplify the hypotheses
    simp only [PffFloat.mantissa, PffFloat.sign] at h_mant_nonneg h_sign_pos
    refine ⟨?mant, trivial, ?sign⟩
    case mant =>
      -- mantissa field: Int.natAbs (if sign then -mantissa else mantissa) = mantissa
      cases hsign : sign with
      | true =>
        simp only [↓reduceIte]
        -- -mantissa, and we need Int.natAbs (-mantissa) = mantissa
        -- Since mantissa > 0 (from h_sign_pos), -mantissa < 0
        have h_pos : mantissa > 0 := h_sign_pos hsign
        rw [Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (le_of_lt h_pos)
      | false =>
        -- if false = true then -mantissa else mantissa simplifies to mantissa
        simp only [Bool.false_eq_true, ↓reduceIte]
        -- mantissa ≥ 0, so Int.natAbs mantissa = mantissa
        exact Int.natAbs_of_nonneg h_mant_nonneg
    case sign =>
      -- sign field: decide ((if sign then -mantissa else mantissa) < 0) = sign
      cases hsign : sign with
      | true =>
        simp only [↓reduceIte]
        -- Need: decide (-mantissa < 0) = true
        have h_pos : mantissa > 0 := h_sign_pos hsign
        simp only [Left.neg_neg_iff, h_pos, decide_true]
      | false =>
        -- if false = true then -mantissa else mantissa simplifies to mantissa
        simp only [Bool.false_eq_true, ↓reduceIte]
        -- Need: decide (mantissa < 0) = false
        have h_nn : ¬(mantissa < 0) := not_lt.mpr h_mant_nonneg
        simp only [h_nn, decide_false]

-- Pff operations match Flocq operations
theorem pff_add_equiv (x y : PffFloat) :
  pff_to_R beta (pff_add beta x y) =
  _root_.F2R (FloatSpec.Calc.Operations.Fplus beta (pff_to_flocq beta x) (pff_to_flocq beta y)) := by
  -- Unfold pff_to_R and pff_add
  unfold pff_to_R pff_add
  -- Use the bijection lemma: pff_to_flocq (flocq_to_pff f) = f
  rw [pff_flocq_bijection]

theorem pff_mul_equiv (x y : PffFloat) :
  pff_to_R beta (pff_mul beta x y) =
  _root_.F2R (FloatSpec.Calc.Operations.Fmult beta (pff_to_flocq beta x) (pff_to_flocq beta y)) := by
  -- Unfold pff_to_R and pff_mul
  unfold pff_to_R pff_mul
  -- Use the bijection lemma: pff_to_flocq (flocq_to_pff f) = f
  rw [pff_flocq_bijection]

-- Helper lemma: round_float followed by conversions gives F2R
private theorem round_float_F2R (fexp : Int → Int) (rnd : ℝ → Int) (x : ℝ) :
    pff_to_R beta (flocq_to_pff (round_float beta fexp rnd x)) =
    _root_.F2R (round_float beta fexp rnd x) := by
  unfold pff_to_R
  rw [pff_flocq_bijection]

-- Rounding Equivalence Section
--
-- The round_float function computes the canonical float representation of a rounded
-- value. The round_float_correct theorem shows that F2R of this float equals the
-- direct computation of the rounded value.
--
-- Note: The original pff_round_equiv claimed an equivalence with Calc.Round.round,
-- but that function uses round_to_generic which ignores the mode parameter and always
-- applies Ztrunc. See Pff2Flocq_changes.md for details.

-- round_float returns a float whose F2R equals the scaled rounded mantissa times beta^exp
-- This should be provable by rfl once the caches are aligned
theorem round_float_correct (fexp : Int → Int) (rnd : ℝ → Int) (x : ℝ) :
    _root_.F2R (round_float beta fexp rnd x) =
    (rnd (x * (beta : ℝ) ^ (-(FloatSpec.Core.Generic_fmt.cexp beta fexp x)))) *
    (beta : ℝ) ^ (FloatSpec.Core.Generic_fmt.cexp beta fexp x) := by
  -- Unfold round_float and F2R - uses the new definition from Compat.lean
  simp only [round_float, _root_.F2R, FloatSpec.Core.Defs.F2R, FlocqFloat.Fnum, FlocqFloat.Fexp]

-- Pff rounding corresponds to the core Flocq-style `roundR` operator.
theorem pff_round_equiv_RZ (x : ℝ) (prec : Int) [Prec_gt_0 prec] :
  let flocq_rnd := pff_to_flocq_rnd PffRounding.RZ
  let fexp := FLX_exp prec
  pff_to_R beta (flocq_to_pff (round_float beta fexp flocq_rnd x)) =
  FloatSpec.Core.Generic_fmt.roundR beta fexp flocq_rnd x := by
  simp only []
  unfold pff_to_R
  rw [pff_flocq_bijection]
  simp [round_float, FloatSpec.Core.Generic_fmt.roundR, pff_to_flocq_rnd,
    FloatSpec.Core.Generic_fmt.scaled_mantissa,
    _root_.F2R, FloatSpec.Core.Defs.F2R]

-- The general bridge is stated against `roundR`, which is parameterized by the
-- concrete integer rounding function selected by the Pff mode.
theorem pff_round_equiv (mode : PffRounding) (x : ℝ) (prec : Int) [Prec_gt_0 prec]
    :
  let flocq_rnd := pff_to_flocq_rnd mode
  let fexp := FLX_exp prec
  pff_to_R beta (flocq_to_pff (round_float beta fexp flocq_rnd x)) =
  FloatSpec.Core.Generic_fmt.roundR beta fexp flocq_rnd x := by
  simp only []
  unfold pff_to_R
  rw [pff_flocq_bijection]
  simp [round_float, FloatSpec.Core.Generic_fmt.roundR,
    FloatSpec.Core.Generic_fmt.scaled_mantissa,
    _root_.F2R, FloatSpec.Core.Defs.F2R]

-- Error bounds are preserved
theorem pff_error_bound_equiv (prec : Int) :
  pff_error_bound prec = (2 : ℝ)^(-prec) := by
  rfl

/-!
Missing theorems imported from Coq Pff2Flocq.v

We follow the project convention: introduce a `_check` function and state each
theorem using the Hoare-triple style when the translated statement is proved.
Entries whose Flocq payload is not available are kept as port-gap definitions,
not theorem claims.
-/

-- Coq: `round_N_opp_sym` — rounding to nearest-even is odd-symmetric
noncomputable def round_N_opp_sym_check (emin prec : Int) (choice : Int → Bool) (x : ℝ) : Unit :=
  ()

/-- Coq: `round_N_opp_sym` — for any `choice` satisfying the usual symmetry,
    rounding of the negation equals the negation of rounding. We phrase the
    statement using the rounding operator from Compat/Core. -/
-- Helper lemma: Ztrunc is odd-symmetric
private lemma Ztrunc_neg_eq (y : ℝ) : FloatSpec.Core.Raux.Ztrunc (-y) = -FloatSpec.Core.Raux.Ztrunc y := by
  unfold FloatSpec.Core.Raux.Ztrunc
  by_cases hy : 0 < y
  · -- y > 0: Ztrunc(-y) uses ceil branch (since -y < 0), Ztrunc(y) uses floor branch
    have h_neg_lt : (-y) < 0 := neg_lt_zero.mpr hy
    have h_not_neg_pos : ¬ (0 < -y) := not_lt.mpr (le_of_lt h_neg_lt)
    have h_not_y_neg : ¬ (y < 0) := not_lt.mpr (le_of_lt hy)
    simp only [h_neg_lt, h_not_neg_pos, ite_false, hy, h_not_y_neg, ite_true]
    rw [Int.ceil_neg]
  · -- y ≤ 0: split on y < 0 or y = 0
    push Not at hy
    by_cases hy0 : y < 0
    · -- y < 0: Ztrunc(-y) uses floor branch (since -y > 0), Ztrunc(y) uses ceil branch
      have h_neg_pos : 0 < -y := neg_pos.mpr hy0
      have h_not_neg_lt : ¬ ((-y) < 0) := not_lt.mpr (le_of_lt h_neg_pos)
      simp only [h_neg_pos, ite_true, hy0, h_not_neg_lt, ite_false]
      rw [Int.floor_neg]
    · -- y = 0
      have hy_eq : y = 0 := le_antisymm hy (le_of_not_gt hy0)
      simp only [hy_eq, neg_zero]
      -- if 0 < 0 then ... else ... evaluates to the else branch
      have h_not_lt : ¬ (0 : ℝ) < 0 := lt_irrefl 0
      simp only [h_not_lt, ite_false, Int.floor_zero, neg_zero]

-- Helper lemma: cexp(-x) = cexp(x)
private lemma cexp_neg_eq (b emin prec : Int) (x : ℝ) :
    FloatSpec.Core.Generic_fmt.cexp b (FLT_exp emin prec) (-x)
    = FloatSpec.Core.Generic_fmt.cexp b (FLT_exp emin prec) x := by
  simp only [FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Raux.mag, abs_neg]
  -- The if condition uses -x = 0 iff x = 0
  congr 1
  simp only [neg_eq_zero]

private lemma Znearest_of_int (choice : Int → Bool) (m : Int) :
    FloatSpec.Core.Generic_fmt.Znearest choice (m : ℝ) = m := by
  unfold FloatSpec.Core.Generic_fmt.Znearest
  simp only [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil,
             FloatSpec.Core.Raux.Rcompare, Id.run, pure,
             Int.floor_intCast, Int.ceil_intCast, Int.cast_id, sub_self]
  norm_num

private lemma nearestEven_choice_opp :
    (fun t : Int => !((fun s : Int => !(decide (2 ∣ s))) (-(t + 1))))
      = (fun t : Int => !(decide (2 ∣ t))) := by
  classical
  have two_dvd_neg_bool (n : Int) : decide (2 ∣ -n) = decide (2 ∣ n) := by
    have hiff : (2 ∣ -n) ↔ (2 ∣ n) := by
      constructor
      · intro h
        rcases h with ⟨k, hk⟩
        refine ⟨-k, ?_⟩
        have hneg := congrArg Neg.neg hk
        simpa [mul_neg] using hneg
      · intro h
        rcases h with ⟨k, hk⟩
        refine ⟨-k, ?_⟩
        have hneg := congrArg Neg.neg hk
        simpa [mul_neg] using hneg
    by_cases hdiv : 2 ∣ n
    · have hdiv' : 2 ∣ -n := hiff.mpr hdiv
      simp [decide_eq_true_iff, hdiv, hdiv']
    · have hdiv' : ¬ (2 ∣ -n) := fun h' => hdiv (hiff.mp h')
      simp [decide_eq_true_iff, hdiv, hdiv']
  have succ_parity_decide (t : Int) : decide (2 ∣ (t + 1)) = !(decide (2 ∣ t)) := by
    rcases Int.emod_two_eq_zero_or_one t with ht0 | ht1
    · have hadd : (t + 1) % 2 = ((t % 2) + (1 % 2)) % 2 := by
        simpa using (Int.add_emod t 1 2)
      have h1mod : (1 % 2 : Int) = 1 := by decide
      have h01 : ((0 + 1) % 2 : Int) = 1 := by decide
      have hmod_succ : (t + 1) % 2 = 1 := by
        simpa [hadd, ht0, h1mod] using h01
      have hdiv_t : 2 ∣ t := Int.dvd_of_emod_eq_zero (by simpa using ht0)
      have hndiv_succ : ¬ (2 ∣ (t + 1)) := by
        intro h
        have h0 : (t + 1) % 2 = 0 := Int.emod_eq_zero_of_dvd (a := 2) (b := t + 1) h
        simpa [hmod_succ] using h0
      simp [decide_eq_true_iff, hdiv_t, hndiv_succ]
    · have hadd : (t + 1) % 2 = ((t % 2) + (1 % 2)) % 2 := by
        simpa using (Int.add_emod t 1 2)
      have h1mod : (1 % 2 : Int) = 1 := by decide
      have h11 : ((1 + 1) % 2 : Int) = 0 := by decide
      have hmod_succ : (t + 1) % 2 = 0 := by
        simpa [hadd, ht1, h1mod] using h11
      have hndiv_t : ¬ (2 ∣ t) := by
        intro h
        have h0 : t % 2 = 0 := Int.emod_eq_zero_of_dvd (a := 2) (b := t) h
        simpa [h0] using ht1
      have hdiv_succ : 2 ∣ (t + 1) := Int.dvd_of_emod_eq_zero (by simpa using hmod_succ)
      simp [decide_eq_true_iff, hndiv_t, hdiv_succ]
  funext t
  have hpar_tog : decide (2 ∣ (-(t + 1))) = !decide (2 ∣ t) := by
    have hneg : decide (2 ∣ (-(t + 1))) = decide (2 ∣ (t + 1)) := by
      simpa using two_dvd_neg_bool (t + 1)
    exact hneg.trans (succ_parity_decide t)
  change Bool.not ((fun s : Int => Bool.not (decide (2 ∣ s))) (-(t + 1)))
      = Bool.not (decide (2 ∣ t))
  dsimp
  rw [Bool.not_not]
  exact hpar_tog

private lemma nearestEven_choice_opp_simp :
    (fun t : Int => decide (2 ∣ -1 + -t))
      = (fun t : Int => !(decide (2 ∣ t))) := by
  funext t
  have h := congrFun nearestEven_choice_opp t
  show decide (2 ∣ -1 + -t) = Bool.not (decide (2 ∣ t))
  have hsyn : (-1 + -t : Int) = -(t + 1) := by omega
  rw [hsyn]
  show decide (2 ∣ (-(t + 1))) = Bool.not (decide (2 ∣ t))
  simpa only [Bool.not_not] using h

theorem round_N_opp_sym (emin prec : Int) [Prec_gt_0 prec] (choice : Int → Bool) (x : ℝ) :
    ⦃⌜∀ t : Int, choice t = ! choice (-(t + 1))⌝⦄
    (pure (round_N_opp_sym_check emin prec choice x) : Id Unit)
    ⦃⇓_ => ⌜FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
              (FloatSpec.Core.Generic_fmt.Znearest choice) (-x)
            = - FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
              (FloatSpec.Core.Generic_fmt.Znearest choice) x⌝⦄ := by
  apply Std.Do.Triple.pure
  simp only [round_N_opp_sym_check, PostCond.noThrow]
  intro hchoice
  have h := FloatSpec.Core.Generic_fmt.round_N_opp
    (beta := 2) (fexp := FLT_exp emin prec) (choice := choice) (x := x)
  have hchoice_ext :
      (fun t : Int => !choice (-1 + -t)) = choice := by
    funext t
    have ht : -(t + 1) = -1 + -t := by omega
    have hsym := hchoice t
    simpa [ht] using hsym.symm
  simpa [hchoice_ext] using h

-- Coq: `C_format` — (β^s + 1) is in generic format for FLT(emin, prec)
noncomputable def C_format_check (emin prec s : Int) : Unit :=
  ()

/-- Coq: `C_format` — under the usual small-precision side conditions,
    the real `(β^s + 1)` is representable in `generic_format β (FLT_exp emin prec)`.
    We capture the side conditions in the Hoare precondition. -/
theorem C_format (emin prec s : Int) [Prec_gt_0 prec] :
    ⦃⌜(2 ≤ s) ∧ (s ≤ prec - 2) ∧ (emin ≤ 0)⌝⦄
    (pure (C_format_check emin prec s) : Id Unit)
    ⦃⇓_ => ⌜generic_format 2 (FLT_exp emin prec) ((2 : ℝ) ^ (Int.toNat s) + 1)⌝⦄ := by
  apply Std.Do.Triple.pure
  intro hpre
  rcases hpre with ⟨hs_ge, hs_le, hemin_le⟩
  let n : Nat := Int.toNat s
  let m : Int := (2 : Int) ^ n + 1
  have hs_nonneg : 0 ≤ s := by omega
  have hn_cast : (n : Int) = s := by
    exact Int.toNat_of_nonneg hs_nonneg
  have hF2R :
      FloatSpec.Core.Defs.F2R (FloatSpec.Core.Defs.FlocqFloat.mk (beta := 2) m 0)
        = (2 : ℝ) ^ n + 1 := by
    simp [FloatSpec.Core.Defs.F2R, m]
  have hfmt :=
    FloatSpec.Core.Generic_fmt.generic_format_F2R
      (beta := 2) (fexp := FLT_exp emin prec) (m := m) (e := 0)
      ⟨by decide, ?_⟩
  · simpa [FloatSpec.Core.Defs.F2R, hF2R, n, m] using hfmt
  intro hm_ne
  simp [FloatSpec.Core.Generic_fmt.cexp, FLT_exp, FloatSpec.Core.FLT.FLT_exp,
    FloatSpec.Core.Defs.F2R, m]
  constructor
  · have hmag_le : FloatSpec.Core.Raux.mag 2 ((2 : ℝ) ^ n + 1) ≤ s + 1 := by
      have hx_ne : (2 : ℝ) ^ n + 1 ≠ 0 := by positivity
      have hx_lt : |(2 : ℝ) ^ n + 1| < (2 : ℝ) ^ (s + 1) := by
        have hn_ge_two : 2 ≤ n := by omega
        have hpow_ge : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ n := by
          exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
        have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
        have hpow_one_lt : (1 : ℝ) < (2 : ℝ) ^ n := by
          have : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
            simpa using hpow_ge
          linarith
        have hs_succ_nonneg : 0 ≤ s + 1 := by omega
        have hsucc_nat : Int.toNat (s + 1) = n + 1 := by omega
        rw [← Int.toNat_of_nonneg hs_succ_nonneg, zpow_natCast, hsucc_nat]
        rw [pow_succ]
        simp [abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ n + 1)]
        nlinarith
      have htrip := FloatSpec.Core.Raux.mag_le_abs (beta := 2)
        (x := (2 : ℝ) ^ n + 1)
        (e := s + 1) (by decide) hx_ne hx_lt
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using (htrip (by trivial))
    omega
  · exact hemin_le

/-!
Coq lemma: `underf_mult_aux`

In the `Underf_mult_aux` section, Flocq proves that if two bounded Pff floats
have a product whose magnitude is at least `bpow (e + 2 * prec - 1)`, then the
sum of their exponents is at least `e`.
-/

noncomputable def underf_mult_aux_check {beta : Int}
    (_b : Fbound_skel) (_prec e : Int)
    (_x _y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

private lemma underf_mult_aux_abs_lt {beta : Int}
    (b : Fbound_skel) (prec : Int)
    (hβ : 1 < beta) (hprec : 1 < prec)
    (hpGivesBound : b.vNum = Zpower_nat beta (Int.natAbs prec))
    (z : FloatSpec.Core.Defs.FlocqFloat beta)
    (hz : Fbounded (beta:=beta) b z) :
    |_root_.F2R (beta:=beta) z| <
      FloatSpec.Core.Raux.bpow beta (z.Fexp + prec) := by
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hβ
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos_real
  have hpow_exp_pos : 0 < (beta : ℝ) ^ z.Fexp := zpow_pos hbpos_real z.Fexp
  have hnum_lt_int : |z.Fnum| < beta ^ Int.natAbs prec := by
    simpa [Fbounded, hpGivesBound, Zpower_nat] using hz.1
  have hnum_lt_cast :
      ((|z.Fnum| : Int) : ℝ) < ((beta ^ Int.natAbs prec : Int) : ℝ) := by
    exact_mod_cast hnum_lt_int
  have hprec_nonneg : 0 ≤ prec := by omega
  have hprec_natAbs : ((Int.natAbs prec : Nat) : Int) = prec :=
    Int.natAbs_of_nonneg hprec_nonneg
  have hpow_prec_cast :
      ((beta ^ Int.natAbs prec : Int) : ℝ) = (beta : ℝ) ^ prec := by
    rw [Int.cast_pow]
    simpa [hprec_natAbs] using
      (zpow_natCast (beta : ℝ) (Int.natAbs prec)).symm
  have hnum_lt_real : ((|z.Fnum| : Int) : ℝ) < (beta : ℝ) ^ prec := by
    simpa [hpow_prec_cast] using hnum_lt_cast
  calc
    |_root_.F2R (beta:=beta) z|
        = |(z.Fnum : ℝ) * (beta : ℝ) ^ z.Fexp| := by
            simp [_root_.F2R, FloatSpec.Core.Defs.F2R]
    _ = ((|z.Fnum| : Int) : ℝ) * (beta : ℝ) ^ z.Fexp := by
            rw [abs_mul, abs_of_pos hpow_exp_pos, Int.cast_abs]
    _ < (beta : ℝ) ^ prec * (beta : ℝ) ^ z.Fexp :=
            mul_lt_mul_of_pos_right hnum_lt_real hpow_exp_pos
    _ = FloatSpec.Core.Raux.bpow beta (z.Fexp + prec) := by
            rw [FloatSpec.Core.Raux.bpow]
            calc
              (beta : ℝ) ^ prec * (beta : ℝ) ^ z.Fexp
                  = (beta : ℝ) ^ (prec + z.Fexp) := by
                      exact (zpow_add₀ hbne prec z.Fexp).symm
              _ = (beta : ℝ) ^ (z.Fexp + prec) := by
                      rw [add_comm]

/-- Coq: `underf_mult_aux`.
If `x` and `y` are bounded by `b`, `b.vNum` is the radix precision bound, and
`|F2R x * F2R y|` is at least `bpow (e + 2 * prec - 1)`, then the product
cannot underflow below exponent `e`. -/
theorem underf_mult_aux {beta : Int}
    (b : Fbound_skel) (prec e : Int)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜1 < beta ∧
        1 < prec ∧
        b.vNum = Zpower_nat beta (Int.natAbs prec) ∧
        Fbounded (beta:=beta) b x ∧
        Fbounded (beta:=beta) b y ∧
        FloatSpec.Core.Raux.bpow beta (e + 2 * prec - 1) ≤
          |_root_.F2R (beta:=beta) x * _root_.F2R (beta:=beta) y|⌝⦄
    (pure (underf_mult_aux_check (beta:=beta) b prec e x y) : Id Unit)
    ⦃⇓_ => ⌜e ≤ x.Fexp + y.Fexp⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hprec, hpGivesBound, hxBounded, hyBounded, hprod_lower⟩
  simp only [wp, PostCond.noThrow, pure, underf_mult_aux_check, Id.run]
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hβ
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hbase_gt_one : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hx_abs_lt :=
    underf_mult_aux_abs_lt (beta:=beta) b prec hβ hprec hpGivesBound x hxBounded
  have hy_abs_lt :=
    underf_mult_aux_abs_lt (beta:=beta) b prec hβ hprec hpGivesBound y hyBounded
  have hx_bound_pos :
      0 < FloatSpec.Core.Raux.bpow beta (x.Fexp + prec) := by
    simpa [FloatSpec.Core.Raux.bpow] using
      zpow_pos hbpos_real (x.Fexp + prec)
  have hprod_lower_pos :
      0 < FloatSpec.Core.Raux.bpow beta (e + 2 * prec - 1) := by
    simpa [FloatSpec.Core.Raux.bpow] using
      zpow_pos hbpos_real (e + 2 * prec - 1)
  have hy_abs_pos : 0 < |_root_.F2R (beta:=beta) y| := by
    have hprod_abs_pos :
        0 < |_root_.F2R (beta:=beta) x * _root_.F2R (beta:=beta) y| :=
      lt_of_lt_of_le hprod_lower_pos hprod_lower
    have hy_ne : _root_.F2R (beta:=beta) y ≠ 0 := by
      intro hy_zero
      have hprod_zero :
          |_root_.F2R (beta:=beta) x * _root_.F2R (beta:=beta) y| = 0 := by
        simp [hy_zero]
      exact (not_lt_of_ge (by rw [hprod_zero])) hprod_abs_pos
    exact abs_pos.mpr hy_ne
  have hprod_upper :
      |_root_.F2R (beta:=beta) x * _root_.F2R (beta:=beta) y| <
        FloatSpec.Core.Raux.bpow beta ((x.Fexp + prec) + (y.Fexp + prec)) := by
    calc
      |_root_.F2R (beta:=beta) x * _root_.F2R (beta:=beta) y|
          = |_root_.F2R (beta:=beta) x| * |_root_.F2R (beta:=beta) y| := by
              rw [abs_mul]
      _ < FloatSpec.Core.Raux.bpow beta (x.Fexp + prec) *
            FloatSpec.Core.Raux.bpow beta (y.Fexp + prec) := by
              exact mul_lt_mul hx_abs_lt (le_of_lt hy_abs_lt) hy_abs_pos (le_of_lt hx_bound_pos)
      _ = FloatSpec.Core.Raux.bpow beta ((x.Fexp + prec) + (y.Fexp + prec)) := by
              simp [FloatSpec.Core.Raux.bpow]
              exact (zpow_add₀ (ne_of_gt hbpos_real) (x.Fexp + prec)
                (y.Fexp + prec)).symm
  have hbpow_lt :
      FloatSpec.Core.Raux.bpow beta (e + 2 * prec - 1) <
        FloatSpec.Core.Raux.bpow beta ((x.Fexp + prec) + (y.Fexp + prec)) :=
    lt_of_le_of_lt hprod_lower hprod_upper
  have hexp_lt :
      e + 2 * prec - 1 < (x.Fexp + prec) + (y.Fexp + prec) := by
    have hbpow_lt' :
        (beta : ℝ) ^ (e + 2 * prec - 1) <
          (beta : ℝ) ^ ((x.Fexp + prec) + (y.Fexp + prec)) := by
      simpa [FloatSpec.Core.Raux.bpow] using hbpow_lt
    exact ((zpow_right_strictMono₀ hbase_gt_one).lt_iff_lt).1 hbpow_lt'
  have hexp_lt' : e + 2 * prec - 1 < x.Fexp + y.Fexp + 2 * prec := by
    omega
  have hsub_lt : e - 1 < x.Fexp + y.Fexp := by
    omega
  have hle : (e - 1) + 1 ≤ x.Fexp + y.Fexp :=
    Int.add_one_le_iff.mpr hsub_lt
  have heq : (e - 1) + 1 = e := by omega
  simpa [heq] using hle

noncomputable def underf_mult_aux'_check {beta : Int}
    (_b : Fbound_skel) (_prec : Int)
    (_x _y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `underf_mult_aux'`.
This is the `underf_mult_aux` specialization at `e = -dExp b`. -/
theorem underf_mult_aux' {beta : Int}
    (b : Fbound_skel) (prec : Int)
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    ⦃⌜1 < beta ∧
        1 < prec ∧
        b.vNum = Zpower_nat beta (Int.natAbs prec) ∧
        Fbounded (beta:=beta) b x ∧
        Fbounded (beta:=beta) b y ∧
        FloatSpec.Core.Raux.bpow beta (-b.dExp + 2 * prec - 1) ≤
          |_root_.F2R (beta:=beta) x * _root_.F2R (beta:=beta) y|⌝⦄
    (pure (underf_mult_aux'_check (beta:=beta) b prec x y) : Id Unit)
    ⦃⇓_ => ⌜-b.dExp ≤ x.Fexp + y.Fexp⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hprec, hpGivesBound, hxBounded, hyBounded, hprod_lower⟩
  simp only [wp, PostCond.noThrow, pure, underf_mult_aux'_check, Id.run]
  exact
    underf_mult_aux (beta:=beta) b prec (-b.dExp) x y
      ⟨hβ, hprec, hpGivesBound, hxBounded, hyBounded, hprod_lower⟩

/-- Coq: `V1_Und3'`.
In the ErrFMA V1 construction, with `u1 := round_flt (a*x)`, the first
rounded product either remains zero or preserves the strong non-underflow lower
bound assumed for `a*x`. -/
theorem V1_Und3' (beta emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (a x _y : ℝ)
    (hβ : 1 < beta) (hprec : 3 ≤ prec)
    (_Fa : generic_format beta (FLT_exp emin prec) a)
    (_Fx : generic_format beta (FLT_exp emin prec) x)
    (_Fy : generic_format beta (FLT_exp emin prec) _y)
    (V1_Und1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |a * x|) :
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec)
      (FloatSpec.Core.Generic_fmt.Znearest choice) (a * x)
    u1 = 0 ∨ FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |u1| := by
  dsimp
  rcases V1_Und1 with hzero | hnonunder
  · left
    have hround0 :=
      (FloatSpec.Calc.Round.round_0 (beta := beta) (fexp := FLT_exp emin prec)
        (mode := FloatSpec.Compat.Scaffold.ZnearestMode choice)) True.intro
    simpa [FloatSpec.Calc.Round.round, FloatSpec.Compat.Scaffold.ZnearestMode, hzero]
      using hround0
  · right
    let e := emin + 2 * prec - 1
    have hfmt_bpow :
        generic_format beta (FLT_exp emin prec) ((beta : ℝ) ^ e) := by
      have htrip := FloatSpec.Core.FLT.generic_format_FLT_bpow
        (prec := prec) (emin := emin) (beta := beta) (e := e)
      have hemin_le : emin ≤ e := by
        dsimp [e]
        omega
      simpa [FLT_exp] using htrip ⟨hβ, hemin_le⟩
    have hfmt_bpow' :
        generic_format beta (FLT_exp emin prec)
          (FloatSpec.Core.Raux.bpow beta e) := by
      simpa [FloatSpec.Core.Raux.bpow] using hfmt_bpow
    by_cases hnonneg : 0 ≤ a * x
    · have hxle : FloatSpec.Core.Raux.bpow beta e ≤ a * x := by
        simpa [e, abs_of_nonneg hnonneg] using hnonunder
      have hle_round :
          FloatSpec.Core.Raux.bpow beta e ≤
            FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec)
              (FloatSpec.Core.Generic_fmt.Znearest choice) (a * x) := by
        exact FloatSpec.Core.Generic_fmt.roundR_ge_generic
          (beta := beta) (fexp := FLT_exp emin prec)
          (rnd := FloatSpec.Core.Generic_fmt.Znearest choice)
          (x := FloatSpec.Core.Raux.bpow beta e) (y := a * x)
          hβ hfmt_bpow' hxle
      exact le_trans hle_round (le_abs_self _)
    · have hnonpos : a * x ≤ 0 := le_of_not_ge hnonneg
      have hxle_neg : a * x ≤ -FloatSpec.Core.Raux.bpow beta e := by
        have hle : FloatSpec.Core.Raux.bpow beta e ≤ -(a * x) := by
          simpa [e, abs_of_nonpos hnonpos] using hnonunder
        linarith
      have hfmt_neg :
          generic_format beta (FLT_exp emin prec) (-FloatSpec.Core.Raux.bpow beta e) := by
        have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
          (beta := beta) (fexp := FLT_exp emin prec)
          (x := FloatSpec.Core.Raux.bpow beta e)
        simp only [wp, PostCond.noThrow, PredTrans.pure, Id.run, pure, Bind.bind] at hopp
        exact hopp hfmt_bpow'
      have hround_le :
          FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec)
              (FloatSpec.Core.Generic_fmt.Znearest choice) (a * x) ≤
            -FloatSpec.Core.Raux.bpow beta e := by
        exact FloatSpec.Core.Generic_fmt.roundR_le_generic
          (beta := beta) (fexp := FLT_exp emin prec)
          (rnd := FloatSpec.Core.Generic_fmt.Znearest choice)
          (x := a * x) (y := -FloatSpec.Core.Raux.bpow beta e)
          hβ hfmt_neg hxle_neg
      have hle_neg_round :
          FloatSpec.Core.Raux.bpow beta e ≤
            -FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec)
              (FloatSpec.Core.Generic_fmt.Znearest choice) (a * x) := by
        linarith
      exact le_trans hle_neg_round (neg_le_abs _)

/-- Coq: `V1_Und3`.
This weakens `V1_Und3'` from exponent `emin + 2*prec - 1` to
`emin + prec`, using monotonicity of powers. -/
theorem V1_Und3 (beta emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hβ : 1 < beta) (hprec : 3 ≤ prec)
    (_Fa : generic_format beta (FLT_exp emin prec) a)
    (_Fx : generic_format beta (FLT_exp emin prec) x)
    (_Fy : generic_format beta (FLT_exp emin prec) y)
    (V1_Und1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |a * x|) :
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec)
      (FloatSpec.Core.Generic_fmt.Znearest choice) (a * x)
    u1 = 0 ∨ FloatSpec.Core.Raux.bpow beta (emin + prec) ≤ |u1| := by
  dsimp
  have hstrong := V1_Und3' (beta := beta) (emin := emin) (prec := prec)
    (choice := choice) (a := a) (x := x) (_y := y)
    hβ hprec _Fa _Fx _Fy V1_Und1
  dsimp at hstrong
  rcases hstrong with hzero | hbound
  · exact Or.inl hzero
  · right
    have hβR : (1 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast (le_of_lt hβ)
    have hpow_le :
        FloatSpec.Core.Raux.bpow beta (emin + prec) ≤
          FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) := by
      have hexp_le : emin + prec ≤ emin + 2 * prec - 1 := by
        omega
      simpa [FloatSpec.Core.Raux.bpow] using zpow_le_zpow_right₀ hβR hexp_le
    exact le_trans hpow_le hbound

-- Coq theorem: `Dekker`
-- We mirror the statement structure by introducing local `let`-bound
-- intermediates that model the algorithm steps, and we state both the
-- conditional exactness and the global error bound. Proof is deferred.

noncomputable def Dekker_check (emin prec s : Int)
    (choice : Int → Bool) (x y : ℝ) : Unit :=
  ()

/-- Audit gap for Coq `Dekker`.
The upstream theorem states an error-free style decomposition of `x*y` into
`r + t4` plus an unconditional error bound.  Side condition: `beta = 2 ∨
Int.Even prec` (as in Coq).

The previous translated shell had postcondition `True`, so it did not encode
either Dekker exactness or the stated error bound. -/
noncomputable def Dekker (emin prec s : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (x y : ℝ) :
    Unit :=
  ()

-- (reserved) ErrFMA_bounded will be added next after validating preceding lemmas

-- Coq: `ErrFMA_bounded` — formats of r1, r2, r3 in compensated FMA scheme
noncomputable def ErrFMA_bounded_check (emin prec : Int)
    (choice : Int → Bool) (a x y : ℝ) : Unit :=
  ()

/-- Audit gap for Coq `ErrFMA_bounded`; the former theorem had postcondition
`True` and proved no boundedness property. -/
noncomputable def ErrFMA_bounded (emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ) :
    Unit :=
  ()

-- Coq: `ErrFMA_correct` — r1 + r2 + r3 = a*x + y
noncomputable def ErrFMA_correct_check (emin prec : Int)
    (choice : Int → Bool) (a x y : ℝ) : Unit :=
  ()

/-- Audit gap for Coq `ErrFMA_correct`; the former theorem had postcondition
`True` and proved no arithmetic equality. -/
noncomputable def ErrFMA_correct (emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ) :
    Unit :=
  ()

/-- Coq: `mult_error_FLT_ge_bpow'`.
Nearest-even specialization of `Prop.Mult_error.mult_error_FLT_ge_bpow`, with
the upstream zero-error disjunct and exponent weakening. -/
theorem mult_error_FLT_ge_bpow' (beta emin prec : Int) [Prec_gt_0 prec]
    (a b : ℝ) (e : Int)
    (hβ : 1 < beta)
    (ha : generic_format beta (FLT_exp emin prec) a)
    (hb : generic_format beta (FLT_exp emin prec) b)
    (hbound_or_zero :
      a * b = 0 ∨ FloatSpec.Core.Raux.bpow beta e ≤ |a * b|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
    a * b -
          FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * b) = 0 ∨
      FloatSpec.Core.Raux.bpow beta (e + 1 - 2 * prec) ≤
        |a * b -
          FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * b)| := by
  dsimp
  let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
  by_cases hzero :
      a * b - FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * b) = 0
  · exact Or.inl hzero
  · right
    rcases hbound_or_zero with hprod_zero | hprod_bound
    · have hround0 :=
        (FloatSpec.Calc.Round.round_0 (beta := beta) (fexp := FLT_exp emin prec)
          (mode := FloatSpec.Calc.Round.nearestEvenMode)) True.intro
      have hround0R :
          FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd 0 = 0 := by
        simpa [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode, rnd]
          using hround0
      have hdiff_zero :
          a * b - FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * b) = 0 := by
        simpa [hprod_zero, hround0R]
      exact False.elim (hzero hdiff_zero)
    · have hround_error_ne :
          FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * b) -
              a * b ≠ 0 := by
        intro hround_error_zero
        apply hzero
        linarith
      have hprod_bound' :
          FloatSpec.Core.Raux.bpow beta ((e + 1 - 2 * prec) + 2 * prec - 1) ≤
            |a * b| := by
        have hexp : (e + 1 - 2 * prec) + 2 * prec - 1 = e := by
          omega
        simpa [hexp] using hprod_bound
      have hcore :=
        mult_error_FLT_ge_bpow
          (beta := beta) (emin := emin) (prec := prec) (rnd := rnd)
          (x := a) (y := b) (e := e + 1 - 2 * prec)
          hβ ha hb hprod_bound' hround_error_ne
      simpa [abs_sub_comm] using hcore

-- Coq: `ErrFMA_bounded_simpl` — simplified boundedness of r1, r2, r3
noncomputable def ErrFMA_bounded_simpl_check (emin prec : Int)
    (a x y : ℝ) : Unit :=
  ()

-- Coq: `ErrFMA_bounded_simpl` — in the ErrFMA V2 setting (nearest-even),
-- the intermediate results `r1`, `r2`, `r3` are in format. We provide a
-- compatibility shell and defer the proof.
/-- Audit gap for Coq `ErrFMA_bounded_simpl`; the former theorem had
postcondition `True`. -/
noncomputable def ErrFMA_bounded_simpl (emin prec : Int) [Prec_gt_0 prec]
    (a x y : ℝ) :
    Unit :=
  ()

/-- Coq: `V2_Und2`.
In the ErrFMA V2 construction, with nearest-even rounding, non-underflow of `y`
implies the rounded `alpha1 := round_flt (y + u2)` is either zero or has
magnitude at least `bpow (emin + prec)`. -/
theorem V2_Und2 (beta emin prec : Int) [Prec_gt_0 prec]
    (a x y : ℝ)
    (hβ : 1 < beta) (hprec : 3 ≤ prec)
    (_Fa : generic_format beta (FLT_exp emin prec) a)
    (_Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (U1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) ≤ |a * x|)
    (U2 : y = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec) ≤ |y|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
    y ≠ 0 →
      alpha1 = 0 ∨
        FloatSpec.Core.Raux.bpow beta (emin + prec) ≤ |alpha1| := by
  dsimp
  intro hy_ne
  let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
  let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
  have hu2_fmt :
      generic_format beta (FLT_exp emin prec) u2 := by
    have hprod_err_fmt :
        generic_format beta (FLT_exp emin prec)
          (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) - a * x) := by
      exact
        mult_error_FLT
          (beta := beta) (prec := prec) (emin := emin) (rnd := rnd)
          (x := a) (y := x) hβ _Fa _Fx
          (by
            intro hax_ne
            rcases U1 with hzero | hbound
            · exact False.elim (hax_ne hzero)
            · have hpow_le :
                  FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤
                    FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) := by
                have hβR : (1 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast (le_of_lt hβ)
                have hexp_le : emin + 2 * prec - 1 ≤ emin + 4 * prec - 3 := by
                  omega
                simpa [FloatSpec.Core.Raux.bpow] using zpow_le_zpow_right₀ hβR hexp_le
              exact le_trans hpow_le hbound)
    have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := FLT_exp emin prec)
      (x := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) - a * x)
    simp only [wp, PostCond.noThrow, PredTrans.pure, Id.run, pure, Bind.bind] at hopp
    have hneg := hopp hprod_err_fmt
    simpa [u2, u1, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
  by_cases halpha1_zero : alpha1 = 0
  · exact Or.inl halpha1_zero
  · right
    have hy_bound :
        FloatSpec.Core.Raux.bpow beta ((emin + prec) + prec) ≤ |y| := by
      rcases U2 with hy_zero | hbound
      · exact False.elim (hy_ne hy_zero)
      · simpa [add_assoc, two_mul] using hbound
    exact round_FLT_plus_ge (beta := beta) (rnd := rnd)
      (emin := emin) (prec := prec) (x := y) (y := u2)
      (e := emin + prec) hβ Fy hu2_fmt hy_bound halpha1_zero

/-- Coq: `V2_Und4`.
In the ErrFMA V2 construction, with nearest-even rounding, non-underflow of
`a*x` implies the rounded `beta1 := round_flt (u1 + alpha1)` is either zero or
has magnitude at least `bpow (emin + prec + 1)`. -/
theorem V2_Und4 (beta emin prec : Int) [Prec_gt_0 prec]
    (a x y : ℝ)
    (hβ : 1 < beta) (hprec : 3 ≤ prec)
    (_Fa : generic_format beta (FLT_exp emin prec) a)
    (_Fx : generic_format beta (FLT_exp emin prec) x)
    (_Fy : generic_format beta (FLT_exp emin prec) y)
    (U1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) ≤ |a * x|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
    let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
    a * x ≠ 0 →
      beta1 = 0 ∨
        FloatSpec.Core.Raux.bpow beta (emin + prec + 1) ≤ |beta1| := by
  dsimp
  intro hax_ne
  let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
  let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
  let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
  have hU1_bound :
      FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) ≤ |a * x| := by
    rcases U1 with hzero | hbound
    · exact False.elim (hax_ne hzero)
    · exact hbound
  have hfmt_strong_bpow :
      generic_format beta (FLT_exp emin prec)
        (FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3)) := by
    have htrip := FloatSpec.Core.FLT.generic_format_FLT_bpow
      (prec := prec) (emin := emin) (beta := beta)
      (e := emin + 4 * prec - 3)
    have hemin_le : emin ≤ emin + 4 * prec - 3 := by
      omega
    simpa [FLT_exp, FloatSpec.Core.Raux.bpow] using htrip ⟨hβ, hemin_le⟩
  have hu1_strong :
      FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) ≤ |u1| := by
    by_cases hnonneg : 0 ≤ a * x
    · have hxle :
          FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) ≤ a * x := by
        simpa [abs_of_nonneg hnonneg] using hU1_bound
      have hle_round :
          FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) ≤ u1 := by
        exact FloatSpec.Core.Generic_fmt.roundR_ge_generic
          (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd)
          (x := FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3))
          (y := a * x) hβ hfmt_strong_bpow hxle
      exact le_trans hle_round (le_abs_self _)
    · have hnonpos : a * x ≤ 0 := le_of_not_ge hnonneg
      have hxle_neg :
          a * x ≤ -FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) := by
        have hle :
            FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) ≤ -(a * x) := by
          simpa [abs_of_nonpos hnonpos] using hU1_bound
        linarith
      have hfmt_neg :
          generic_format beta (FLT_exp emin prec)
            (-FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3)) := by
        have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
          (beta := beta) (fexp := FLT_exp emin prec)
          (x := FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3))
        simp only [wp, PostCond.noThrow, PredTrans.pure, Id.run, pure, Bind.bind] at hopp
        exact hopp hfmt_strong_bpow
      have hround_le :
          u1 ≤ -FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) := by
        exact FloatSpec.Core.Generic_fmt.roundR_le_generic
          (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd)
          (x := a * x)
          (y := -FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3))
          hβ hfmt_neg hxle_neg
      have hle_neg_round :
          FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) ≤ -u1 := by
        linarith
      exact le_trans hle_neg_round (neg_le_abs _)
  have hfmt_u1 :
      generic_format beta (FLT_exp emin prec) u1 := by
    simpa [u1, rnd] using
      (FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd)
        (x := a * x) hβ)
  have hfmt_alpha1 :
      generic_format beta (FLT_exp emin prec) alpha1 := by
    simpa [alpha1, u2, rnd] using
      (FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd)
        (x := y + u2) hβ)
  by_cases hbeta1_zero : beta1 = 0
  · exact Or.inl hbeta1_zero
  · right
    have hweaken :
        FloatSpec.Core.Raux.bpow beta ((emin + prec + 1) + prec) ≤ |u1| := by
      have hβR : (1 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast (le_of_lt hβ)
      have hpow_le :
          FloatSpec.Core.Raux.bpow beta ((emin + prec + 1) + prec) ≤
            FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) := by
        have hexp_le : (emin + prec + 1) + prec ≤ emin + 4 * prec - 3 := by
          omega
        simpa [FloatSpec.Core.Raux.bpow] using zpow_le_zpow_right₀ hβR hexp_le
      exact le_trans hpow_le hu1_strong
    exact round_FLT_plus_ge (beta := beta) (rnd := rnd)
      (emin := emin) (prec := prec) (x := u1) (y := alpha1)
      (e := emin + prec + 1) hβ hfmt_u1 hfmt_alpha1 hweaken hbeta1_zero

/-
Coq lemma: `ErrFMA_correct_simpl`

In the ErrFMA V2 section, Coq proves a simplified correctness result stating
that the compensated sum r1 + r2 + r3 equals a*x + y. We mirror the statement
with our hoare-triple style skeleton and defer the proof.
-/

noncomputable def ErrFMA_correct_simpl_check (emin prec : Int)
    (a x y : ℝ) : Unit :=
  ()

-- Coq: `ErrFMA_correct_simpl` — simplified equality r1 + r2 + r3 = a * x + y
-- under the ErrFMA V2 construction with ties-to-even rounding.
/-- Audit gap for Coq `ErrFMA_correct_simpl`; the former theorem had
postcondition `True`. -/
noncomputable def ErrFMA_correct_simpl (emin prec : Int) [Prec_gt_0 prec]
    (a x y : ℝ) :
    Unit :=
  ()

/-
Coq lemma: `ErrFmaAppr_correct`

In the ErrFmaApprox section, Coq establishes an a priori error bound for the
two-step approximation variant. The Flocq payload is not ported here, so this
entry is kept as a port-gap definition rather than a theorem claim.
-/

noncomputable def ErrFmaAppr_correct_check (emin prec : Int)
    (a x y : ℝ) : Unit :=
  ()

/-- Audit gap for Coq `ErrFmaAppr_correct`; the former theorem had
postcondition `True`. -/
noncomputable def ErrFmaAppr_correct (emin prec : Int) [Prec_gt_0 prec]
    (a x y : ℝ) :
    Unit :=
  ()

/-!
Coq lemma: `format_dp`

In the Discri1 context, `dp := b*b - p` where `p := round_flt (b*b)` is
represented in the target format. We mirror the statement by reconstructing
the local `let` bindings and asserting `generic_format` of `dp`.
-/

noncomputable def format_dp_check (emin prec : Int)
    (a b c : ℝ) : Unit :=
  ()

/-- Coq: `format_dp` — with `p := round_flt (b*b)` and `dp := b*b - p`,
    `dp` is representable in `generic_format 2 (FLT_exp emin prec)`.
    Here `round_flt := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) ()`. -/
theorem format_dp (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜generic_format 2 (FLT_exp emin prec) a ∧
        generic_format 2 (FLT_exp emin prec) b ∧
        generic_format 2 (FLT_exp emin prec) c ∧
        (b * b ≠ 0 → (2 : ℝ) ^ (emin + 3 * prec) ≤ |b * b|)⌝⦄
    (pure (format_dp_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) ()
            let p := round_flt (b * b)
            let dp := b * b - p
            generic_format 2 (FLT_exp emin prec) dp⌝⦄ := by
  apply Std.Do.Triple.pure
  intro hpre
  rcases hpre with ⟨_, hb, _, hunder⟩
  have hunder' : b * b ≠ 0 → FloatSpec.Core.Raux.bpow 2 (emin + 2 * prec - 1) ≤ |b * b| := by
    intro hne
    have hstrong := hunder hne
    have hpow_le :
        (2 : ℝ) ^ (emin + 2 * prec - 1) ≤ (2 : ℝ) ^ (emin + 3 * prec) := by
      exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by
        have hprec_pos : 0 < prec := Prec_gt_0.pos
        omega)
    simpa [FloatSpec.Core.Raux.bpow] using le_trans hpow_le hstrong
  have hmul :=
    mult_error_FLT
      (beta := 2) (prec := prec) (emin := emin)
      (rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t))))
      (x := b) (y := b) (by decide) hb hb
      hunder'
  have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
    (beta := 2) (fexp := FLT_exp emin prec) (x :=
      FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
        (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) (b * b) - b * b)
  simp only [wp, PostCond.noThrow, PredTrans.pure, Id.run, pure, Bind.bind] at hopp
  have hneg := hopp hmul
  simpa [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg

/-!
Coq lemma: `format_dq`

Symmetric to `format_dp`, with `q := round_flt (a*c)` and `dq := a*c - q`.
We assert `generic_format` of `dq` under the same Discri1 context assumptions.
-/

noncomputable def format_dq_check (emin prec : Int)
    (a b c : ℝ) : Unit :=
  ()

/-- Coq: `format_dq` — with `q := round_flt (a*c)` and `dq := a*c - q`,
    `dq` is representable in `generic_format 2 (FLT_exp emin prec)`.
    Here `round_flt := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) ()`. -/
theorem format_dq (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜generic_format 2 (FLT_exp emin prec) a ∧
        generic_format 2 (FLT_exp emin prec) b ∧
        generic_format 2 (FLT_exp emin prec) c ∧
        (a * c ≠ 0 → (2 : ℝ) ^ (emin + 3 * prec) ≤ |a * c|)⌝⦄
    (pure (format_dq_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) ()
            let q := round_flt (a * c)
            let dq := a * c - q
            generic_format 2 (FLT_exp emin prec) dq⌝⦄ := by
  apply Std.Do.Triple.pure
  intro hpre
  rcases hpre with ⟨ha, _, hc, hunder⟩
  have hunder' : a * c ≠ 0 → FloatSpec.Core.Raux.bpow 2 (emin + 2 * prec - 1) ≤ |a * c| := by
    intro hne
    have hstrong := hunder hne
    have hpow_le :
        (2 : ℝ) ^ (emin + 2 * prec - 1) ≤ (2 : ℝ) ^ (emin + 3 * prec) := by
      exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by
        have hprec_pos : 0 < prec := Prec_gt_0.pos
        omega)
    simpa [FloatSpec.Core.Raux.bpow] using le_trans hpow_le hstrong
  have hmul :=
    mult_error_FLT
      (beta := 2) (prec := prec) (emin := emin)
      (rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t))))
      (x := a) (y := c) (by decide) ha hc
      hunder'
  have hneg :
      generic_format 2 (FLT_exp emin prec)
        (-(FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
            (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) (a * c) - a * c)) := by
    have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := 2) (fexp := FLT_exp emin prec) (x :=
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
          (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) (a * c) - a * c)
    exact hopp hmul
  simpa [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg

/-!
Coq lemma: `U3_discri1`

In the Discri1 context, non-underflow of `b*b`, nonzero `a*c`, and
nonzero `p - q` imply a lower bound for the rounded difference
`round_flt (p - q)`.
-/

/-- Coq: `U3_discri1` — with
    `p := round_flt (b*b)` and `q := round_flt (a*c)`,
    if `b*b`, `a*c`, and `p - q` are nonzero, then
    `round_flt (p - q)` has magnitude at least `bpow (emin + 2*prec)`. -/
theorem U3_discri1 (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ)
    (_ha : generic_format 2 (FLT_exp emin prec) a)
    (_hb : generic_format 2 (FLT_exp emin prec) b)
    (_hc : generic_format 2 (FLT_exp emin prec) c)
    (U1 : b * b ≠ 0 →
      FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) ≤ |b * b|)
    (_U2 : a * c ≠ 0 →
      FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) ≤ |a * c|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
    let p := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (b * b)
    let q := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * c)
    b * b ≠ 0 →
      a * c ≠ 0 →
        p - q ≠ 0 →
          FloatSpec.Core.Raux.bpow 2 (emin + 2 * prec) ≤
            |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (p - q)| := by
  dsimp
  intro hbb_ne _hac_ne hpq_ne
  let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
  let p := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (b * b)
  let q := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * c)
  have hp_fmt : generic_format 2 (FLT_exp emin prec) p := by
    simpa [p, rnd] using
      (FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := 2) (fexp := FLT_exp emin prec) (rnd := rnd)
        (x := b * b) (by decide))
  have hq_fmt : generic_format 2 (FLT_exp emin prec) q := by
    simpa [q, rnd] using
      (FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := 2) (fexp := FLT_exp emin prec) (rnd := rnd)
        (x := a * c) (by decide))
  have hnegq_fmt : generic_format 2 (FLT_exp emin prec) (-q) := by
    have h := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := 2) (fexp := FLT_exp emin prec) (x := q)
    exact h hq_fmt
  have hbpow_fmt :
      generic_format 2 (FLT_exp emin prec)
        (FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec)) := by
    have htrip := FloatSpec.Core.FLT.generic_format_FLT_bpow
      (prec := prec) (emin := emin) (beta := 2) (e := emin + 3 * prec)
    have hemin_le : emin ≤ emin + 3 * prec := by
      have hprec_pos : 0 < prec := Prec_gt_0.pos
      omega
    simpa [FloatSpec.Core.Raux.bpow] using
      htrip ⟨(by decide : (2 : Int) > 1), hemin_le⟩
  have hbb_nonneg : 0 ≤ b * b := by nlinarith [sq_nonneg b]
  have hbpow_le_bb :
      FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) ≤ b * b := by
    simpa [abs_of_nonneg hbb_nonneg] using U1 hbb_ne
  have hbpow_le_p :
      FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) ≤ p := by
    exact FloatSpec.Core.Generic_fmt.roundR_ge_generic
      (beta := 2) (fexp := FLT_exp emin prec) (rnd := rnd)
      (x := FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec)) (y := b * b)
      (by decide) hbpow_fmt hbpow_le_bb
  have hp_bound :
      FloatSpec.Core.Raux.bpow 2 ((emin + 2 * prec) + prec) ≤ |p| := by
    have hexp : (emin + 2 * prec) + prec = emin + 3 * prec := by
      omega
    simpa [hexp] using le_trans hbpow_le_p (le_abs_self p)
  have hpq_sum_ne : p + -q ≠ 0 := by
    intro hsum
    apply hpq_ne
    linarith
  haveI : FloatSpec.Core.Generic_fmt.Monotone_exp (FLT_exp emin prec) := by
    simpa [FLT_exp] using
      (inferInstance :
        FloatSpec.Core.Generic_fmt.Monotone_exp
          (FloatSpec.Core.FLT.FLT_exp prec emin))
  haveI : FloatSpec.Core.Ulp.Exp_not_FTZ (FLT_exp emin prec) := by
    refine ⟨?_⟩
    intro k
    have hprec : 0 < prec := Prec_gt_0.pos
    let a : Int := max (k - prec) emin
    change max (a + 1 - prec) emin ≤ a
    exact max_le (by omega) (by simp [a])
  have hround_ne :
      FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (p + -q) ≠ 0 := by
    exact round_plus_neq_0 (beta := 2) (fexp := FLT_exp emin prec)
      (rnd := rnd) (x := p) (y := -q) (by decide)
      hp_fmt hnegq_fmt hpq_sum_ne
  have hmain :=
    round_FLT_plus_ge (beta := 2) (rnd := rnd)
      (emin := emin) (prec := prec) (x := p) (y := -q)
      (e := emin + 2 * prec) (by decide) hp_fmt hnegq_fmt
      hp_bound hround_ne
  simpa [p, q, rnd, sub_eq_add_neg] using hmain

/-!
Coq lemma: `U4_discri1`

In the Discri1 context, if the computed discriminant branch result `d` is
nonzero, then the final value has the weaker lower bound
`bpow (emin + prec)`. The direct branch weakens `U3_discri1`; the compensated
branch applies `round_FLT_plus_ge` to the two rounded summands.
-/

/-- Coq: `U4_discri1` — with
    `p := round_flt (b*b)`, `q := round_flt (a*c)`,
    `dp := b*b - p`, `dq := a*c - q`, and
    `d := if p + q ≤ 3*|p - q| then round_flt (p - q)
          else round_flt (round_flt (p - q) + round_flt (dp - dq))`,
    nonzero inputs and `p - q ≠ 0` imply
    `bpow (emin + prec) ≤ |d|`. -/
theorem U4_discri1 (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ)
    (_ha : generic_format 2 (FLT_exp emin prec) a)
    (_hb : generic_format 2 (FLT_exp emin prec) b)
    (_hc : generic_format 2 (FLT_exp emin prec) c)
    (U1 : b * b ≠ 0 →
      FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) ≤ |b * b|)
    (U2 : a * c ≠ 0 →
      FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) ≤ |a * c|)
    (Zd :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
      let p := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (b * b)
      let q := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * c)
      let dp := b * b - p
      let dq := a * c - q
      let d := if p + q ≤ 3 * |p - q|
        then FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (p - q)
        else FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
          (FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (p - q) +
            FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (dp - dq))
      d ≠ 0) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
    let p := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (b * b)
    let q := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * c)
    let dp := b * b - p
    let dq := a * c - q
    let d := if p + q ≤ 3 * |p - q|
      then FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (p - q)
      else FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
        (FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (p - q) +
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (dp - dq))
    b * b ≠ 0 →
      a * c ≠ 0 →
        p - q ≠ 0 →
          FloatSpec.Core.Raux.bpow 2 (emin + prec) ≤ |d| := by
  dsimp at Zd ⊢
  intro hbb_ne hac_ne hpq_ne
  let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
  let p := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (b * b)
  let q := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * c)
  let dp := b * b - p
  let dq := a * c - q
  have hU3 :
      FloatSpec.Core.Raux.bpow 2 (emin + 2 * prec) ≤
        |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (p - q)| := by
    have h :=
      U3_discri1 (emin := emin) (prec := prec) (a := a) (b := b) (c := c)
        _ha _hb _hc U1 U2
    simpa [rnd, p, q] using h hbb_ne hac_ne hpq_ne
  by_cases hcond : p + q ≤ 3 * |p - q|
  · have hbpow_le :
        FloatSpec.Core.Raux.bpow 2 (emin + prec) ≤
          FloatSpec.Core.Raux.bpow 2 (emin + 2 * prec) := by
      have hprec_nonneg : 0 ≤ prec := le_of_lt (Prec_gt_0.pos : 0 < prec)
      simpa [FloatSpec.Core.Raux.bpow] using
        (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega :
          emin + prec ≤ emin + 2 * prec))
    exact by
      simpa [rnd, p, q, dp, dq, hcond] using le_trans hbpow_le hU3
  · have hdiff_fmt :
        generic_format 2 (FLT_exp emin prec)
          (FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (p - q)) := by
      exact FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := 2) (fexp := FLT_exp emin prec) (rnd := rnd)
        (x := p - q) (by decide)
    have hdpdq_fmt :
        generic_format 2 (FLT_exp emin prec)
          (FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (dp - dq)) := by
      exact FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := 2) (fexp := FLT_exp emin prec) (rnd := rnd)
        (x := dp - dq) (by decide)
    have houter_ne :
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
          (FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (p - q) +
            FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (dp - dq)) ≠ 0 := by
      simpa [rnd, p, q, dp, dq, hcond] using Zd
    have hbound :
        FloatSpec.Core.Raux.bpow 2 ((emin + prec) + prec) ≤
          |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (p - q)| := by
      have hexp : (emin + prec) + prec = emin + 2 * prec := by omega
      simpa [hexp] using hU3
    have hmain :=
      round_FLT_plus_ge (beta := 2) (rnd := rnd)
        (emin := emin) (prec := prec)
        (x := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (p - q))
        (y := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (dp - dq))
        (e := emin + prec) (by decide) hdiff_fmt hdpdq_fmt hbound houter_ne
    simpa [rnd, p, q, dp, dq, hcond] using hmain

/-!
Coq lemma: `format_d_discri1`

With `d` defined from `p, q, dp, dq` and a conditional on `p+q ≤ 3*|p-q|`,
`d` is in the target `generic_format`. This follows since `d` is the rounding
of either `p - q` or `round_flt (p - q) + round_flt (dp - dq)`.
-/

noncomputable def format_d_discri1_check (emin prec : Int)
    (a b c : ℝ) : Unit :=
  ()

/-- Coq: `format_d_discri1` — with local definitions
    `p := round_flt (b*b)`, `q := round_flt (a*c)`, `dp := b*b - p`,
    `dq := a*c - q`, and
    `d := if p + q ≤ 3*|p - q| then round_flt (p - q)
          else round_flt (round_flt (p - q) + round_flt (dp - dq))`,
    the value `d` is representable in `generic_format 2 (FLT_exp emin prec)`.
    Here `round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()`. -/
theorem format_d_discri1 (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜True⌝⦄
    (pure (format_d_discri1_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) ()
            let p := round_flt (b * b)
            let q := round_flt (a * c)
            let dp := b * b - p
            let dq := a * c - q
            let d := if (p + q ≤ 3 * |p - q|)
                     then round_flt (p - q)
                     else round_flt (round_flt (p - q) + round_flt (dp - dq))
            generic_format 2 (FLT_exp emin prec) d⌝⦄ := by
  apply Std.Do.Triple.pure
  intro _
  dsimp
  by_cases hcond :
      FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (b * b) +
        FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (a * c) ≤
        3 * |FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (b * b) -
          FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (a * c)|
  · simp [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode] at hcond ⊢
    rw [if_pos hcond]
    simpa [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode] using
      FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := 2) (fexp := FLT_exp emin prec)
      (rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t))))
      (x := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (b * b) -
        FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (a * c)) (by decide)
  · simp [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode] at hcond ⊢
    rw [if_neg (not_le_of_gt hcond)]
    simpa [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode] using
      FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := 2) (fexp := FLT_exp emin prec)
      (rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t))))
      (x :=
        FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) ()
          (FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (b * b) -
            FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (a * c)) +
        FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) ()
          ((b * b -
              FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (b * b)) -
            (a * c -
              FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (a * c)))) (by decide)

/-!
Coq lemma: `format_d_discri2`

A companion to `format_d_discri1`, ensuring that with the same local
definitions for `p, q, dp, dq` and `d`, the value `d` is representable in
`generic_format 2 (FLT_exp emin prec)`.
-/

noncomputable def format_d_discri2_check (emin prec : Int)
    (a b c : ℝ) : Unit :=
  ()

/-- Coq: `format_d_discri2` — with local definitions
    `p := round_flt (b*b)`, `q := round_flt (a*c)`, `dp := b*b - p`,
    `dq := a*c - q`, and
    `d := if p + q ≤ 3*|p - q| then round_flt (p - q)
          else round_flt (round_flt (p - q) + round_flt (dp - dq))`,
    the value `d` is representable in `generic_format 2 (FLT_exp emin prec)`.
    Here `round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()`.
    Proof deferred. -/
theorem format_d_discri2 (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜True⌝⦄
    (pure (format_d_discri2_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) ()
            let p := round_flt (b * b)
            let q := round_flt (a * c)
            let dp := b * b - p
            let dq := a * c - q
            let d := if (p + q ≤ 3 * |p - q|)
                     then round_flt (p - q)
                     else round_flt (round_flt (p - q) + round_flt (dp - dq))
            generic_format 2 (FLT_exp emin prec) d⌝⦄ := by
  apply Std.Do.Triple.pure
  intro _
  dsimp
  by_cases hcond :
      FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (b * b) +
        FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (a * c) ≤
        3 * |FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (b * b) -
          FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (a * c)|
  · simp [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode] at hcond ⊢
    rw [if_pos hcond]
    simpa [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode] using
      FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := 2) (fexp := FLT_exp emin prec)
      (rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t))))
      (x := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (b * b) -
        FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (a * c)) (by decide)
  · simp [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode] at hcond ⊢
    rw [if_neg (not_le_of_gt hcond)]
    simpa [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode] using
      FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := 2) (fexp := FLT_exp emin prec)
      (rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t))))
      (x :=
        FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) ()
          (FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (b * b) -
            FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (a * c)) +
        FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) ()
          ((b * b -
              FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (b * b)) -
            (a * c -
              FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) () (a * c)))) (by decide)

/-!
Coq lemma: `U5_discri1_aux`

Auxiliary bound: if two formatted values `x` and `y` are both at least
`bpow e` in magnitude, `emin ≤ e`, and rounding `x + y` is not exact, then the
rounded sum has magnitude at least `bpow e`.
-/

/-- Coq: `U5_discri1_aux` — with
    `round_flt := round 2 (FLT_exp emin prec) ZnearestE`, if `x` and `y` are
    in format, `emin ≤ e`, `bpow e ≤ |x|`, `bpow e ≤ |y|`, and rounding
    `x + y` is not exact, then `bpow e ≤ |round_flt (x + y)|`. -/
theorem U5_discri1_aux (emin prec : Int) [Prec_gt_0 prec]
    (x y : ℝ) (e : Int)
    (hx : generic_format 2 (FLT_exp emin prec) x)
    (hy : generic_format 2 (FLT_exp emin prec) y)
    (hemin : emin ≤ e)
    (hx_bound : FloatSpec.Core.Raux.bpow 2 e ≤ |x|)
    (hy_bound : FloatSpec.Core.Raux.bpow 2 e ≤ |y|)
    (hne :
      FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
        (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t))))
        (x + y) ≠ x + y) :
    FloatSpec.Core.Raux.bpow 2 e ≤
      |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
        (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t))))
        (x + y)| := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
  have hfmt_bpow :
      generic_format 2 (FLT_exp emin prec) (FloatSpec.Core.Raux.bpow 2 e) := by
    have htrip := FloatSpec.Core.FLT.generic_format_FLT_bpow
      (prec := prec) (emin := emin) (beta := 2) (e := e)
    simpa [FloatSpec.Core.Raux.bpow] using
      htrip ⟨(by decide : (2 : Int) > 1), hemin⟩
  by_cases hlarge : FloatSpec.Core.Raux.bpow 2 e ≤ |x + y|
  · by_cases hsum_nonneg : 0 ≤ x + y
    · have hle_sum :
          FloatSpec.Core.Raux.bpow 2 e ≤ x + y := by
        simpa [abs_of_nonneg hsum_nonneg] using hlarge
      have hround_le :
          FloatSpec.Core.Raux.bpow 2 e ≤
            FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (x + y) :=
        FloatSpec.Core.Generic_fmt.roundR_ge_generic
          (beta := 2) (fexp := FLT_exp emin prec) (rnd := rnd)
          (x := FloatSpec.Core.Raux.bpow 2 e) (y := x + y)
          (by decide : (1 : Int) < 2) hfmt_bpow hle_sum
      exact le_trans hround_le (le_abs_self _)
    · have hsum_nonpos : x + y ≤ 0 := le_of_not_ge hsum_nonneg
      have hle_neg_sum :
          FloatSpec.Core.Raux.bpow 2 e ≤ -(x + y) := by
        simpa [abs_of_nonpos hsum_nonpos] using hlarge
      have hround_le :
          FloatSpec.Core.Raux.bpow 2 e ≤
            FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
              (FloatSpec.Core.Generic_fmt.Zrnd_opp rnd) (-(x + y)) :=
        FloatSpec.Core.Generic_fmt.roundR_ge_generic
          (beta := 2) (fexp := FLT_exp emin prec)
          (rnd := FloatSpec.Core.Generic_fmt.Zrnd_opp rnd)
          (x := FloatSpec.Core.Raux.bpow 2 e) (y := -(x + y))
          (by decide : (1 : Int) < 2) hfmt_bpow hle_neg_sum
      have hopp :
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (x + y) =
            -FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
              (FloatSpec.Core.Generic_fmt.Zrnd_opp rnd) (-(x + y)) := by
        have h := FloatSpec.Core.Generic_fmt.roundR_opp
          (beta := 2) (fexp := FLT_exp emin prec) (rnd := rnd)
          (x := -(x + y)) (by decide : (1 : Int) < 2)
        simpa using h
      have habs :
          |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (x + y)| =
            |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
              (FloatSpec.Core.Generic_fmt.Zrnd_opp rnd) (-(x + y))| := by
        rw [hopp, abs_neg]
      rw [habs]
      exact le_trans hround_le
        (le_abs_self
          (FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
            (FloatSpec.Core.Generic_fmt.Zrnd_opp rnd) (-(x + y))))
  · have hsum_abs_lt : |x + y| < FloatSpec.Core.Raux.bpow 2 e := lt_of_not_ge hlarge
    have hx_ne : x ≠ 0 := by
      intro hx0
      have hpow_pos : 0 < FloatSpec.Core.Raux.bpow 2 e := by
        simpa [FloatSpec.Core.Raux.bpow] using
          (zpow_pos (by norm_num : (0 : ℝ) < 2) e)
      have : FloatSpec.Core.Raux.bpow 2 e ≤ 0 := by
        simpa [hx0] using hx_bound
      exact (not_lt_of_ge this) hpow_pos
    have hy_ne : y ≠ 0 := by
      intro hy0
      have hpow_pos : 0 < FloatSpec.Core.Raux.bpow 2 e := by
        simpa [FloatSpec.Core.Raux.bpow] using
          (zpow_pos (by norm_num : (0 : ℝ) < 2) e)
      have : FloatSpec.Core.Raux.bpow 2 e ≤ 0 := by
        simpa [hy0] using hy_bound
      exact (not_lt_of_ge this) hpow_pos
    have hsum_small :
        |x + y| ≤ min |x| |y| := by
      have hbpow_le_min : FloatSpec.Core.Raux.bpow 2 e ≤ min |x| |y| :=
        le_min hx_bound hy_bound
      exact le_trans (le_of_lt hsum_abs_lt) hbpow_le_min
    haveI : FloatSpec.Core.Generic_fmt.Monotone_exp (FLT_exp emin prec) := by
      simpa [FLT_exp] using
        (inferInstance :
          FloatSpec.Core.Generic_fmt.Monotone_exp
            (FloatSpec.Core.FLT.FLT_exp prec emin))
    have hsum_fmt : generic_format 2 (FLT_exp emin prec) (x + y) :=
      generic_format_plus_weak (beta := 2) (fexp := FLT_exp emin prec)
        x y hx hy (by decide : (1 : Int) < 2) hsum_small
    have hround_eq :
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (x + y) = x + y :=
      FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := 2) (fexp := FLT_exp emin prec) (rnd := rnd)
        (x := x + y) (by decide : (1 : Int) < 2) hsum_fmt
    exact False.elim (hne hround_eq)

/-!
Coq lemma: `U5_discri1`

In the Discri1 context, nonzero products and a non-exact rounded compensation
term imply the lower bound `bpow (emin + prec - 1)` for `round_flt (dp - dq)`.
-/

/-- Coq: `U5_discri1` — with
    `p := round_flt (b*b)`, `q := round_flt (a*c)`,
    `dp := b*b - p`, and `dq := a*c - q`, if `b*b` and `a*c` are nonzero and
    rounding `dp - dq` is not exact, then
    `bpow (emin + prec - 1) ≤ |round_flt (dp - dq)|`. -/
theorem U5_discri1 (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ)
    (ha : generic_format 2 (FLT_exp emin prec) a)
    (hb : generic_format 2 (FLT_exp emin prec) b)
    (hc : generic_format 2 (FLT_exp emin prec) c)
    (U1 : b * b ≠ 0 →
      FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) ≤ |b * b|)
    (U2 : a * c ≠ 0 →
      FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) ≤ |a * c|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
    let p := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (b * b)
    let q := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * c)
    let dp := b * b - p
    let dq := a * c - q
    b * b ≠ 0 →
      a * c ≠ 0 →
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (dp - dq) ≠
          dp - dq →
          FloatSpec.Core.Raux.bpow 2 (emin + prec - 1) ≤
            |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (dp - dq)| := by
  dsimp
  intro hbb_ne hac_ne hne
  let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
  let p := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (b * b)
  let q := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * c)
  let dp := b * b - p
  let dq := a * c - q
  have hdp_fmt : generic_format 2 (FLT_exp emin prec) dp := by
    have hpre :
        b * b ≠ 0 → FloatSpec.Core.Raux.bpow 2 (emin + 2 * prec - 1) ≤ |b * b| := by
      intro hne'
      have hpow_le :
          FloatSpec.Core.Raux.bpow 2 (emin + 2 * prec - 1) ≤
            FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) := by
        have hmono := FloatSpec.Core.Raux.bpow_le (beta := 2)
          (e1 := emin + 2 * prec - 1) (e2 := emin + 3 * prec)
          (by decide : (1 : Int) < 2) (by
            have hprec_pos : 0 < prec := Prec_gt_0.pos
            omega)
        simpa [FloatSpec.Core.Raux.bpow, FloatSpec.Core.Raux.bpow_le_check,
          wp, PostCond.noThrow, Id.run, pure]
          using hmono True.intro
      exact le_trans hpow_le (U1 hne')
    have hmul :=
      mult_error_FLT
        (beta := 2) (prec := prec) (emin := emin) (rnd := rnd)
        (x := b) (y := b) (by decide) hb hb hpre
    have hneg :
        generic_format 2 (FLT_exp emin prec) (-(p - b * b)) := by
      exact FloatSpec.Core.Generic_fmt.generic_format_opp
        (beta := 2) (fexp := FLT_exp emin prec) (x := p - b * b) hmul
    simpa [dp, p, rnd, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
  have hdq_fmt : generic_format 2 (FLT_exp emin prec) dq := by
    have hpre :
        a * c ≠ 0 → FloatSpec.Core.Raux.bpow 2 (emin + 2 * prec - 1) ≤ |a * c| := by
      intro hne'
      have hpow_le :
          FloatSpec.Core.Raux.bpow 2 (emin + 2 * prec - 1) ≤
            FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) := by
        have hmono := FloatSpec.Core.Raux.bpow_le (beta := 2)
          (e1 := emin + 2 * prec - 1) (e2 := emin + 3 * prec)
          (by decide : (1 : Int) < 2) (by
            have hprec_pos : 0 < prec := Prec_gt_0.pos
            omega)
        simpa [FloatSpec.Core.Raux.bpow, FloatSpec.Core.Raux.bpow_le_check,
          wp, PostCond.noThrow, Id.run, pure]
          using hmono True.intro
      exact le_trans hpow_le (U2 hne')
    have hmul :=
      mult_error_FLT
        (beta := 2) (prec := prec) (emin := emin) (rnd := rnd)
        (x := a) (y := c) (by decide) ha hc hpre
    have hneg :
        generic_format 2 (FLT_exp emin prec) (-(q - a * c)) := by
      exact FloatSpec.Core.Generic_fmt.generic_format_opp
        (beta := 2) (fexp := FLT_exp emin prec) (x := q - a * c) hmul
    simpa [dq, q, rnd, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
  have hneg_dq_fmt : generic_format 2 (FLT_exp emin prec) (-dq) := by
    exact FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := 2) (fexp := FLT_exp emin prec) (x := dq) hdq_fmt
  have hdp_bound :
      FloatSpec.Core.Raux.bpow 2 (emin + prec - 1) ≤ |dp| := by
    have hraw := mult_error_FLT_ge_bpow'
      (beta := 2) (emin := emin) (prec := prec)
      (a := b) (b := b) (e := emin + 3 * prec)
      (by decide : (1 : Int) < 2) hb hb (Or.inr (U1 hbb_ne))
    have hnonzero :
        b * b - p ≠ 0 := by
      intro hz
      apply hne
      have hround_exact : p = b * b := by linarith
      have hdp_zero : dp = 0 := by simp [dp, hround_exact]
      have hsum_fmt : generic_format 2 (FLT_exp emin prec) (dp - dq) := by
        simpa [hdp_zero, zero_sub] using hneg_dq_fmt
      have hround_eq :
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (dp - dq) =
            dp - dq :=
        FloatSpec.Core.Generic_fmt.roundR_generic
          (beta := 2) (fexp := FLT_exp emin prec) (rnd := rnd)
          (x := dp - dq) (by decide : (1 : Int) < 2) hsum_fmt
      exact hround_eq
    rcases hraw with hzero | hbound
    · exact False.elim (hnonzero hzero)
    · have hexp : emin + 3 * prec + 1 - 2 * prec = emin + prec + 1 := by omega
      have hweaken :
          FloatSpec.Core.Raux.bpow 2 (emin + prec - 1) ≤
            FloatSpec.Core.Raux.bpow 2 (emin + prec + 1) := by
        have hmono := FloatSpec.Core.Raux.bpow_le (beta := 2)
          (e1 := emin + prec - 1) (e2 := emin + prec + 1)
          (by decide : (1 : Int) < 2) (by omega)
        simpa [FloatSpec.Core.Raux.bpow, FloatSpec.Core.Raux.bpow_le_check,
          wp, PostCond.noThrow, Id.run, pure]
          using hmono True.intro
      have hbound' :
          FloatSpec.Core.Raux.bpow 2 (emin + prec + 1) ≤ |dp| := by
        simpa [dp, p, rnd, hexp, abs_sub_comm] using hbound
      exact le_trans hweaken hbound'
  have hdq_bound :
      FloatSpec.Core.Raux.bpow 2 (emin + prec - 1) ≤ |-dq| := by
    have hraw := mult_error_FLT_ge_bpow'
      (beta := 2) (emin := emin) (prec := prec)
      (a := a) (b := c) (e := emin + 3 * prec)
      (by decide : (1 : Int) < 2) ha hc (Or.inr (U2 hac_ne))
    have hnonzero :
        a * c - q ≠ 0 := by
      intro hz
      apply hne
      have hround_exact : q = a * c := by linarith
      have hdq_zero : dq = 0 := by simp [dq, hround_exact]
      have hsum_fmt : generic_format 2 (FLT_exp emin prec) (dp - dq) := by
        simpa [hdq_zero, sub_zero] using hdp_fmt
      have hround_eq :
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (dp - dq) =
            dp - dq :=
        FloatSpec.Core.Generic_fmt.roundR_generic
          (beta := 2) (fexp := FLT_exp emin prec) (rnd := rnd)
          (x := dp - dq) (by decide : (1 : Int) < 2) hsum_fmt
      exact hround_eq
    rcases hraw with hzero | hbound
    · exact False.elim (hnonzero hzero)
    · have hexp : emin + 3 * prec + 1 - 2 * prec = emin + prec + 1 := by omega
      have hweaken :
          FloatSpec.Core.Raux.bpow 2 (emin + prec - 1) ≤
            FloatSpec.Core.Raux.bpow 2 (emin + prec + 1) := by
        have hmono := FloatSpec.Core.Raux.bpow_le (beta := 2)
          (e1 := emin + prec - 1) (e2 := emin + prec + 1)
          (by decide : (1 : Int) < 2) (by omega)
        simpa [FloatSpec.Core.Raux.bpow, FloatSpec.Core.Raux.bpow_le_check,
          wp, PostCond.noThrow, Id.run, pure]
          using hmono True.intro
      have hbound' :
          FloatSpec.Core.Raux.bpow 2 (emin + prec + 1) ≤ |-dq| := by
        simpa [dq, q, rnd, hexp, abs_neg, abs_sub_comm] using hbound
      exact le_trans hweaken hbound'
  have hmain := U5_discri1_aux (emin := emin) (prec := prec)
    (x := dp) (y := -dq) (e := emin + prec - 1)
    hdp_fmt hneg_dq_fmt (by
      have hprec_pos : 0 < prec := Prec_gt_0.pos
      omega) hdp_bound hdq_bound
  simpa [rnd, p, q, dp, dq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using hmain hne
