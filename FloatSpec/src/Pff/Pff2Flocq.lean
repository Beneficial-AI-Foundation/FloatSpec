import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Pff.Pff
import FloatSpec.src.Prop.Mult_error
import FloatSpec.src.Prop.Plus_error
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
  have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
    (beta := 2) (fexp := FLT_exp emin prec) (x :=
      FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
        (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) (a * c) - a * c)
  simp only [wp, PostCond.noThrow, PredTrans.pure, Id.run, pure, Bind.bind] at hopp
  have hneg := hopp hmul
  simpa [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg

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
