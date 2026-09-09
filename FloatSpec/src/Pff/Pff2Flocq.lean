import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Pff.Pff
import FloatSpec.src.Pff.Pff2FlocqAux
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

set_option linter.style.haveILetI false

-- Keep source/target value bridges stable under Lean 4.33 simplification.
attribute [-simp] FloatSpec.Core.Defs.F2R_run

-- Conversion functions between Pff and Flocq representations

variable (beta : Int) [ValidRadix beta]

private theorem bpow_le_plain (beta e1 e2 : Int) [ValidRadix beta]
    (hβ : 1 < beta) (hle : e1 ≤ e2) :
    FloatSpec.Core.Raux.bpow beta e1 ≤ FloatSpec.Core.Raux.bpow beta e2 := by
  change (beta : ℝ) ^ e1 ≤ (beta : ℝ) ^ e2
  exact FloatSpec.Core.Raux.bpow_le beta e1 e2 hβ hle True.intro

-- Convert Pff float to Flocq float
def pff_to_float (f : PffFloat beta) : FloatSpec.Core.Defs.FlocqFloat beta :=
  pff_to_flocq beta f

-- Convert Flocq float to real number via Pff
noncomputable def pff_to_R (f : PffFloat beta) : ℝ :=
  _root_.F2R (pff_to_flocq beta f)

-- Conversion preserves value
theorem pff_flocq_equiv (f : PffFloat beta) :
  pff_to_R beta f = _root_.F2R (pff_to_flocq beta f) := by
  rfl

-- Conversion is bijective for valid inputs
theorem pff_flocq_bijection (f : FloatSpec.Core.Defs.FlocqFloat beta) :
  pff_to_flocq beta (flocq_to_pff f) = f := by
  rfl

theorem flocq_pff_bijection (f : PffFloat beta) :
  flocq_to_pff (pff_to_flocq beta f) = f := by
  rfl

-- Pff operations match Flocq operations
theorem pff_add_equiv (x y : PffFloat beta) :
  pff_to_R beta (pff_add beta x y) =
  _root_.F2R (FloatSpec.Calc.Operations.Fplus beta (pff_to_flocq beta x) (pff_to_flocq beta y)) := by
  -- Unfold pff_to_R and pff_add
  unfold pff_to_R pff_add
  -- Use the bijection lemma: pff_to_flocq (flocq_to_pff f) = f
  rw [pff_flocq_bijection]

theorem pff_mul_equiv (x y : PffFloat beta) :
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
Theorems imported from Coq Pff2Flocq.v

We follow the project convention: introduce a `_check` function and state each
theorem using the Hoare-triple style, with closed proofs and descriptive helper
witnesses where proof reconstruction benefits from factoring.
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
private lemma cexp_neg_eq (b emin prec : Int) [ValidRadix b] (x : ℝ) :
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

/-- Raw `roundR` nearest rounding sends zero to zero. -/
private lemma roundR_Znearest_zero (emin prec : Int) (choice : Int → Bool) :
    FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
      (FloatSpec.Core.Generic_fmt.Znearest choice) 0 = 0 := by
  unfold FloatSpec.Core.Generic_fmt.roundR FloatSpec.Core.Generic_fmt.scaled_mantissa
  simp only [zero_mul]
  have hz : ((FloatSpec.Core.Generic_fmt.Znearest choice (0 : ℝ) : Int) : ℝ) = 0 := by
    exact_mod_cast (Znearest_of_int choice 0)
  simpa [hz]

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
  simpa only [Bool.not_not, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h

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

-- Coq: `Fast2Sum_correct`
noncomputable def Fast2Sum_round
    (emin prec : Int) (choice : Int → Bool) (z : ℝ) : ℝ :=
  FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
    (FloatSpec.Core.Generic_fmt.Znearest choice) z

noncomputable def Fast2Sum_result
    (emin prec : Int) (choice : Int → Bool) (x y : ℝ) : Prop :=
  let a := Fast2Sum_round emin prec choice (x + y)
  let b := Fast2Sum_round emin prec choice
    (y + Fast2Sum_round emin prec choice (x - a))
  a + b = x + y

noncomputable def Fast2Sum_correct_check
    (emin prec : Int) (choice : Int → Bool) (x y : ℝ) : Unit :=
  ()

/-- Coq: `Fast2Sum_correct`.

For FLT radix-2 inputs `x` and `y`, the Fast2Sum correction term restores the
exact sum when `|y| <= |x|`. -/
theorem Fast2Sum_correct (emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (x y : ℝ) :
    ⦃⌜precisionNotZero prec ∧ emin ≤ 0 ∧
        (∀ t : Int, choice t = ! choice (-(t + 1))) ∧
        generic_format 2 (FLT_exp emin prec) x ∧
        generic_format 2 (FLT_exp emin prec) y ∧ |y| ≤ |x|⌝⦄
    (pure (Fast2Sum_correct_check emin prec choice x y) : Id Unit)
    ⦃⇓_ => ⌜Fast2Sum_result emin prec choice x y⌝⦄ := by
  intro h
  rcases h with ⟨hprec, hemin, hchoice, hx_fmt, hy_fmt, hAbs⟩
  simp only [wp, PostCond.noThrow, pure, Fast2Sum_correct_check, Id.run,
    ULift.up_down]
  let round_flt : ℝ → ℝ := fun z =>
    FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
      (FloatSpec.Core.Generic_fmt.Znearest choice) z
  let bnd : Fbound := make_bound 2 prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  have hbeta : (1 : Int) < 2 := by decide
  have hbnd_dExp : -bnd.dExp = emin := by
    have h := make_bound_Emin 2 prec emin (hp := by exact hprec)
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using h hemin
    omega
  have hpBound : pGivesBound 2 bnd prec := by
    have h := make_bound_p 2 prec emin (hp := by exact hprec)
    have hv : (make_bound 2 prec emin).vNum =
        Zpower_nat 2 (prec.natAbs) := by
      simpa [wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound, bnd] using hv
  have hx_fmt_bnd : generic_format 2 (FLT_exp (-bnd.dExp) prec) x := by
    simpa [hbnd_dExp] using hx_fmt
  have hy_fmt_bnd : generic_format 2 (FLT_exp (-bnd.dExp) prec) y := by
    simpa [hbnd_dExp] using hy_fmt
  rcases (by
      have h := format_is_flocq_bounded 2 bnd prec x
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨hx_fmt_bnd, hpBound, hprec, hbeta⟩) with
    ⟨fx, hfx_val, hfx_bound⟩
  rcases (by
      have h := format_is_flocq_bounded 2 bnd prec y
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨hy_fmt_bnd, hpBound, hprec, hbeta⟩) with
    ⟨fy, hfy_val, hfy_bound⟩
  have hprec_pos : (0 : Int) < prec := lt_trans Int.zero_lt_one hprec
  have hprec_nonneg : (0 : Int) ≤ prec := le_of_lt hprec_pos
  have hprec_toNat_abs : prec.natAbs = prec.toNat := by
    apply Nat.cast_injective (R := Int)
    rw [Int.natAbs_of_nonneg hprec_nonneg, Int.toNat_of_nonneg hprec_nonneg]
  have hpBound_toNat : bnd.vNum = Zpower_nat 2 prec.toNat := by
    unfold pGivesBound at hpBound
    calc
      bnd.vNum = Zpower_nat 2 (prec.natAbs) := hpBound
      _ = Zpower_nat 2 prec.toNat := by rw [hprec_toNat_abs]
  have hvNum : bo.vNum = Zpower_nat 2 prec.toNat := by
    unfold bo toFboundSkel
    exact hpBound_toNat
  have hprecision_nat_ne : prec.toNat ≠ 0 := by
    have htoNat_pos : 0 < prec.toNat := by omega
    exact Nat.ne_of_gt htoNat_pos
  have hvNum_gt : (1 : Int) < bo.vNum := by
    rw [hvNum, Zpower_nat]
    exact one_lt_pow₀ (by decide : (1 : Int) < 2) hprecision_nat_ne
  have hBoundExpAll :
      ∀ r : ℝ, -bo.dExp ≤ (boundR (beta:=2) 2 r).Fexp := by
    intro r
    simpa [bo, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using make_bound_boundR_exp_box 2 prec emin r
  have hMinTotal : TotalP (isMin (beta:=2) bo 2) := by
    intro r
    have h := MinEx_from_finite_box_payload (beta:=2) bo 2 r
    simpa only [wp, PostCond.noThrow, pure, MinEx_check, Id.run,
      ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨rfl, hbeta, hvNum_gt, hBoundExpAll r⟩
  have hMaxTotal : TotalP (isMax (beta:=2) bo 2) := by
    intro r
    have h := MaxEx_from_finite_box_payload (beta:=2) bo 2 r
    simpa only [wp, PostCond.noThrow, pure, MaxEx_check, Id.run,
      ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨rfl, hbeta, hvNum_gt, hBoundExpAll r⟩
  have hTotal : TotalP (Closest (beta:=2) bo (2 : ℝ)) := by
    intro r
    have h := ClosestTotal_from_extrema_payload (beta:=2) bo 2 (2 : ℝ) r
    simpa only [wp, PostCond.noThrow, pure, ClosestTotal_check, Id.run,
      ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨hMinTotal, hMaxTotal⟩
  let Iplus :
      FloatSpec.Core.Defs.FlocqFloat 2 →
        FloatSpec.Core.Defs.FlocqFloat 2 →
          FloatSpec.Core.Defs.FlocqFloat 2 :=
    fun f g => RND_Closest (beta:=2) bo 2 prec choice
      (_root_.F2R (beta:=2) f + _root_.F2R (beta:=2) g)
  let Iminus :
      FloatSpec.Core.Defs.FlocqFloat 2 →
        FloatSpec.Core.Defs.FlocqFloat 2 →
          FloatSpec.Core.Defs.FlocqFloat 2 :=
    fun f g => RND_Closest (beta:=2) bo 2 prec choice
      (_root_.F2R (beta:=2) f - _root_.F2R (beta:=2) g)
  have hIplus_val :
      ∀ f g : FloatSpec.Core.Defs.FlocqFloat 2,
        _root_.F2R (beta:=2) (Iplus f g) =
          round_flt (_root_.F2R (beta:=2) f + _root_.F2R (beta:=2) g) := by
    intro f g
    have h := pff_round_N_is_round 2 bnd prec choice
      (_root_.F2R (beta:=2) f + _root_.F2R (beta:=2) g)
      hpBound hprec hbeta
    simpa [Iplus, round_flt, bo, hbnd_dExp] using h
  have hIminus_val :
      ∀ f g : FloatSpec.Core.Defs.FlocqFloat 2,
        _root_.F2R (beta:=2) (Iminus f g) =
          round_flt (_root_.F2R (beta:=2) f - _root_.F2R (beta:=2) g) := by
    intro f g
    have h := pff_round_N_is_round 2 bnd prec choice
      (_root_.F2R (beta:=2) f - _root_.F2R (beta:=2) g)
      hpBound hprec hbeta
    simpa [Iminus, round_flt, bo, hbnd_dExp] using h
  have hIplusCorrect :
      ∀ p q : FloatSpec.Core.Defs.FlocqFloat 2,
        Fbounded (beta:=2) bo p →
        Fbounded (beta:=2) bo q →
        Closest (beta:=2) bo (2 : ℝ)
          (_root_.F2R (beta:=2) p + _root_.F2R (beta:=2) q)
          (Iplus p q) := by
    intro p q _hp _hq
    have h := RND_Closest_correct (beta:=2) bo 2 prec choice
      (_root_.F2R (beta:=2) p + _root_.F2R (beta:=2) q)
    simpa only [wp, PostCond.noThrow, pure, RND_Closest_correct_check,
      Id.run, ULift.up_down, Iplus, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨rfl, hbeta, hprec, hvNum⟩
  have hIplusCan :
      ∀ p q : FloatSpec.Core.Defs.FlocqFloat 2,
        Fcanonic (beta:=2) 2 bo (Iplus p q) := by
    intro p q
    have h := RND_Closest_canonic (beta:=2) bo 2 prec choice
      (_root_.F2R (beta:=2) p + _root_.F2R (beta:=2) q)
    simpa only [wp, PostCond.noThrow, pure, RND_Closest_canonic_check,
      Id.run, ULift.up_down, Iplus, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨rfl, hbeta, hprec, hvNum⟩
  have hIminusCan :
      ∀ p q : FloatSpec.Core.Defs.FlocqFloat 2,
        Fcanonic (beta:=2) 2 bo (Iminus p q) := by
    intro p q
    have h := RND_Closest_canonic (beta:=2) bo 2 prec choice
      (_root_.F2R (beta:=2) p - _root_.F2R (beta:=2) q)
    simpa only [wp, PostCond.noThrow, pure, RND_Closest_canonic_check,
      Id.run, ULift.up_down, Iminus, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨rfl, hbeta, hprec, hvNum⟩
  have hIplusOp :
      ∀ p q : FloatSpec.Core.Defs.FlocqFloat 2,
        Fopp (beta:=2) (Iplus p q) =
          Iplus (Fopp (beta:=2) p) (Fopp (beta:=2) q) := by
    intro p q
    have hcan_left : Fcanonic (beta:=2) 2 bo (Fopp (beta:=2) (Iplus p q)) := by
      have h := FcanonicFopp (beta:=2) 2 bo (Iplus p q)
      simpa only [wp, PostCond.noThrow, pure, FcanonicFopp_check,
        Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h (hIplusCan p q)
    have hcan_right : Fcanonic (beta:=2) 2 bo
        (Iplus (Fopp (beta:=2) p) (Fopp (beta:=2) q)) :=
      hIplusCan (Fopp (beta:=2) p) (Fopp (beta:=2) q)
    have hpopp := Fopp_correct (beta:=2) p
    have hqopp := Fopp_correct (beta:=2) q
    have hsum_opp :
        _root_.F2R (beta:=2) (Fopp (beta:=2) p) +
            _root_.F2R (beta:=2) (Fopp (beta:=2) q) =
          -(_root_.F2R (beta:=2) p + _root_.F2R (beta:=2) q) := by
      have hpv : _root_.F2R (beta:=2) (Fopp (beta:=2) p) =
          -_root_.F2R (beta:=2) p := by
        simpa only [wp, PostCond.noThrow, pure, Fopp_correct_check,
          Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hpopp True.intro
      have hqv : _root_.F2R (beta:=2) (Fopp (beta:=2) q) =
          -_root_.F2R (beta:=2) q := by
        simpa only [wp, PostCond.noThrow, pure, Fopp_correct_check,
          Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hqopp True.intro
      rw [hpv, hqv]
      ring
    have hround_opp :
        round_flt (-(_root_.F2R (beta:=2) p + _root_.F2R (beta:=2) q)) =
          -round_flt (_root_.F2R (beta:=2) p + _root_.F2R (beta:=2) q) := by
      have h := round_N_opp_sym emin prec choice
        (_root_.F2R (beta:=2) p + _root_.F2R (beta:=2) q)
      simpa [round_flt] using h hchoice
    have hval :
        _root_.F2R (beta:=2) (Fopp (beta:=2) (Iplus p q)) =
          _root_.F2R (beta:=2)
            (Iplus (Fopp (beta:=2) p) (Fopp (beta:=2) q)) := by
      have hopen := Fopp_correct (beta:=2) (Iplus p q)
      have hleft : _root_.F2R (beta:=2) (Fopp (beta:=2) (Iplus p q)) =
          -_root_.F2R (beta:=2) (Iplus p q) := by
        simpa only [wp, PostCond.noThrow, pure, Fopp_correct_check,
          Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hopen True.intro
      rw [hleft, hIplus_val, hIplus_val, hsum_opp, hround_opp]
    have huniq := FcanonicUnique (beta:=2) 2 bo
      (Fopp (beta:=2) (Iplus p q))
      (Iplus (Fopp (beta:=2) p) (Fopp (beta:=2) q)) hbeta rfl
    simpa [Fcanonic'] using huniq ⟨hcan_left, hcan_right, hval⟩
  have hIminusPlus :
      ∀ p q : FloatSpec.Core.Defs.FlocqFloat 2,
        Iminus p q = Iplus p (Fopp (beta:=2) q) := by
    intro p q
    have hcan_left : Fcanonic (beta:=2) 2 bo (Iminus p q) :=
      hIminusCan p q
    have hcan_right : Fcanonic (beta:=2) 2 bo
        (Iplus p (Fopp (beta:=2) q)) :=
      hIplusCan p (Fopp (beta:=2) q)
    have hqopp := Fopp_correct (beta:=2) q
    have hqopp_val : _root_.F2R (beta:=2) (Fopp (beta:=2) q) =
        -_root_.F2R (beta:=2) q := by
      simpa only [wp, PostCond.noThrow, pure, Fopp_correct_check,
        Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hqopp True.intro
    have hval :
        _root_.F2R (beta:=2) (Iminus p q) =
          _root_.F2R (beta:=2) (Iplus p (Fopp (beta:=2) q)) := by
      rw [hIminus_val, hIplus_val, hqopp_val]
      ring_nf
    have huniq := FcanonicUnique (beta:=2) 2 bo (Iminus p q)
      (Iplus p (Fopp (beta:=2) q)) hbeta rfl
    simpa [Fcanonic'] using huniq ⟨hcan_left, hcan_right, hval⟩
  have hAbs' :
      |_root_.F2R (beta:=2) fy| ≤ |_root_.F2R (beta:=2) fx| := by
    simpa [hfx_val, hfy_val] using hAbs
  have K := Dekker_FTS_closed (beta:=2) bo (2 : ℝ) prec.toNat Iplus Iminus
    hIplusCorrect hIplusOp hIminusPlus hbeta rfl rfl hprecision_nat_ne
    hvNum hvNum_gt hBoundExpAll hTotal fx fy hfx_bound hfy_bound hAbs'
  let a : ℝ := round_flt (x + y)
  have hIplus_fx_fy : _root_.F2R (beta:=2) (Iplus fx fy) = a := by
    rw [hIplus_val, hfx_val, hfy_val]
  have hInner :
      _root_.F2R (beta:=2) (Iminus (Iplus fx fy) fx) =
        round_flt (a - x) := by
    rw [hIminus_val, hIplus_fx_fy, hfx_val]
  have hLeft :
      _root_.F2R (beta:=2) (Iminus fy (Iminus (Iplus fx fy) fx)) =
        round_flt (y - round_flt (a - x)) := by
    rw [hIminus_val, hfy_val, hInner]
  have K' : round_flt (y - round_flt (a - x)) = x + y - a := by
    rw [← hLeft]
    calc
      _root_.F2R (beta:=2) (Iminus fy (Iminus (Iplus fx fy) fx)) =
          _root_.F2R (beta:=2) fx + _root_.F2R (beta:=2) fy -
            _root_.F2R (beta:=2) (Iplus fx fy) := K
      _ = x + y - a := by
        rw [hfx_val, hfy_val, hIplus_fx_fy]
  have hround_x_sub_a :
      round_flt (x - a) = -round_flt (a - x) := by
    have h := round_N_opp_sym emin prec choice (a - x)
    have hsym : round_flt (-(a - x)) = -round_flt (a - x) := by
      simpa [round_flt] using h hchoice
    have hx : x - a = -(a - x) := by ring
    rw [hx]
    exact hsym
  change Fast2Sum_result emin prec choice x y
  unfold Fast2Sum_result Fast2Sum_round
  change a + round_flt (y + round_flt (x - a)) = x + y
  rw [hround_x_sub_a]
  have hy_sub : y + -round_flt (a - x) = y - round_flt (a - x) := by ring
  rw [hy_sub, K']
  ring

-- Coq: `TwoSum_correct`
noncomputable def TwoSum_round
    (emin prec : Int) (choice : Int → Bool) (z : ℝ) : ℝ :=
  FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
    (FloatSpec.Core.Generic_fmt.Znearest choice) z

noncomputable def TwoSum_result
    (emin prec : Int) (choice : Int → Bool) (x y : ℝ) : Prop :=
  let a := TwoSum_round emin prec choice (x + y)
  let x' := TwoSum_round emin prec choice (a - x)
  let dx := TwoSum_round emin prec choice
    (x - TwoSum_round emin prec choice (a - x'))
  let dy := TwoSum_round emin prec choice (y - x')
  let b := TwoSum_round emin prec choice (dx + dy)
  a + b = x + y

noncomputable def TwoSum_correct_check
    (emin prec : Int) (choice : Int → Bool) (x y : ℝ) : Unit :=
  ()

/-- Coq: `TwoSum_correct`.

For FLT radix-2 inputs `x` and `y`, the Knuth/TwoSum correction term restores
the exact sum. -/
theorem TwoSum_correct (emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (x y : ℝ) :
    ⦃⌜precisionNotZero prec ∧ emin ≤ 0 ∧
        (∀ t : Int, choice t = ! choice (-(t + 1))) ∧
        generic_format 2 (FLT_exp emin prec) x ∧
        generic_format 2 (FLT_exp emin prec) y⌝⦄
    (pure (TwoSum_correct_check emin prec choice x y) : Id Unit)
    ⦃⇓_ => ⌜TwoSum_result emin prec choice x y⌝⦄ := by
  intro h
  rcases h with ⟨hprec, hemin, hchoice, hx_fmt, hy_fmt⟩
  simp only [wp, PostCond.noThrow, pure, TwoSum_correct_check, Id.run,
    ULift.up_down]
  let round_flt : ℝ → ℝ := fun z =>
    FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
      (FloatSpec.Core.Generic_fmt.Znearest choice) z
  let bnd : Fbound := make_bound 2 prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  have hbeta : (1 : Int) < 2 := by decide
  have hbnd_dExp : -bnd.dExp = emin := by
    have h := make_bound_Emin 2 prec emin (hp := by exact hprec)
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using h hemin
    omega
  have hpBound : pGivesBound 2 bnd prec := by
    have h := make_bound_p 2 prec emin (hp := by exact hprec)
    have hv : (make_bound 2 prec emin).vNum =
        Zpower_nat 2 (prec.natAbs) := by
      simpa [wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound, bnd] using hv
  have hx_fmt_bnd : generic_format 2 (FLT_exp (-bnd.dExp) prec) x := by
    simpa [hbnd_dExp] using hx_fmt
  have hy_fmt_bnd : generic_format 2 (FLT_exp (-bnd.dExp) prec) y := by
    simpa [hbnd_dExp] using hy_fmt
  rcases (by
      have h := format_is_flocq_bounded 2 bnd prec x
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨hx_fmt_bnd, hpBound, hprec, hbeta⟩) with
    ⟨fx, hfx_val, hfx_bound⟩
  rcases (by
      have h := format_is_flocq_bounded 2 bnd prec y
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨hy_fmt_bnd, hpBound, hprec, hbeta⟩) with
    ⟨fy, hfy_val, hfy_bound⟩
  have hprec_pos : (0 : Int) < prec := lt_trans Int.zero_lt_one hprec
  have hprec_nonneg : (0 : Int) ≤ prec := le_of_lt hprec_pos
  have hprec_toNat_abs : prec.natAbs = prec.toNat := by
    apply Nat.cast_injective (R := Int)
    rw [Int.natAbs_of_nonneg hprec_nonneg, Int.toNat_of_nonneg hprec_nonneg]
  have hpBound_toNat : bnd.vNum = Zpower_nat 2 prec.toNat := by
    unfold pGivesBound at hpBound
    calc
      bnd.vNum = Zpower_nat 2 (prec.natAbs) := hpBound
      _ = Zpower_nat 2 prec.toNat := by rw [hprec_toNat_abs]
  have hvNum : bo.vNum = Zpower_nat 2 prec.toNat := by
    unfold bo toFboundSkel
    exact hpBound_toNat
  have hprecision_nat_gt : 1 < prec.toNat := by
    have hprec_toNat_int : (prec.toNat : Int) = prec := Int.toNat_of_nonneg hprec_nonneg
    have hprec_as_nat : (1 : Int) < (prec.toNat : Int) := by
      simpa [precisionNotZero, hprec_toNat_int] using hprec
    exact_mod_cast hprec_as_nat
  have hprecision_nat_ne : prec.toNat ≠ 0 :=
    Nat.ne_of_gt (lt_trans Nat.zero_lt_one hprecision_nat_gt)
  have hvNum_gt : (1 : Int) < bo.vNum := by
    rw [hvNum, Zpower_nat]
    exact one_lt_pow₀ (by decide : (1 : Int) < 2) hprecision_nat_ne
  have hBoundExpAll :
      ∀ r : ℝ, -bo.dExp ≤ (boundR (beta:=2) 2 r).Fexp := by
    intro r
    simpa [bo] using make_bound_boundR_exp_box 2 prec emin r
  have hMinTotal : TotalP (isMin (beta:=2) bo 2) := by
    intro r
    have h := MinEx_from_finite_box_payload (beta:=2) bo 2 r
    simpa only [wp, PostCond.noThrow, pure, MinEx_check, Id.run,
      ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨rfl, hbeta, hvNum_gt, hBoundExpAll r⟩
  have hMaxTotal : TotalP (isMax (beta:=2) bo 2) := by
    intro r
    have h := MaxEx_from_finite_box_payload (beta:=2) bo 2 r
    simpa only [wp, PostCond.noThrow, pure, MaxEx_check, Id.run,
      ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨rfl, hbeta, hvNum_gt, hBoundExpAll r⟩
  have hTotal : TotalP (Closest (beta:=2) bo (2 : ℝ)) := by
    intro r
    have h := ClosestTotal_from_extrema_payload (beta:=2) bo 2 (2 : ℝ) r
    simpa only [wp, PostCond.noThrow, pure, ClosestTotal_check, Id.run,
      ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨hMinTotal, hMaxTotal⟩
  let Iplus :
      FloatSpec.Core.Defs.FlocqFloat 2 →
        FloatSpec.Core.Defs.FlocqFloat 2 →
          FloatSpec.Core.Defs.FlocqFloat 2 :=
    fun f g => RND_Closest (beta:=2) bo 2 prec choice
      (_root_.F2R (beta:=2) f + _root_.F2R (beta:=2) g)
  let Iminus :
      FloatSpec.Core.Defs.FlocqFloat 2 →
        FloatSpec.Core.Defs.FlocqFloat 2 →
          FloatSpec.Core.Defs.FlocqFloat 2 :=
    fun f g => RND_Closest (beta:=2) bo 2 prec choice
      (_root_.F2R (beta:=2) f - _root_.F2R (beta:=2) g)
  have hIplus_val :
      ∀ f g : FloatSpec.Core.Defs.FlocqFloat 2,
        _root_.F2R (beta:=2) (Iplus f g) =
          round_flt (_root_.F2R (beta:=2) f + _root_.F2R (beta:=2) g) := by
    intro f g
    have h := pff_round_N_is_round 2 bnd prec choice
      (_root_.F2R (beta:=2) f + _root_.F2R (beta:=2) g)
      hpBound hprec hbeta
    simpa [Iplus, round_flt, bo, hbnd_dExp] using h
  have hIminus_val :
      ∀ f g : FloatSpec.Core.Defs.FlocqFloat 2,
        _root_.F2R (beta:=2) (Iminus f g) =
          round_flt (_root_.F2R (beta:=2) f - _root_.F2R (beta:=2) g) := by
    intro f g
    have h := pff_round_N_is_round 2 bnd prec choice
      (_root_.F2R (beta:=2) f - _root_.F2R (beta:=2) g)
      hpBound hprec hbeta
    simpa [Iminus, round_flt, bo, hbnd_dExp] using h
  have hIplusCorrect :
      ∀ p q : FloatSpec.Core.Defs.FlocqFloat 2,
        Fbounded (beta:=2) bo p →
        Fbounded (beta:=2) bo q →
        Closest (beta:=2) bo (2 : ℝ)
          (_root_.F2R (beta:=2) p + _root_.F2R (beta:=2) q)
          (Iplus p q) := by
    intro p q _hp _hq
    have h := RND_Closest_correct (beta:=2) bo 2 prec choice
      (_root_.F2R (beta:=2) p + _root_.F2R (beta:=2) q)
    simpa only [wp, PostCond.noThrow, pure, RND_Closest_correct_check,
      Id.run, ULift.up_down, Iplus, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨rfl, hbeta, hprec, hvNum⟩
  have hIplusCan :
      ∀ p q : FloatSpec.Core.Defs.FlocqFloat 2,
        Fcanonic (beta:=2) 2 bo (Iplus p q) := by
    intro p q
    have h := RND_Closest_canonic (beta:=2) bo 2 prec choice
      (_root_.F2R (beta:=2) p + _root_.F2R (beta:=2) q)
    simpa only [wp, PostCond.noThrow, pure, RND_Closest_canonic_check,
      Id.run, ULift.up_down, Iplus, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨rfl, hbeta, hprec, hvNum⟩
  have hIminusCan :
      ∀ p q : FloatSpec.Core.Defs.FlocqFloat 2,
        Fcanonic (beta:=2) 2 bo (Iminus p q) := by
    intro p q
    have h := RND_Closest_canonic (beta:=2) bo 2 prec choice
      (_root_.F2R (beta:=2) p - _root_.F2R (beta:=2) q)
    simpa only [wp, PostCond.noThrow, pure, RND_Closest_canonic_check,
      Id.run, ULift.up_down, Iminus, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨rfl, hbeta, hprec, hvNum⟩
  have hIplusCompatible :
      ∀ p q r s : FloatSpec.Core.Defs.FlocqFloat 2,
        Fbounded (beta:=2) bo p → Fbounded (beta:=2) bo q →
        Fbounded (beta:=2) bo r → Fbounded (beta:=2) bo s →
        _root_.F2R (beta:=2) p = _root_.F2R (beta:=2) r →
        _root_.F2R (beta:=2) q = _root_.F2R (beta:=2) s →
        _root_.F2R (beta:=2) (Iplus p q) =
          _root_.F2R (beta:=2) (Iplus r s) := by
    intro p q r s _ _ _ _ hp hq
    rw [hIplus_val, hIplus_val, hp, hq]
  have hIplusSym :
      ∀ p q : FloatSpec.Core.Defs.FlocqFloat 2,
        Iplus p q = Iplus q p := by
    intro p q
    have huniq := FcanonicUnique (beta:=2) 2 bo (Iplus p q) (Iplus q p)
      hbeta rfl
    have hval :
        _root_.F2R (beta:=2) (Iplus p q) =
          _root_.F2R (beta:=2) (Iplus q p) := by
      rw [hIplus_val, hIplus_val]
      congr 1
      ring
    simpa [Fcanonic'] using huniq ⟨hIplusCan p q, hIplusCan q p, hval⟩
  have hIplusOp :
      ∀ p q : FloatSpec.Core.Defs.FlocqFloat 2,
        Fopp (beta:=2) (Iplus p q) =
          Iplus (Fopp (beta:=2) p) (Fopp (beta:=2) q) := by
    intro p q
    have hcan_left : Fcanonic (beta:=2) 2 bo (Fopp (beta:=2) (Iplus p q)) := by
      have h := FcanonicFopp (beta:=2) 2 bo (Iplus p q)
      simpa only [wp, PostCond.noThrow, pure, FcanonicFopp_check,
        Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h (hIplusCan p q)
    have hcan_right : Fcanonic (beta:=2) 2 bo
        (Iplus (Fopp (beta:=2) p) (Fopp (beta:=2) q)) :=
      hIplusCan (Fopp (beta:=2) p) (Fopp (beta:=2) q)
    have hpopp := Fopp_correct (beta:=2) p
    have hqopp := Fopp_correct (beta:=2) q
    have hsum_opp :
        _root_.F2R (beta:=2) (Fopp (beta:=2) p) +
            _root_.F2R (beta:=2) (Fopp (beta:=2) q) =
          -(_root_.F2R (beta:=2) p + _root_.F2R (beta:=2) q) := by
      have hpv : _root_.F2R (beta:=2) (Fopp (beta:=2) p) =
          -_root_.F2R (beta:=2) p := by
        simpa only [wp, PostCond.noThrow, pure, Fopp_correct_check,
          Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hpopp True.intro
      have hqv : _root_.F2R (beta:=2) (Fopp (beta:=2) q) =
          -_root_.F2R (beta:=2) q := by
        simpa only [wp, PostCond.noThrow, pure, Fopp_correct_check,
          Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hqopp True.intro
      rw [hpv, hqv]
      ring
    have hround_opp :
        round_flt (-(_root_.F2R (beta:=2) p + _root_.F2R (beta:=2) q)) =
          -round_flt (_root_.F2R (beta:=2) p + _root_.F2R (beta:=2) q) := by
      have h := round_N_opp_sym emin prec choice
        (_root_.F2R (beta:=2) p + _root_.F2R (beta:=2) q)
      simpa [round_flt] using h hchoice
    have hval :
        _root_.F2R (beta:=2) (Fopp (beta:=2) (Iplus p q)) =
          _root_.F2R (beta:=2)
            (Iplus (Fopp (beta:=2) p) (Fopp (beta:=2) q)) := by
      have hopen := Fopp_correct (beta:=2) (Iplus p q)
      have hleft : _root_.F2R (beta:=2) (Fopp (beta:=2) (Iplus p q)) =
          -_root_.F2R (beta:=2) (Iplus p q) := by
        simpa only [wp, PostCond.noThrow, pure, Fopp_correct_check,
          Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hopen True.intro
      rw [hleft, hIplus_val, hIplus_val, hsum_opp, hround_opp]
    have huniq := FcanonicUnique (beta:=2) 2 bo
      (Fopp (beta:=2) (Iplus p q))
      (Iplus (Fopp (beta:=2) p) (Fopp (beta:=2) q)) hbeta rfl
    simpa [Fcanonic'] using huniq ⟨hcan_left, hcan_right, hval⟩
  have hIminusPlus :
      ∀ p q : FloatSpec.Core.Defs.FlocqFloat 2,
        Iminus p q = Iplus p (Fopp (beta:=2) q) := by
    intro p q
    have hcan_left : Fcanonic (beta:=2) 2 bo (Iminus p q) :=
      hIminusCan p q
    have hcan_right : Fcanonic (beta:=2) 2 bo
        (Iplus p (Fopp (beta:=2) q)) :=
      hIplusCan p (Fopp (beta:=2) q)
    have hqopp := Fopp_correct (beta:=2) q
    have hqopp_val : _root_.F2R (beta:=2) (Fopp (beta:=2) q) =
        -_root_.F2R (beta:=2) q := by
      simpa only [wp, PostCond.noThrow, pure, Fopp_correct_check,
        Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hqopp True.intro
    have hval :
        _root_.F2R (beta:=2) (Iminus p q) =
          _root_.F2R (beta:=2) (Iplus p (Fopp (beta:=2) q)) := by
      rw [hIminus_val, hIplus_val, hqopp_val]
      ring_nf
    have huniq := FcanonicUnique (beta:=2) 2 bo (Iminus p q)
      (Iplus p (Fopp (beta:=2) q)) hbeta rfl
    simpa [Fcanonic'] using huniq ⟨hcan_left, hcan_right, hval⟩
  have K := Knuth bo prec.toNat hprecision_nat_gt hvNum Iplus
    hIplusCorrect hIplusCompatible hIplusSym hIplusOp Iminus hIminusPlus
    fx fy hfx_bound hfy_bound
  let a : ℝ := round_flt (x + y)
  let x' : ℝ := round_flt (a - x)
  let dx : ℝ := round_flt (x - round_flt (a - x'))
  let dy : ℝ := round_flt (y - x')
  have hIplus_fx_fy : _root_.F2R (beta:=2) (Iplus fx fy) = a := by
    rw [hIplus_val, hfx_val, hfy_val]
  have hxprime :
      _root_.F2R (beta:=2) (Iminus (Iplus fx fy) fx) = x' := by
    rw [hIminus_val, hIplus_fx_fy, hfx_val]
  have hdx :
      _root_.F2R (beta:=2)
          (Iminus fx (Iminus (Iplus fx fy) (Iminus (Iplus fx fy) fx))) =
        dx := by
    rw [hIminus_val, hIminus_val, hIplus_fx_fy, hxprime, hfx_val]
  have hdy :
      _root_.F2R (beta:=2) (Iminus fy (Iminus (Iplus fx fy) fx)) = dy := by
    rw [hIminus_val, hfy_val, hxprime]
  have hb :
      _root_.F2R (beta:=2)
          (Iplus
            (Iminus fx
              (Iminus (Iplus fx fy) (Iminus (Iplus fx fy) fx)))
            (Iminus fy (Iminus (Iplus fx fy) fx))) =
        round_flt (dx + dy) := by
    rw [hIplus_val, hdx, hdy]
  change TwoSum_result emin prec choice x y
  unfold TwoSum_result TwoSum_round
  change a + round_flt (dx + dy) = x + y
  rw [← hb]
  calc
    a + _root_.F2R (beta:=2)
          (Iplus
            (Iminus fx
              (Iminus (Iplus fx fy) (Iminus (Iplus fx fy) fx)))
            (Iminus fy (Iminus (Iplus fx fy) fx)))
        = a + (_root_.F2R (beta:=2) fx + _root_.F2R (beta:=2) fy -
            _root_.F2R (beta:=2) (Iplus fx fy)) := by rw [K]
    _ = x + y := by
      rw [hfx_val, hfy_val, hIplus_fx_fy]
      ring

-- Coq: `C_format` — (β^s + 1) is in generic format for FLT(emin, prec)
noncomputable def C_format_check (beta emin prec s : Int) : Unit :=
  ()

/-- Coq: `C_format` — under the usual small-precision side conditions,
    the real `(β^s + 1)` is representable in `generic_format β (FLT_exp emin prec)`.
    We capture the side conditions in the Hoare precondition. -/
theorem C_format (beta emin prec s : Int) [ValidRadix beta] [Prec_gt_0 prec] :
    ⦃⌜(2 ≤ s) ∧ (s ≤ prec - 2) ∧ (emin ≤ 0)⌝⦄
    (pure (C_format_check beta emin prec s) : Id Unit)
    ⦃⇓_ => ⌜generic_format beta (FLT_exp emin prec)
      (FloatSpec.Core.Raux.bpow beta s + 1)⌝⦄ := by
  apply Std.Do.Triple.pure
  intro hpre
  rcases hpre with ⟨hs_ge, hs_le, hemin_le⟩
  let n : Nat := Int.toNat s
  let m : Int := beta ^ n + 1
  have hβ : 1 < beta := ValidRadix.valid
  have hβreal : (1 : ℝ) < beta := by exact_mod_cast hβ
  have hs_nonneg : 0 ≤ s := by omega
  have hn_cast : (n : Int) = s := by
    exact Int.toNat_of_nonneg hs_nonneg
  have hF2R :
      FloatSpec.Core.Defs.F2R (FloatSpec.Core.Defs.FlocqFloat.mk (beta := beta) m 0)
        = (beta : ℝ) ^ n + 1 := by
    simp [FloatSpec.Core.Defs.F2R, m]
  have hpow_cast : (beta : ℝ) ^ n = (beta : ℝ) ^ s := by
    rw [← hn_cast, zpow_natCast]
  have hfmt :=
    FloatSpec.Core.Generic_fmt.generic_format_F2R
      (beta := beta) (fexp := FLT_exp emin prec) (m := m) (e := 0)
      ⟨hβ, ?_⟩
  · simpa [FloatSpec.Core.Defs.F2R, hF2R, n, m,
      FloatSpec.Core.Raux.bpow, hpow_cast] using hfmt
  intro hm_ne
  simp [FloatSpec.Core.Generic_fmt.cexp, FLT_exp, FloatSpec.Core.FLT.FLT_exp,
    FloatSpec.Core.Defs.F2R, m]
  constructor
  · have hmag_le :
        FloatSpec.Core.Raux.mag beta ((beta : ℝ) ^ n + 1) ≤ s + 1 := by
      have hx_ne : (beta : ℝ) ^ n + 1 ≠ 0 := by positivity
      have hx_lt : |(beta : ℝ) ^ n + 1| < (beta : ℝ) ^ (s + 1) := by
        have hn_ge_two : 2 ≤ n := by omega
        have hβone : (1 : ℝ) ≤ beta := le_of_lt hβreal
        have hpow_ge : (beta : ℝ) ^ 1 ≤ (beta : ℝ) ^ n := by
          exact pow_le_pow_right₀ hβone (by omega)
        have hpow_pos : (0 : ℝ) < (beta : ℝ) ^ n := pow_pos (by positivity) n
        have hpow_one_lt : (1 : ℝ) < (beta : ℝ) ^ n := by
          have : (beta : ℝ) ≤ (beta : ℝ) ^ n := by
            simpa using hpow_ge
          exact lt_of_lt_of_le hβreal this
        have hβtwo : (2 : ℝ) ≤ beta := by exact_mod_cast hβ
        have hs_succ_nonneg : 0 ≤ s + 1 := by omega
        have hsucc_nat : Int.toNat (s + 1) = n + 1 := by omega
        rw [← Int.toNat_of_nonneg hs_succ_nonneg, zpow_natCast, hsucc_nat]
        rw [pow_succ]
        simp [abs_of_pos (by positivity : (0 : ℝ) < (beta : ℝ) ^ n + 1)]
        nlinarith [hpow_one_lt, hpow_pos, hβtwo]
      have htrip := FloatSpec.Core.Raux.mag_le_abs_from_bpow_payload (beta := beta)
        (x := (beta : ℝ) ^ n + 1)
        (e := s + 1) hβ hx_ne hx_lt
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using (htrip (by trivial))
    omega
  · exact hemin_le

/-!
Coq lemma: `underf_mult_aux`

In the `Underf_mult_aux` section, Flocq proves that if two bounded Pff floats
have a product whose magnitude is at least `bpow (e + 2 * prec - 1)`, then the
sum of their exponents is at least `e`.
-/

noncomputable def underf_mult_aux_check {beta : Int} [ValidRadix beta]
    (_b : Fbound_skel) (_prec e : Int)
    (_x _y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

private lemma underf_mult_aux_abs_lt {beta : Int} [ValidRadix beta]
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
theorem underf_mult_aux {beta : Int} [ValidRadix beta]
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

noncomputable def underf_mult_aux'_check {beta : Int} [ValidRadix beta]
    (_b : Fbound_skel) (_prec : Int)
    (_x _y : FloatSpec.Core.Defs.FlocqFloat beta) : Unit :=
  ()

/-- Coq: `underf_mult_aux'`.
This is the `underf_mult_aux` specialization at `e = -dExp b`. -/
theorem underf_mult_aux' {beta : Int} [ValidRadix beta]
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
theorem V1_Und3' (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
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
theorem V1_Und3 (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
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

/-- Pff-side nearest-rounding witnesses used by Coq `Veltkamp` and
`Veltkamp_tail`.

The public Veltkamp wrappers first convert the formatted input `x` to a
bounded Pff float, then destruct `round_N_is_pff_round` for the three rounded
intermediates `p`, `q`, and `hx`.  This helper packages that wrapper-side
setup independently of the still-missing lower Pff `Veltkamp` payload. -/
theorem Veltkamp_round_N_witnesses (beta emin prec s : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (x : ℝ)
    (hβ : 1 < beta)
    (hprec : precisionNotZero prec)
    (hemin : emin ≤ 0)
    (Fx : generic_format beta (FLT_exp emin prec) x) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let bnd : Fbound := make_bound beta prec emin
    let bo : Fbound_skel := toFboundSkel bnd
    let valueWitness := fun (value : ℝ) (f : FloatSpec.Core.Defs.FlocqFloat beta) =>
      _root_.F2R (beta:=beta) f = value ∧ Fbounded (beta:=beta) bo f
    let roundWitness := fun (input rounded : ℝ)
        (f : FloatSpec.Core.Defs.FlocqFloat beta) =>
      Fcanonic (beta:=beta) beta bo f ∧
        Closest (beta:=beta) bo (beta : ℝ) input f ∧
        _root_.F2R (beta:=beta) f = rounded
    let p := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
      (x * (FloatSpec.Core.Raux.bpow beta s + 1))
    let q := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x - p)
    let hx := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (q + p)
    ∃ fx fp fq fhx : FloatSpec.Core.Defs.FlocqFloat beta,
      valueWitness x fx ∧
        roundWitness (x * (FloatSpec.Core.Raux.bpow beta s + 1)) p fp ∧
        roundWitness (x - p) q fq ∧
        roundWitness (q + p) hx fhx := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let bnd : Fbound := make_bound beta prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  let p := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
    (x * (FloatSpec.Core.Raux.bpow beta s + 1))
  let q := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x - p)
  let hx := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (q + p)
  have hpBound : pGivesBound beta bnd prec := by
    have h := make_bound_p beta prec emin (hp := by exact hprec)
    have hv : (make_bound beta prec emin).vNum =
        Zpower_nat beta (prec.natAbs) := by
      simpa [wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound, bnd] using hv
  have hbnd_dExp : -bnd.dExp = emin := by
    have h := make_bound_Emin beta prec emin (hp := by exact hprec)
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using
        h hemin
    omega
  have Fx_bnd : generic_format beta (FLT_exp (-bnd.dExp) prec) x := by
    simpa [hbnd_dExp] using Fx
  rcases (by
      have h := format_is_flocq_bounded beta bnd prec x
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨Fx_bnd, hpBound, hprec, hβ⟩) with
    ⟨fx, hfx_val, hfx_bound⟩
  rcases (round_N_is_pff_round (beta := beta) (b := bnd) (p := prec)
      (choice := choice) (r := x * (FloatSpec.Core.Raux.bpow beta s + 1))
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨fp, hfp_can, hfp_closest, hfp_val⟩
  rcases (round_N_is_pff_round (beta := beta) (b := bnd) (p := prec)
      (choice := choice) (r := x - p)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨fq, hfq_can, hfq_closest, hfq_val⟩
  rcases (round_N_is_pff_round (beta := beta) (b := bnd) (p := prec)
      (choice := choice) (r := q + p)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨fhx, hfhx_can, hfhx_closest, hfhx_val⟩
  refine ⟨fx, fp, fq, fhx, ?_, ?_, ?_, ?_⟩
  · exact ⟨hfx_val, hfx_bound⟩
  · exact ⟨hfp_can, hfp_closest, by simpa [p, rnd, hbnd_dExp, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hfp_val⟩
  · exact ⟨hfq_can, hfq_closest, by simpa [q, rnd, hbnd_dExp] using hfq_val⟩
  · exact ⟨hfhx_can, hfhx_closest, by simpa [hx, rnd, hbnd_dExp] using hfhx_val⟩

/-- Pff-side nearest-rounding witnesses used by Coq `Veltkamp_tail`.

This extends `Veltkamp_round_N_witnesses` with the fourth rounded
intermediate `tx := round (x - hx)`, the extra witness destructed by the
upstream tail theorem before invoking the lower Pff `Veltkamp_tail` payload. -/
theorem Veltkamp_tail_round_N_witnesses (beta emin prec s : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (x : ℝ)
    (hβ : 1 < beta)
    (hprec : precisionNotZero prec)
    (hemin : emin ≤ 0)
    (Fx : generic_format beta (FLT_exp emin prec) x) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let bnd : Fbound := make_bound beta prec emin
    let bo : Fbound_skel := toFboundSkel bnd
    let valueWitness := fun (value : ℝ) (f : FloatSpec.Core.Defs.FlocqFloat beta) =>
      _root_.F2R (beta:=beta) f = value ∧ Fbounded (beta:=beta) bo f
    let roundWitness := fun (input rounded : ℝ)
        (f : FloatSpec.Core.Defs.FlocqFloat beta) =>
      Fcanonic (beta:=beta) beta bo f ∧
        Closest (beta:=beta) bo (beta : ℝ) input f ∧
        _root_.F2R (beta:=beta) f = rounded
    let p := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
      (x * (FloatSpec.Core.Raux.bpow beta s + 1))
    let q := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x - p)
    let hx := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (q + p)
    let tx := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x - hx)
    ∃ fx fp fq fhx ftx : FloatSpec.Core.Defs.FlocqFloat beta,
      valueWitness x fx ∧
        roundWitness (x * (FloatSpec.Core.Raux.bpow beta s + 1)) p fp ∧
        roundWitness (x - p) q fq ∧
        roundWitness (q + p) hx fhx ∧
        roundWitness (x - hx) tx ftx := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let bnd : Fbound := make_bound beta prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  let p := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
    (x * (FloatSpec.Core.Raux.bpow beta s + 1))
  let q := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x - p)
  let hx := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (q + p)
  let tx := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x - hx)
  have hpBound : pGivesBound beta bnd prec := by
    have h := make_bound_p beta prec emin (hp := by exact hprec)
    have hv : (make_bound beta prec emin).vNum =
        Zpower_nat beta (prec.natAbs) := by
      simpa [wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound, bnd] using hv
  have hbnd_dExp : -bnd.dExp = emin := by
    have h := make_bound_Emin beta prec emin (hp := by exact hprec)
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using
        h hemin
    omega
  have Fx_bnd : generic_format beta (FLT_exp (-bnd.dExp) prec) x := by
    simpa [hbnd_dExp] using Fx
  rcases (by
      have h := format_is_flocq_bounded beta bnd prec x
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨Fx_bnd, hpBound, hprec, hβ⟩) with
    ⟨fx, hfx_val, hfx_bound⟩
  rcases (round_N_is_pff_round (beta := beta) (b := bnd) (p := prec)
      (choice := choice) (r := x * (FloatSpec.Core.Raux.bpow beta s + 1))
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨fp, hfp_can, hfp_closest, hfp_val⟩
  rcases (round_N_is_pff_round (beta := beta) (b := bnd) (p := prec)
      (choice := choice) (r := x - p)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨fq, hfq_can, hfq_closest, hfq_val⟩
  rcases (round_N_is_pff_round (beta := beta) (b := bnd) (p := prec)
      (choice := choice) (r := q + p)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨fhx, hfhx_can, hfhx_closest, hfhx_val⟩
  rcases (round_N_is_pff_round (beta := beta) (b := bnd) (p := prec)
      (choice := choice) (r := x - hx)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨ftx, hftx_can, hftx_closest, hftx_val⟩
  refine ⟨fx, fp, fq, fhx, ftx, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hfx_val, hfx_bound⟩
  · exact ⟨hfp_can, hfp_closest, by simpa [p, rnd, hbnd_dExp, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hfp_val⟩
  · exact ⟨hfq_can, hfq_closest, by simpa [q, rnd, hbnd_dExp] using hfq_val⟩
  · exact ⟨hfhx_can, hfhx_closest, by simpa [hx, rnd, hbnd_dExp] using hfhx_val⟩
  · exact ⟨hftx_can, hftx_closest, by simpa [tx, rnd, hbnd_dExp] using hftx_val⟩

/-- Final Pff-to-Flocq conversion step used by Coq `Veltkamp_Even`.

Once the lower Pff `VeltkampEven` payload supplies an `EvenClosest` witness for
the reduced precision bound, the public Flocq equality follows from the
nearest-even bridge. -/
theorem Veltkamp_Even_from_reduced_evenClosest (beta emin prec s : Int) [ValidRadix beta]
    [Prec_gt_0 prec] (x hx : ℝ)
    (hβ : 1 < beta)
    (hemin : emin ≤ 0)
    (hs_le : 2 ≤ s)
    (hs_ge : s ≤ prec - 2)
    (hReduced :
      ∃ fhx : FloatSpec.Core.Defs.FlocqFloat beta,
        _root_.F2R (beta:=beta) fhx = hx ∧
        EvenClosest (beta:=beta)
          (toFboundSkel (make_bound beta (prec - s) emin)) (beta : ℝ)
          (prec - s).toNat x fhx) :
    hx =
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin (prec - s))
        (FloatSpec.Core.Generic_fmt.Znearest
          (fun t : Int => !(decide (2 ∣ t)))) x := by
  classical
  let reducedPrec : Int := prec - s
  let reducedBound : Fbound := make_bound beta reducedPrec emin
  have hReducedPrec : precisionNotZero reducedPrec := by
    dsimp [precisionNotZero, reducedPrec]
    omega
  have hReducedPos : 0 < reducedPrec := lt_trans Int.zero_lt_one hReducedPrec
  haveI : Prec_gt_0 reducedPrec := ⟨hReducedPos⟩
  have hReducedBound : pGivesBound beta reducedBound reducedPrec := by
    have h := make_bound_p beta reducedPrec emin
    have hv : (make_bound beta reducedPrec emin).vNum =
        Zpower_nat beta (reducedPrec.natAbs) := by
      simpa [wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound, reducedBound] using hv
  have hReducedExp : -reducedBound.dExp = emin := by
    have h := make_bound_Emin beta reducedPrec emin
    have hd : reducedBound.dExp = -emin := by
      simpa [reducedBound, wp, PostCond.noThrow, make_bound_Emin_check, pure]
        using h hemin
    omega
  rcases hReduced with ⟨fhx, hfhx_val, hfhx_even⟩
  have hbridge := evenClosest_value_eq_round_NE beta reducedBound reducedPrec x fhx
    hReducedBound hReducedPrec hβ
    (by simpa [reducedBound, reducedPrec] using hfhx_even)
  calc
    hx = _root_.F2R (beta:=beta) fhx := hfhx_val.symm
    _ =
        FloatSpec.Core.Generic_fmt.roundR beta
          (FLT_exp (-reducedBound.dExp) reducedPrec)
          (FloatSpec.Core.Generic_fmt.Znearest
            (fun t : Int => !(decide (2 ∣ t)))) x := hbridge
    _ =
        FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin (prec - s))
          (FloatSpec.Core.Generic_fmt.Znearest
            (fun t : Int => !(decide (2 ∣ t)))) x := by
          simp [hReducedExp, reducedPrec]

/-- Final Pff-to-Flocq conversion step used by Coq `Veltkamp`.

The lower Pff payload used by both public Veltkamp theorems can provide the
same reduced-bound nearest-even witness.  The non-even public theorem only asks
for existence of a nearest choice, so this bridge packages the even choice as
that witness. -/
theorem Veltkamp_from_reduced_evenClosest (beta emin prec s : Int) [ValidRadix beta]
    [Prec_gt_0 prec] (x hx : ℝ)
    (hβ : 1 < beta)
    (hemin : emin ≤ 0)
    (hs_le : 2 ≤ s)
    (hs_ge : s ≤ prec - 2)
    (hReduced :
      ∃ fhx : FloatSpec.Core.Defs.FlocqFloat beta,
        _root_.F2R (beta:=beta) fhx = hx ∧
        EvenClosest (beta:=beta)
          (toFboundSkel (make_bound beta (prec - s) emin)) (beta : ℝ)
          (prec - s).toNat x fhx) :
    ∃ choice' : Int → Bool,
      hx =
        FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin (prec - s))
          (FloatSpec.Core.Generic_fmt.Znearest choice') x := by
  refine ⟨fun t : Int => !(decide (2 ∣ t)), ?_⟩
  exact Veltkamp_Even_from_reduced_evenClosest beta emin prec s x hx hβ
    hemin hs_le hs_ge hReduced

/-- Final Pff-to-Flocq conversion step used by Coq `Veltkamp_tail`.

Once the lower Pff `Veltkamp_tail` payload supplies the tail float bounded by
the precision-`s` bound, this bridge converts it to the public Flocq equality
and `generic_format` statement. -/
theorem Veltkamp_tail_from_pff_tail_payload (beta emin prec s : Int) [ValidRadix beta]
    [Prec_gt_0 prec] (x hx tx : ℝ)
    (hβ : 1 < beta)
    (hemin : emin ≤ 0)
    (hs_le : 2 ≤ s)
    (hTail :
      ∃ ftx : FloatSpec.Core.Defs.FlocqFloat beta,
        _root_.F2R (beta:=beta) ftx = tx ∧
        x = hx + _root_.F2R (beta:=beta) ftx ∧
        Fbounded (beta:=beta) (toFboundSkel (make_bound beta s emin)) ftx) :
    x = hx + tx ∧ generic_format beta (FLT_exp emin s) tx := by
  classical
  have hs_pos : 0 < s := by omega
  haveI : Prec_gt_0 s := ⟨hs_pos⟩
  let tailBound : Fbound := make_bound beta s emin
  have hTailPrec : precisionNotZero s := by
    dsimp [precisionNotZero]
    omega
  have hTailBound : pGivesBound beta tailBound s := by
    have h := make_bound_p beta s emin
    have hv : (make_bound beta s emin).vNum =
        Zpower_nat beta (s.natAbs) := by
      simpa [wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound, tailBound] using hv
  have hTailExp : -tailBound.dExp = emin := by
    have h := make_bound_Emin beta s emin
    have hd : tailBound.dExp = -emin := by
      simpa [tailBound, wp, PostCond.noThrow, make_bound_Emin_check, pure]
        using h hemin
    omega
  rcases hTail with ⟨ftx, hftx_val, hsum, hftx_bound⟩
  have hfmt :
      generic_format beta (FLT_exp (-tailBound.dExp) s)
        (_root_.F2R (beta:=beta) ftx) := by
    have h := flocq_bounded_is_format beta tailBound s ftx
    simpa only [wp, PostCond.noThrow, pff_format_is_format_check, pure,
      PredTrans.pure, PredTrans.apply, SPred.down_pure_nil]
      using h ⟨hTailBound, hTailPrec, by simpa [tailBound, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hftx_bound, hβ⟩
  constructor
  · simpa [hftx_val] using hsum
  · simpa [hTailExp, hftx_val] using hfmt

/-- Coq theorem: `Veltkamp_Even`.

The upstream public wrapper constructs the Pff witnesses for the Veltkamp
intermediates and calls lower Pff `VeltkampEven`.  This wrapper records the
final checked conversion: once that lower payload supplies the reduced
`EvenClosest` witness, the public nearest-even equality follows. -/
theorem Veltkamp_Even_from_reduced_payload (beta emin prec s : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (x hx : ℝ)
    (hβ : 1 < beta)
    (hemin : emin ≤ 0)
    (hs_le : 2 ≤ s)
    (hs_ge : s ≤ prec - 2)
    (hchoice : choice = fun t : Int => !(decide (2 ∣ t)))
    (hReduced :
      ∃ fhx : FloatSpec.Core.Defs.FlocqFloat beta,
        _root_.F2R (beta:=beta) fhx = hx ∧
        EvenClosest (beta:=beta)
          (toFboundSkel (make_bound beta (prec - s) emin)) (beta : ℝ)
          (prec - s).toNat x fhx) :
    hx =
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin (prec - s))
        (FloatSpec.Core.Generic_fmt.Znearest choice) x := by
  rw [hchoice]
  exact Veltkamp_Even_from_reduced_evenClosest beta emin prec s x hx hβ
    hemin hs_le hs_ge hReduced

/-- Coq theorem: `Veltkamp`.

The lower Pff payload gives the same reduced nearest-even witness used by
`Veltkamp_Even`; the non-even public theorem only requires existence of a
nearest choice. -/
theorem Veltkamp_from_reduced_payload (beta emin prec s : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (x hx : ℝ)
    (hβ : 1 < beta)
    (hemin : emin ≤ 0)
    (hs_le : 2 ≤ s)
    (hs_ge : s ≤ prec - 2)
    (hReduced :
      ∃ fhx : FloatSpec.Core.Defs.FlocqFloat beta,
        _root_.F2R (beta:=beta) fhx = hx ∧
        EvenClosest (beta:=beta)
          (toFboundSkel (make_bound beta (prec - s) emin)) (beta : ℝ)
          (prec - s).toNat x fhx) :
    ∃ choice' : Int → Bool,
      hx =
        FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin (prec - s))
          (FloatSpec.Core.Generic_fmt.Znearest choice') x := by
  exact Veltkamp_from_reduced_evenClosest beta emin prec s x hx hβ
    hemin hs_le hs_ge hReduced

/-- Coq theorem: `Veltkamp_tail`.

Once the lower Pff `Veltkamp_tail` payload supplies the tail float and its
bound, this public wrapper exposes the Flocq equality and format conclusion. -/
theorem Veltkamp_tail_from_tail_payload (beta emin prec s : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (x hx tx : ℝ)
    (hβ : 1 < beta)
    (hemin : emin ≤ 0)
    (hs_le : 2 ≤ s)
    (hTail :
      ∃ ftx : FloatSpec.Core.Defs.FlocqFloat beta,
        _root_.F2R (beta:=beta) ftx = tx ∧
        x = hx + _root_.F2R (beta:=beta) ftx ∧
        Fbounded (beta:=beta) (toFboundSkel (make_bound beta s emin)) ftx) :
    x = hx + tx ∧ generic_format beta (FLT_exp emin s) tx := by
  exact Veltkamp_tail_from_pff_tail_payload beta emin prec s x hx tx hβ
    hemin hs_le hTail

/-- Coq `Pff2Flocq.Veltkamp_Even`, with all algorithm intermediates local. -/
theorem Veltkamp_Even (beta emin prec s : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (x : ℝ)
    (hprecision : 3 ≤ prec)
    (hemin : emin ≤ 0)
    (hs_le : 2 ≤ s)
    (hs_ge : s ≤ prec - 2)
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (hchoice : choice = fun t : Int => !(decide (2 ∣ t))) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let p := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
      (x * (FloatSpec.Core.Raux.bpow beta s + 1))
    let q := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x - p)
    let hx := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (q + p)
    hx = FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin (prec - s)) rnd x := by
  classical
  subst choice
  let evenChoice : Int → Bool := fun t => !(decide (2 ∣ t))
  let rnd := FloatSpec.Core.Generic_fmt.Znearest evenChoice
  let p := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
    (x * (FloatSpec.Core.Raux.bpow beta s + 1))
  let q := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x - p)
  let hx := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (q + p)
  have hβ : 1 < beta := ValidRadix.valid
  let bnd : Fbound := make_bound beta prec emin (hβ := hβ)
  let bo : Fbound_skel := toFboundSkel bnd
  have hprec : precisionNotZero prec := by
    unfold precisionNotZero
    omega
  have hprecPos : 0 ≤ prec := by omega
  have hsPos : 0 ≤ s := by omega
  have hsubPos : 0 ≤ prec - s := by omega
  have hprecNat : (prec.toNat : Int) = prec := Int.toNat_of_nonneg hprecPos
  have hsNat : (s.toNat : Int) = s := Int.toNat_of_nonneg hsPos
  have hsubNat : ((prec - s).toNat : Int) = prec - s :=
    Int.toNat_of_nonneg hsubPos
  have hnatSub : prec.toNat - s.toNat = (prec - s).toNat := by omega
  have habsPrec : prec.natAbs = prec.toNat := by omega
  have hpBound : pGivesBound beta bnd prec := by
    have h := make_bound_p beta prec emin
    have hv : bnd.vNum = Zpower_nat beta prec.natAbs := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound, habsPrec] using hv
  have hbndExp : -bnd.dExp = emin := by
    have h := make_bound_Emin beta prec emin
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using h hemin
    omega
  have hboExp : -bo.dExp = emin := by simpa [bo] using hbndExp
  have hfxFmt : generic_format beta (FLT_exp (-bnd.dExp) prec) x := by
    simpa [hbndExp] using Fx
  rcases (by
      have h := format_is_flocq_bounded beta bnd prec x
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨hfxFmt, hpBound, hprec, hβ⟩) with
    ⟨fx, hfxVal, hfxBound⟩
  rcases round_NE_is_pff_round beta bnd prec
      (x * (FloatSpec.Core.Raux.bpow beta s + 1)) hpBound hprec hβ with
    ⟨fp, _hfpCan, hfpEven, hfpVal⟩
  rcases round_NE_is_pff_round beta bnd prec (x - p) hpBound hprec hβ with
    ⟨fq, _hfqCan, hfqEven, hfqVal⟩
  rcases round_NE_is_pff_round beta bnd prec (q + p) hpBound hprec hβ with
    ⟨fhx, _hfhxCan, hfhxEven, hfhxVal⟩
  have hfpAlg : _root_.F2R (beta:=beta) fp = p := by
    simpa [p, rnd, evenChoice, hbndExp, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hfpVal
  have hfqAlg : _root_.F2R (beta:=beta) fq = q := by
    simpa [q, rnd, evenChoice, hbndExp] using hfqVal
  have hpEven : EvenClosest (beta:=beta) bo (beta : ℝ) prec.toNat
      (_root_.F2R (beta:=beta) fx * ((beta : ℝ) ^ (s.toNat : Int) + 1)) fp := by
    simpa [bo, hfxVal, hsNat, FloatSpec.Core.Raux.bpow] using hfpEven
  have hqEven : EvenClosest (beta:=beta) bo (beta : ℝ) prec.toNat
      (_root_.F2R (beta:=beta) fx - _root_.F2R (beta:=beta) fp) fq := by
    simpa [bo, hfxVal, hfpAlg] using hfqEven
  have hhxEven : EvenClosest (beta:=beta) bo (beta : ℝ) prec.toNat
      (_root_.F2R (beta:=beta) fq + _root_.F2R (beta:=beta) fp) fhx := by
    simpa [bo, hfqAlg, hfpAlg] using hfhxEven
  rcases VeltkampEven (beta:=beta) bo beta s.toNat prec.toNat fx fp fq fhx
      rfl hβ (by simpa [bo, pGivesBound, habsPrec] using hpBound) (by omega) (by omega)
      (by simpa [bo] using hfxBound) hpEven hqEven hhxEven with
    ⟨fhx', hfhx'Val, hfhx'Reduced⟩
  have hredBound :
      Veltkamp_reducedBound beta bo s.toNat prec.toNat (hβ := hβ) =
        toFboundSkel (make_bound beta (prec - s) emin (hβ := hβ)) := by
    have habs : (prec - s).natAbs = (prec - s).toNat := by omega
    have hredNotNeg : ¬ prec - s < 0 := by omega
    simp [Veltkamp_reducedBound, bo, bnd, toFboundSkel, make_bound,
      Bound, hemin, hnatSub, habs, hredNotNeg]
  have hReduced :
      ∃ g : FloatSpec.Core.Defs.FlocqFloat beta,
        _root_.F2R (beta:=beta) g = hx ∧
        EvenClosest (beta:=beta)
          (toFboundSkel (make_bound beta (prec - s) emin (hβ := hβ))) (beta : ℝ)
          (prec - s).toNat x g := by
    refine ⟨fhx', ?_, ?_⟩
    · calc
        _root_.F2R (beta:=beta) fhx' = _root_.F2R (beta:=beta) fhx := hfhx'Val
        _ = hx := by simpa [hx, q, p, rnd, evenChoice, hbndExp] using hfhxVal
    · simpa [hredBound, hfxVal, hnatSub] using hfhx'Reduced
  simpa [rnd, evenChoice, p, q, hx] using
    Veltkamp_Even_from_reduced_evenClosest beta emin prec s x hx hβ hemin
      hs_le hs_ge hReduced

/-- Coq `Pff2Flocq.Veltkamp`, including construction of the arbitrary-nearest
reduced-precision witness from the local algorithm. -/
theorem Veltkamp (beta emin prec s : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (x : ℝ)
    (hprecision : 3 ≤ prec)
    (hemin : emin ≤ 0)
    (hs_le : 2 ≤ s)
    (hs_ge : s ≤ prec - 2)
    (Fx : generic_format beta (FLT_exp emin prec) x) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let p := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
      (x * (FloatSpec.Core.Raux.bpow beta s + 1))
    let q := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x - p)
    let hx := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (q + p)
    ∃ choice' : Int → Bool,
      hx = FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin (prec - s))
        (FloatSpec.Core.Generic_fmt.Znearest choice') x := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let p := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
    (x * (FloatSpec.Core.Raux.bpow beta s + 1))
  let q := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x - p)
  let hx := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (q + p)
  have hβ : 1 < beta := ValidRadix.valid
  have hprec : precisionNotZero prec := by
    unfold precisionNotZero
    omega
  have hprecPos : 0 ≤ prec := by omega
  have hsPos : 0 ≤ s := by omega
  have hredPos : 0 ≤ prec - s := by omega
  have hsNat : (s.toNat : Int) = s := Int.toNat_of_nonneg hsPos
  have hnatSub : prec.toNat - s.toNat = (prec - s).toNat := by omega
  have habsPrec : prec.natAbs = prec.toNat := by omega
  have habsRed : (prec - s).natAbs = (prec - s).toNat := by omega
  let bnd : Fbound := make_bound beta prec emin (hβ := hβ)
  let bo : Fbound_skel := toFboundSkel bnd
  have hpBound : pGivesBound beta bnd prec := by
    have h := make_bound_p beta prec emin
    have hv : bnd.vNum = Zpower_nat beta prec.natAbs := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound, habsPrec] using hv
  have hvNum : bo.vNum = Zpower_nat beta prec.toNat := by
    simpa [bo, pGivesBound, habsPrec] using hpBound
  rcases Veltkamp_round_N_witnesses beta emin prec s choice x hβ hprec hemin Fx with
    ⟨fx, fp, fq, fhx, hfx, hpw, hqw, hhxw⟩
  let nx : FloatSpec.Core.Defs.FlocqFloat beta :=
    Fnormalize (beta:=beta) beta bo prec.toNat fx
  have hnxCan : Fcanonic (beta:=beta) beta bo nx := by
    have h := FnormalizeCanonic (beta:=beta) beta bo prec.toNat fx
    simpa only [wp, PostCond.noThrow, pure, FnormalizeCanonic_check,
      Id.run, ULift.up_down, nx, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using
      h ⟨hfx.2, hfx.2, by omega, hβ, hvNum⟩
  have hnxVal : _root_.F2R (beta:=beta) nx = x := by
    have h := FnormalizeCorrect (beta:=beta) beta bo prec.toNat fx
    have hn : _root_.F2R (beta:=beta) nx = _root_.F2R (beta:=beta) fx := by
      simpa only [wp, PostCond.noThrow, pure, FnormalizeCorrect_check,
        Id.run, ULift.up_down, nx, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨rfl, hβ⟩
    exact hn.trans hfx.1
  have hpNx : Closest (beta:=beta) bo (beta : ℝ)
      (_root_.F2R (beta:=beta) nx * ((beta : ℝ) ^ (s.toNat : Int) + 1)) fp := by
    simpa [bo, bnd, hnxVal, hpw.2.2, hsNat,
      FloatSpec.Core.Raux.bpow] using hpw.2.1
  have hqNx : Closest (beta:=beta) bo (beta : ℝ)
      (_root_.F2R (beta:=beta) nx - _root_.F2R (beta:=beta) fp) fq := by
    simpa [bo, bnd, hnxVal, hpw.2.2] using hqw.2.1
  have hhxPff : Closest (beta:=beta) bo (beta : ℝ)
      (_root_.F2R (beta:=beta) fq + _root_.F2R (beta:=beta) fp) fhx := by
    simpa [bo, bnd, hqw.2.2, hpw.2.2] using hhxw.2.1
  have hCore :
      ∃ g : FloatSpec.Core.Defs.FlocqFloat beta,
        _root_.F2R (beta:=beta) g = hx ∧
        Closest (beta:=beta) (Veltkamp_reducedBound beta bo s.toNat prec.toNat)
          (beta : ℝ) x g := by
    rcases hnxCan with hnormal | hsub
    · rcases VeltkampN (beta:=beta) bo beta s.toNat prec.toNat nx fp fq fhx
          rfl hβ hvNum (by omega) (by omega) hnormal hpNx hqNx hhxPff with
        ⟨_, g, hgVal, hgClose, _⟩
      exact ⟨g, hgVal.trans hhxw.2.2, by simpa [hnxVal] using hgClose⟩
    · rcases VeltkampS (beta:=beta) bo beta s.toNat prec.toNat nx fp fq fhx
          rfl hβ hvNum (by omega) (by omega) hsub hpNx hqNx hhxPff with
        ⟨_, g, hgVal, hgClose⟩
      exact ⟨g, hgVal.trans hhxw.2.2, by simpa [hnxVal] using hgClose⟩
  let redPrec : Int := prec - s
  have hredPrec : precisionNotZero redPrec := by
    unfold precisionNotZero redPrec
    omega
  haveI : Prec_gt_0 redPrec := ⟨by unfold redPrec; omega⟩
  let redBound : Fbound := make_bound beta redPrec emin (hβ := hβ)
  have hredPBound : pGivesBound beta redBound redPrec := by
    have h := make_bound_p beta redPrec emin
    have hv : redBound.vNum = Zpower_nat beta redPrec.natAbs := by
      simpa [redBound, wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound, redPrec, habsRed] using hv
  have hredExp : -redBound.dExp = emin := by
    have h := make_bound_Emin beta redPrec emin
    have hd : redBound.dExp = -emin := by
      simpa [redBound, wp, PostCond.noThrow, make_bound_Emin_check, pure] using h hemin
    omega
  have hredBoundEq :
      Veltkamp_reducedBound beta bo s.toNat prec.toNat = toFboundSkel redBound := by
    have hredNotNeg : ¬ prec - s < 0 := by omega
    simp [Veltkamp_reducedBound, bo, bnd, redBound, redPrec, toFboundSkel,
      make_bound, Bound, hemin, hnatSub, habsRed, hredNotNeg]
  rcases hCore with ⟨g, hgVal, hgClose⟩
  rcases pff_round_is_round_N beta redBound redPrec x g hredPBound hredPrec hβ
      (by simpa [hredBoundEq] using hgClose) with ⟨choice', hgRound⟩
  refine ⟨choice', ?_⟩
  calc
    hx = _root_.F2R (beta:=beta) g := hgVal.symm
    _ = FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp (-redBound.dExp) redPrec)
        (FloatSpec.Core.Generic_fmt.Znearest choice') x := hgRound
    _ = FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin (prec - s))
        (FloatSpec.Core.Generic_fmt.Znearest choice') x := by
      simp [hredExp, redPrec]

/-- Coq `Pff2Flocq.Veltkamp_tail`, deriving both exact reconstruction and the
`s`-digit format of the locally computed residual. -/
theorem Veltkamp_tail (beta emin prec s : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (x : ℝ)
    (hprecision : 3 ≤ prec)
    (hemin : emin ≤ 0)
    (hs_le : 2 ≤ s)
    (hs_ge : s ≤ prec - 2)
    (Fx : generic_format beta (FLT_exp emin prec) x) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let p := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
      (x * (FloatSpec.Core.Raux.bpow beta s + 1))
    let q := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x - p)
    let hx := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (q + p)
    let tx := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x - hx)
    x = hx + tx ∧ generic_format beta (FLT_exp emin s) tx := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let p := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
    (x * (FloatSpec.Core.Raux.bpow beta s + 1))
  let q := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x - p)
  let hx := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (q + p)
  let tx := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x - hx)
  have hβ : 1 < beta := ValidRadix.valid
  have hprec : precisionNotZero prec := by
    unfold precisionNotZero
    omega
  have hprecPos : 0 ≤ prec := by omega
  have hsPos : 0 ≤ s := by omega
  have hsNat : (s.toNat : Int) = s := Int.toNat_of_nonneg hsPos
  have habsPrec : prec.natAbs = prec.toNat := by omega
  have habsS : s.natAbs = s.toNat := by omega
  let bnd : Fbound := make_bound beta prec emin (hβ := hβ)
  let bo : Fbound_skel := toFboundSkel bnd
  have hpBound : pGivesBound beta bnd prec := by
    have h := make_bound_p beta prec emin
    have hv : bnd.vNum = Zpower_nat beta prec.natAbs := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound, habsPrec] using hv
  have hvNum : bo.vNum = Zpower_nat beta prec.toNat := by
    simpa [bo, pGivesBound, habsPrec] using hpBound
  rcases Veltkamp_tail_round_N_witnesses beta emin prec s choice x hβ hprec hemin Fx with
    ⟨fx, fp, fq, fhx, ftx, hfx, hpw, hqw, hhxw, htxw⟩
  let nx : FloatSpec.Core.Defs.FlocqFloat beta :=
    Fnormalize (beta:=beta) beta bo prec.toNat fx
  have hnxCan : Fcanonic (beta:=beta) beta bo nx := by
    have h := FnormalizeCanonic (beta:=beta) beta bo prec.toNat fx
    simpa only [wp, PostCond.noThrow, pure, FnormalizeCanonic_check,
      Id.run, ULift.up_down, nx, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using
      h ⟨hfx.2, hfx.2, by omega, hβ, hvNum⟩
  have hnxVal : _root_.F2R (beta:=beta) nx = x := by
    have h := FnormalizeCorrect (beta:=beta) beta bo prec.toNat fx
    have hn : _root_.F2R (beta:=beta) nx = _root_.F2R (beta:=beta) fx := by
      simpa only [wp, PostCond.noThrow, pure, FnormalizeCorrect_check,
        Id.run, ULift.up_down, nx, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨rfl, hβ⟩
    exact hn.trans hfx.1
  have hpNx : Closest (beta:=beta) bo (beta : ℝ)
      (_root_.F2R (beta:=beta) nx * ((beta : ℝ) ^ (s.toNat : Int) + 1)) fp := by
    simpa [bo, bnd, hnxVal, hpw.2.2, hsNat,
      FloatSpec.Core.Raux.bpow] using hpw.2.1
  have hqNx : Closest (beta:=beta) bo (beta : ℝ)
      (_root_.F2R (beta:=beta) nx - _root_.F2R (beta:=beta) fp) fq := by
    simpa [bo, bnd, hnxVal, hpw.2.2] using hqw.2.1
  have hhxPff : Closest (beta:=beta) bo (beta : ℝ)
      (_root_.F2R (beta:=beta) fq + _root_.F2R (beta:=beta) fp) fhx := by
    simpa [bo, bnd, hqw.2.2, hpw.2.2] using hhxw.2.1
  have htxPff : Closest (beta:=beta) bo (beta : ℝ)
      (_root_.F2R (beta:=beta) nx - _root_.F2R (beta:=beta) fhx) ftx := by
    simpa [bo, bnd, hnxVal, hhxw.2.2] using htxw.2.1
  rcases VeltkampU (beta:=beta) bo beta s.toNat prec.toNat nx fp fq fhx ftx
      rfl hβ hvNum (by omega) (by omega) hnxCan hpNx hqNx hhxPff htxPff with
    ⟨_, hsum, _, ftx', hftx'Val, hftx'Bound, _⟩
  have hsplitBound :
      Veltkamp_splitBound beta bo s.toNat =
        toFboundSkel (make_bound beta s emin (hβ := hβ)) := by
    have hsNotNeg : ¬ s < 0 := by omega
    simp [Veltkamp_splitBound, bo, bnd, toFboundSkel, make_bound,
      Bound, hemin, habsS, hsNotNeg]
  have hTail :
      ∃ g : FloatSpec.Core.Defs.FlocqFloat beta,
        _root_.F2R (beta:=beta) g = tx ∧
        x = hx + _root_.F2R (beta:=beta) g ∧
        Fbounded (beta:=beta) (toFboundSkel (make_bound beta s emin)) g := by
    refine ⟨ftx', ?_, ?_, ?_⟩
    · exact hftx'Val.trans htxw.2.2
    · calc
        x = _root_.F2R (beta:=beta) nx := hnxVal.symm
        _ = _root_.F2R (beta:=beta) fhx + _root_.F2R (beta:=beta) ftx := hsum
        _ = hx + _root_.F2R (beta:=beta) ftx' := by
          rw [hhxw.2.2, hftx'Val]
    · simpa [hsplitBound] using hftx'Bound
  simpa [rnd, p, q, hx, tx] using
    Veltkamp_tail_from_pff_tail_payload beta emin prec s x hx tx hβ hemin hs_le hTail

-- Coq theorem: `Dekker`
-- We mirror the statement structure by introducing local `let`-bound
-- intermediates that model the algorithm steps, and we state both the
-- conditional exactness and the global error bound.

/-- The radix-2 FLT nearest rounding used by the Pff2Flocq Dekker wrapper. -/
noncomputable def Dekker_round (emin prec : Int) (choice : Int → Bool) (z : ℝ) : ℝ :=
  FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
    (FloatSpec.Core.Generic_fmt.Znearest choice) z

/-- The final Dekker correction term `t4` from Coq `Pff2Flocq.Dekker`. -/
noncomputable def Dekker_t4 (emin prec s : Int) (choice : Int → Bool)
    (x y : ℝ) : ℝ :=
  let round_flt := Dekker_round emin prec choice
  let px := round_flt (x * (FloatSpec.Core.Raux.bpow 2 s + 1))
  let qx := round_flt (x - px)
  let hx := round_flt (qx + px)
  let tx := round_flt (x - hx)
  let py := round_flt (y * (FloatSpec.Core.Raux.bpow 2 s + 1))
  let qy := round_flt (y - py)
  let hy := round_flt (qy + py)
  let ty := round_flt (y - hy)
  let x1y1 := round_flt (hx * hy)
  let x1y2 := round_flt (hx * ty)
  let x2y1 := round_flt (tx * hy)
  let x2y2 := round_flt (tx * ty)
  let r := round_flt (x * y)
  let t1 := round_flt (-r + x1y1)
  let t2 := round_flt (t1 + x1y2)
  let t3 := round_flt (t2 + x2y1)
  round_flt (t3 + x2y2)

/-- The exact Coq-style postcondition for the Pff2Flocq `Dekker` wrapper. -/
def Dekker_result (emin prec s : Int) (choice : Int → Bool) (x y : ℝ) : Prop :=
  let round_flt := Dekker_round emin prec choice
  let r := round_flt (x * y)
  let t4 := Dekker_t4 emin prec s choice x y
  (x * y = 0 ∨ FloatSpec.Core.Raux.bpow 2 (emin + 2 * prec - 1) ≤ |x * y| →
      x * y = r + t4) ∧
    |x * y - (r + t4)| ≤ (7 / 2 : ℝ) * FloatSpec.Core.Raux.bpow 2 emin

/-- The `x = 0` branch at the start of Coq `Pff2Flocq.Dekker`. -/
theorem Dekker_result_of_x_eq_zero (emin prec s : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (x y : ℝ) (hx : x = 0) :
    Dekker_result emin prec s choice x y := by
  classical
  subst x
  let round_flt := Dekker_round emin prec choice
  have hround0 : round_flt 0 = 0 := by
    simpa [round_flt, Dekker_round] using
      roundR_Znearest_zero emin prec choice
  have ht4 : Dekker_t4 emin prec s choice 0 y = 0 := by
    simp [Dekker_t4, Dekker_round, hround0, round_flt, roundR_Znearest_zero]
  have hr : round_flt (0 * y) = 0 := by
    simp [hround0, round_flt]
  have hround0' : Dekker_round emin prec choice 0 = 0 := by
    simpa [round_flt] using hround0
  unfold Dekker_result
  dsimp [round_flt]
  constructor
  · intro _
    simpa [zero_mul, hround0', ht4]
  · simp [zero_mul, hround0', ht4]
    have hpow_nonneg : 0 ≤ FloatSpec.Core.Raux.bpow 2 emin := by
      simpa [FloatSpec.Core.Raux.bpow] using
        (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) emin))
    exact hpow_nonneg

/-- The `y = 0` branch at the start of Coq `Pff2Flocq.Dekker`. -/
theorem Dekker_result_of_y_eq_zero (emin prec s : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (x y : ℝ) (hy : y = 0) :
    Dekker_result emin prec s choice x y := by
  classical
  subst y
  let round_flt := Dekker_round emin prec choice
  have hround0 : round_flt 0 = 0 := by
    simpa [round_flt, Dekker_round] using
      roundR_Znearest_zero emin prec choice
  have ht4 : Dekker_t4 emin prec s choice x 0 = 0 := by
    simp [Dekker_t4, Dekker_round, hround0, round_flt, roundR_Znearest_zero]
  have hr : round_flt (x * 0) = 0 := by
    simp [hround0, round_flt]
  have hround0' : Dekker_round emin prec choice 0 = 0 := by
    simpa [round_flt] using hround0
  unfold Dekker_result
  dsimp [round_flt]
  constructor
  · intro _
    simpa [mul_zero, hround0', ht4]
  · simp [mul_zero, hround0', ht4]
    have hpow_nonneg : 0 ≤ FloatSpec.Core.Raux.bpow 2 emin := by
      simpa [FloatSpec.Core.Raux.bpow] using
        (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) emin))
    exact hpow_nonneg

/-- The zero-product branch of Coq `Pff2Flocq.Dekker`, obtained from the two
zero-input branches over reals. -/
theorem Dekker_result_of_product_eq_zero (emin prec s : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (x y : ℝ) (hxy : x * y = 0) :
    Dekker_result emin prec s choice x y := by
  rcases mul_eq_zero.mp hxy with hx | hy
  · exact Dekker_result_of_x_eq_zero (emin := emin) (prec := prec) (s := s)
      (choice := choice) (x := x) (y := y) hx
  · exact Dekker_result_of_y_eq_zero (emin := emin) (prec := prec) (s := s)
      (choice := choice) (x := x) (y := y) hy

/-- Pff-side witnesses for the rounded values in Coq `Pff2Flocq.Dekker`.

The public Dekker proof converts formatted inputs to bounded Pff floats, then
destructs `round_N_is_pff_round` for two Veltkamp decompositions, four product
rounds, and the five final summation rounds.  This helper packages that
wrapper-side construction independently of the remaining final call to the
lower Pff `Dekker_FTS_closed` payload. -/
theorem Dekker_round_N_witnesses (emin prec s : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (x y : ℝ)
    (hprec : precisionNotZero prec)
    (hemin : emin ≤ 0)
    (Fx : generic_format 2 (FLT_exp emin prec) x)
    (Fy : generic_format 2 (FLT_exp emin prec) y) :
    let bnd : Fbound := make_bound 2 prec emin
    let bo : Fbound_skel := toFboundSkel bnd
    let round_flt := Dekker_round emin prec choice
    let valueWitness := fun (value : ℝ) (f : FloatSpec.Core.Defs.FlocqFloat 2) =>
      _root_.F2R (beta:=2) f = value ∧ Fbounded (beta:=2) bo f
    let roundWitness := fun (input rounded : ℝ)
        (f : FloatSpec.Core.Defs.FlocqFloat 2) =>
      Fcanonic (beta:=2) 2 bo f ∧
        Closest (beta:=2) bo (2 : ℝ) input f ∧
        _root_.F2R (beta:=2) f = rounded
    let px := round_flt (x * (FloatSpec.Core.Raux.bpow 2 s + 1))
    let qx := round_flt (x - px)
    let hx := round_flt (qx + px)
    let tx := round_flt (x - hx)
    let py := round_flt (y * (FloatSpec.Core.Raux.bpow 2 s + 1))
    let qy := round_flt (y - py)
    let hy := round_flt (qy + py)
    let ty := round_flt (y - hy)
    let x1y1 := round_flt (hx * hy)
    let x1y2 := round_flt (hx * ty)
    let x2y1 := round_flt (tx * hy)
    let x2y2 := round_flt (tx * ty)
    let r := round_flt (x * y)
    let t1 := round_flt (-r + x1y1)
    let t2 := round_flt (t1 + x1y2)
    let t3 := round_flt (t2 + x2y1)
    let t4 := round_flt (t3 + x2y2)
    ∃ fx fpx fqx fhx ftx fy fpy fqy fhy fty
      fx1y1 fx1y2 fx2y1 fx2y2 fr ft1 ft2 ft3 ft4 :
        FloatSpec.Core.Defs.FlocqFloat 2,
      valueWitness x fx ∧
        roundWitness (x * (FloatSpec.Core.Raux.bpow 2 s + 1)) px fpx ∧
        roundWitness (x - px) qx fqx ∧
        roundWitness (qx + px) hx fhx ∧
        roundWitness (x - hx) tx ftx ∧
        valueWitness y fy ∧
        roundWitness (y * (FloatSpec.Core.Raux.bpow 2 s + 1)) py fpy ∧
        roundWitness (y - py) qy fqy ∧
        roundWitness (qy + py) hy fhy ∧
        roundWitness (y - hy) ty fty ∧
        roundWitness (hx * hy) x1y1 fx1y1 ∧
        roundWitness (hx * ty) x1y2 fx1y2 ∧
        roundWitness (tx * hy) x2y1 fx2y1 ∧
        roundWitness (tx * ty) x2y2 fx2y2 ∧
        roundWitness (x * y) r fr ∧
        roundWitness (-r + x1y1) t1 ft1 ∧
        roundWitness (t1 + x1y2) t2 ft2 ∧
        roundWitness (t2 + x2y1) t3 ft3 ∧
        roundWitness (t3 + x2y2) t4 ft4 := by
  classical
  let bnd : Fbound := make_bound 2 prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  let round_flt := Dekker_round emin prec choice
  let valueWitness := fun (value : ℝ) (f : FloatSpec.Core.Defs.FlocqFloat 2) =>
    _root_.F2R (beta:=2) f = value ∧ Fbounded (beta:=2) bo f
  let roundWitness := fun (input rounded : ℝ)
      (f : FloatSpec.Core.Defs.FlocqFloat 2) =>
    Fcanonic (beta:=2) 2 bo f ∧
      Closest (beta:=2) bo (2 : ℝ) input f ∧
      _root_.F2R (beta:=2) f = rounded
  let px := round_flt (x * (FloatSpec.Core.Raux.bpow 2 s + 1))
  let qx := round_flt (x - px)
  let hx := round_flt (qx + px)
  let tx := round_flt (x - hx)
  let py := round_flt (y * (FloatSpec.Core.Raux.bpow 2 s + 1))
  let qy := round_flt (y - py)
  let hy := round_flt (qy + py)
  let ty := round_flt (y - hy)
  let x1y1 := round_flt (hx * hy)
  let x1y2 := round_flt (hx * ty)
  let x2y1 := round_flt (tx * hy)
  let x2y2 := round_flt (tx * ty)
  let r := round_flt (x * y)
  let t1 := round_flt (-r + x1y1)
  let t2 := round_flt (t1 + x1y2)
  let t3 := round_flt (t2 + x2y1)
  let t4 := round_flt (t3 + x2y2)
  have hβ : (1 : Int) < 2 := by decide
  have hpBound : pGivesBound 2 bnd prec := by
    have h := make_bound_p 2 prec emin (hp := by exact hprec)
    have hv : (make_bound 2 prec emin).vNum =
        Zpower_nat 2 (prec.natAbs) := by
      simpa [wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound, bnd] using hv
  have hbnd_dExp : -bnd.dExp = emin := by
    have h := make_bound_Emin 2 prec emin (hp := by exact hprec)
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using
        h hemin
    omega
  have hformatWitness
      (z : ℝ) (hz : generic_format 2 (FLT_exp emin prec) z) :
      ∃ f : FloatSpec.Core.Defs.FlocqFloat 2, valueWitness z f := by
    have hz_bnd : generic_format 2 (FLT_exp (-bnd.dExp) prec) z := by
      simpa [hbnd_dExp] using hz
    rcases (by
        have h := format_is_flocq_bounded 2 bnd prec z
        simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
          using h ⟨hz_bnd, hpBound, hprec, hβ⟩) with
      ⟨fz, hfz_val, hfz_bound⟩
    exact ⟨fz, hfz_val, hfz_bound⟩
  have hroundWitness (z : ℝ) :
      ∃ f : FloatSpec.Core.Defs.FlocqFloat 2,
        roundWitness z (round_flt z) f := by
    rcases (round_N_is_pff_round (beta := 2) (b := bnd) (p := prec)
        (choice := choice) (r := z)
        (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
      ⟨fz, hfz_can, hfz_closest, hfz_val⟩
    refine ⟨fz, hfz_can, hfz_closest, ?_⟩
    simpa [round_flt, Dekker_round, hbnd_dExp, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hfz_val
  rcases hformatWitness x Fx with ⟨fx, hfx⟩
  rcases hroundWitness (x * (FloatSpec.Core.Raux.bpow 2 s + 1)) with
    ⟨fpx, hfpx⟩
  rcases hroundWitness (x - px) with ⟨fqx, hfqx⟩
  rcases hroundWitness (qx + px) with ⟨fhx, hfhx⟩
  rcases hroundWitness (x - hx) with ⟨ftx, hftx⟩
  rcases hformatWitness y Fy with ⟨fy, hfy⟩
  rcases hroundWitness (y * (FloatSpec.Core.Raux.bpow 2 s + 1)) with
    ⟨fpy, hfpy⟩
  rcases hroundWitness (y - py) with ⟨fqy, hfqy⟩
  rcases hroundWitness (qy + py) with ⟨fhy, hfhy⟩
  rcases hroundWitness (y - hy) with ⟨fty, hfty⟩
  rcases hroundWitness (hx * hy) with ⟨fx1y1, hfx1y1⟩
  rcases hroundWitness (hx * ty) with ⟨fx1y2, hfx1y2⟩
  rcases hroundWitness (tx * hy) with ⟨fx2y1, hfx2y1⟩
  rcases hroundWitness (tx * ty) with ⟨fx2y2, hfx2y2⟩
  rcases hroundWitness (x * y) with ⟨fr, hfr⟩
  rcases hroundWitness (-r + x1y1) with ⟨ft1, hft1⟩
  rcases hroundWitness (t1 + x1y2) with ⟨ft2, hft2⟩
  rcases hroundWitness (t2 + x2y1) with ⟨ft3, hft3⟩
  rcases hroundWitness (t3 + x2y2) with ⟨ft4, hft4⟩
  exact ⟨fx, fpx, fqx, fhx, ftx, fy, fpy, fqy, fhy, fty,
    fx1y1, fx1y2, fx2y1, fx2y2, fr, ft1, ft2, ft3, ft4,
    hfx, hfpx, hfqx, hfhx, hftx, hfy, hfpy, hfqy, hfhy, hfty,
    hfx1y1, hfx1y2, hfx2y1, hfx2y2, hfr, hft1, hft2, hft3, hft4⟩

noncomputable def Dekker_check (emin prec s : Int)
    (choice : Int → Bool) (x y : ℝ) : Unit :=
  ()

/-- Checked wrapper-side payload for Coq `Dekker`.

This restores a nontrivial public theorem at the upstream name without
claiming the still-missing lower Pff `Dekker` error-bound payload.  It proves
the zero-product public postcondition and packages the bounded/canonical Pff
witnesses that the Coq `Pff2Flocq.Dekker` wrapper constructs before invoking
the lower Pff theorem. -/
theorem Dekker_from_zero_branch_and_rounding_witnesses (emin prec s : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (x y : ℝ)
    (hprec : precisionNotZero prec)
    (hemin : emin ≤ 0)
    (Fx : generic_format 2 (FLT_exp emin prec) x)
    (Fy : generic_format 2 (FLT_exp emin prec) y) :
    (x * y = 0 → Dekker_result emin prec s choice x y) ∧
      let bnd : Fbound := make_bound 2 prec emin
      let bo : Fbound_skel := toFboundSkel bnd
      let round_flt := Dekker_round emin prec choice
      let valueWitness := fun (value : ℝ) (f : FloatSpec.Core.Defs.FlocqFloat 2) =>
        _root_.F2R (beta:=2) f = value ∧ Fbounded (beta:=2) bo f
      let roundWitness := fun (input rounded : ℝ)
          (f : FloatSpec.Core.Defs.FlocqFloat 2) =>
        Fcanonic (beta:=2) 2 bo f ∧
          Closest (beta:=2) bo (2 : ℝ) input f ∧
          _root_.F2R (beta:=2) f = rounded
      let px := round_flt (x * (FloatSpec.Core.Raux.bpow 2 s + 1))
      let qx := round_flt (x - px)
      let hx := round_flt (qx + px)
      let tx := round_flt (x - hx)
      let py := round_flt (y * (FloatSpec.Core.Raux.bpow 2 s + 1))
      let qy := round_flt (y - py)
      let hy := round_flt (qy + py)
      let ty := round_flt (y - hy)
      let x1y1 := round_flt (hx * hy)
      let x1y2 := round_flt (hx * ty)
      let x2y1 := round_flt (tx * hy)
      let x2y2 := round_flt (tx * ty)
      let r := round_flt (x * y)
      let t1 := round_flt (-r + x1y1)
      let t2 := round_flt (t1 + x1y2)
      let t3 := round_flt (t2 + x2y1)
      let t4 := round_flt (t3 + x2y2)
      ∃ fx fpx fqx fhx ftx fy fpy fqy fhy fty
        fx1y1 fx1y2 fx2y1 fx2y2 fr ft1 ft2 ft3 ft4 :
          FloatSpec.Core.Defs.FlocqFloat 2,
        valueWitness x fx ∧
          roundWitness (x * (FloatSpec.Core.Raux.bpow 2 s + 1)) px fpx ∧
          roundWitness (x - px) qx fqx ∧
          roundWitness (qx + px) hx fhx ∧
          roundWitness (x - hx) tx ftx ∧
          valueWitness y fy ∧
          roundWitness (y * (FloatSpec.Core.Raux.bpow 2 s + 1)) py fpy ∧
          roundWitness (y - py) qy fqy ∧
          roundWitness (qy + py) hy fhy ∧
          roundWitness (y - hy) ty fty ∧
          roundWitness (hx * hy) x1y1 fx1y1 ∧
          roundWitness (hx * ty) x1y2 fx1y2 ∧
          roundWitness (tx * hy) x2y1 fx2y1 ∧
          roundWitness (tx * ty) x2y2 fx2y2 ∧
          roundWitness (x * y) r fr ∧
          roundWitness (-r + x1y1) t1 ft1 ∧
          roundWitness (t1 + x1y2) t2 ft2 ∧
          roundWitness (t2 + x2y1) t3 ft3 ∧
          roundWitness (t3 + x2y2) t4 ft4 := by
  constructor
  · intro hxy
    exact Dekker_result_of_product_eq_zero (emin := emin) (prec := prec)
      (s := s) (choice := choice) (x := x) (y := y) hxy
  · simpa using
      Dekker_round_N_witnesses (emin := emin) (prec := prec) (s := s)
        (choice := choice) (x := x) (y := y) hprec hemin Fx Fy

/-- Coq `Pff2Flocq.Dekker`.  The source's local split precision and all
nineteen nearest-rounding witnesses are reconstructed internally. -/
theorem Dekker (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (x y : ℝ)
    (hprecision : 4 ≤ prec)
    (hemin : emin < 0)
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (hBranch : beta = 2 ∨ Even prec) :
    let s := prec - prec / 2
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let round_flt := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
    let px := round_flt (x * (FloatSpec.Core.Raux.bpow beta s + 1))
    let qx := round_flt (x - px)
    let hx := round_flt (qx + px)
    let tx := round_flt (x - hx)
    let py := round_flt (y * (FloatSpec.Core.Raux.bpow beta s + 1))
    let qy := round_flt (y - py)
    let hy := round_flt (qy + py)
    let ty := round_flt (y - hy)
    let x1y1 := round_flt (hx * hy)
    let x1y2 := round_flt (hx * ty)
    let x2y1 := round_flt (tx * hy)
    let x2y2 := round_flt (tx * ty)
    let r := round_flt (x * y)
    let t1 := round_flt (-r + x1y1)
    let t2 := round_flt (t1 + x1y2)
    let t3 := round_flt (t2 + x2y1)
    let t4 := round_flt (t3 + x2y2)
    (x * y = 0 ∨ FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |x * y| →
        x * y = r + t4) ∧
      |x * y - (r + t4)| ≤
        (7 / 2 : ℝ) * FloatSpec.Core.Raux.bpow beta emin := by
  classical
  let s := prec - prec / 2
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let round_flt := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
  let px := round_flt (x * (FloatSpec.Core.Raux.bpow beta s + 1))
  let qx := round_flt (x - px)
  let hx := round_flt (qx + px)
  let tx := round_flt (x - hx)
  let py := round_flt (y * (FloatSpec.Core.Raux.bpow beta s + 1))
  let qy := round_flt (y - py)
  let hy := round_flt (qy + py)
  let ty := round_flt (y - hy)
  let x1y1 := round_flt (hx * hy)
  let x1y2 := round_flt (hx * ty)
  let x2y1 := round_flt (tx * hy)
  let x2y2 := round_flt (tx * ty)
  let r := round_flt (x * y)
  let t1 := round_flt (-r + x1y1)
  let t2 := round_flt (t1 + x1y2)
  let t3 := round_flt (t2 + x2y1)
  let t4 := round_flt (t3 + x2y2)
  have hβ : 1 < beta := ValidRadix.valid
  have hround0 : round_flt 0 = 0 := by
    have hrnd0 : rnd 0 = 0 := by simpa [rnd] using Znearest_of_int choice 0
    simp [round_flt, FloatSpec.Core.Generic_fmt.roundR,
      FloatSpec.Core.Generic_fmt.scaled_mantissa, hrnd0]
  by_cases hx0 : x = 0
  · subst x
    have hpx : px = 0 := by simp [px, hround0]
    have hqx : qx = 0 := by simp [qx, hpx, hround0]
    have hhx : hx = 0 := by simp [hx, hqx, hpx, hround0]
    have htx : tx = 0 := by simp [tx, hhx, hround0]
    have hx11 : x1y1 = 0 := by simp [x1y1, hhx, hround0]
    have hx12 : x1y2 = 0 := by simp [x1y2, hhx, hround0]
    have hx21 : x2y1 = 0 := by simp [x2y1, htx, hround0]
    have hx22 : x2y2 = 0 := by simp [x2y2, htx, hround0]
    have hr : r = 0 := by simp [r, hround0]
    have ht1 : t1 = 0 := by simp [t1, hr, hx11, hround0]
    have ht2 : t2 = 0 := by simp [t2, ht1, hx12, hround0]
    have ht3 : t3 = 0 := by simp [t3, ht2, hx21, hround0]
    have ht4 : t4 = 0 := by simp [t4, ht3, hx22, hround0]
    change (0 * y = 0 ∨
        FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |0 * y| →
          0 * y = r + t4) ∧
      |0 * y - (r + t4)| ≤
        (7 / 2 : ℝ) * FloatSpec.Core.Raux.bpow beta emin
    constructor
    · intro _; simp [hr, ht4]
    · rw [hr, ht4]
      simp only [zero_mul, zero_add, sub_zero, abs_zero]
      exact mul_nonneg (by norm_num) (le_of_lt (by
        exact zpow_pos (show (0 : ℝ) < (beta : ℝ) by exact_mod_cast
          (show (0 : Int) < beta by omega)) emin))
  by_cases hy0 : y = 0
  · subst y
    have hpy : py = 0 := by simp [py, hround0]
    have hqy : qy = 0 := by simp [qy, hpy, hround0]
    have hhy : hy = 0 := by simp [hy, hqy, hpy, hround0]
    have hty : ty = 0 := by simp [ty, hhy, hround0]
    have hx11 : x1y1 = 0 := by simp [x1y1, hhy, hround0]
    have hx12 : x1y2 = 0 := by simp [x1y2, hty, hround0]
    have hx21 : x2y1 = 0 := by simp [x2y1, hhy, hround0]
    have hx22 : x2y2 = 0 := by simp [x2y2, hty, hround0]
    have hr : r = 0 := by simp [r, hround0]
    have ht1 : t1 = 0 := by simp [t1, hr, hx11, hround0]
    have ht2 : t2 = 0 := by simp [t2, ht1, hx12, hround0]
    have ht3 : t3 = 0 := by simp [t3, ht2, hx21, hround0]
    have ht4 : t4 = 0 := by simp [t4, ht3, hx22, hround0]
    change (x * 0 = 0 ∨
        FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |x * 0| →
          x * 0 = r + t4) ∧
      |x * 0 - (r + t4)| ≤
        (7 / 2 : ℝ) * FloatSpec.Core.Raux.bpow beta emin
    constructor
    · intro _; simp [hr, ht4]
    · rw [hr, ht4]
      simp only [mul_zero, zero_add, sub_zero, abs_zero]
      exact mul_nonneg (by norm_num) (le_of_lt (by
        exact zpow_pos (show (0 : ℝ) < (beta : ℝ) by exact_mod_cast
          (show (0 : Int) < beta by omega)) emin))
  have hprec : precisionNotZero prec := by unfold precisionNotZero; omega
  have hprecNonneg : 0 ≤ prec := by omega
  have hprecNat : (prec.toNat : Int) = prec := Int.toNat_of_nonneg hprecNonneg
  have hprecisionNat : 4 ≤ prec.toNat := by omega
  have hsNonneg : 0 ≤ s := by
    dsimp [s]
    have := Int.ediv_le_self prec (by omega : 0 ≤ prec)
    omega
  have hsNat : ((prec.toNat - Nat.div2 prec.toNat : Nat) : Int) = s := by
    simp only [Nat.div2_val, Nat.cast_sub (by omega : prec.toNat / 2 ≤ prec.toNat)]
    rw [Int.natCast_ediv]
    simp [s, hprecNat]
  have hBranchNat : beta = 2 ∨ Even prec.toNat := by
    rcases hBranch with hb | he
    · exact Or.inl hb
    · right
      rcases he with ⟨k, hk⟩
      have hkNonneg : 0 ≤ k := by omega
      refine ⟨k.toNat, ?_⟩
      have hkNat : (k.toNat : Int) = k := Int.toNat_of_nonneg hkNonneg
      apply Nat.cast_injective (R := Int)
      push_cast
      rw [hprecNat, hkNat]
      omega
  let bnd : Fbound := make_bound beta prec emin (hβ := hβ)
  let bo : Fbound_skel := toFboundSkel bnd
  have hpBound : pGivesBound beta bnd prec := by
    have h := make_bound_p beta prec emin
    have hv : bnd.vNum = Zpower_nat beta prec.natAbs := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound] using hv
  have habsPrec : prec.natAbs = prec.toNat := by omega
  have hvNum : bo.vNum = Zpower_nat beta prec.toNat := by
    simpa [bo, pGivesBound, habsPrec] using hpBound
  have hbndExp : -bnd.dExp = emin := by
    have h := make_bound_Emin beta prec emin
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using h (le_of_lt hemin)
    omega
  have hboExp : -bo.dExp = emin := by simpa [bo] using hbndExp
  have hdExpPos : 0 < bo.dExp := by omega
  have hformatCan (z : ℝ) (hz : generic_format beta (FLT_exp emin prec) z) :
      ∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
        _root_.F2R (beta:=beta) f = z ∧ Fcanonic (beta:=beta) beta bo f := by
    have hz' : generic_format beta (FLT_exp (-bnd.dExp) prec) z := by
      simpa [hbndExp] using hz
    have h := format_is_pff_format_can beta bnd prec z
    simpa [wp, PostCond.noThrow, format_is_pff_format'_check, pure,
      PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, PFcanonic,
      pff_to_R_aux, pff_to_flocq, bo]
      using h ⟨hz', hpBound, hprec, hβ⟩
  have hround (z : ℝ) :
      ∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
        Fcanonic (beta:=beta) beta bo f ∧
          Closest (beta:=beta) bo (beta : ℝ) z f ∧
          _root_.F2R (beta:=beta) f = round_flt z := by
    rcases round_N_is_pff_round (beta:=beta) (b:=bnd) (p:=prec)
        (choice:=choice) (r:=z) hpBound hprec hβ with ⟨f, hfCan, hfClose, hfVal⟩
    exact ⟨f, by simpa [bo, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hfCan, by simpa [bo] using hfClose,
      by simpa [round_flt, rnd, hbndExp] using hfVal⟩
  rcases hformatCan x Fx with ⟨fx, hfxVal, hfxCan⟩
  rcases hformatCan y Fy with ⟨fy, hfyVal, hfyCan⟩
  rcases hround (x * (FloatSpec.Core.Raux.bpow beta s + 1)) with ⟨fpx, hfpx⟩
  rcases hround (x - px) with ⟨fqx, hfqx⟩
  rcases hround (qx + px) with ⟨fhx, hfhx⟩
  rcases hround (x - hx) with ⟨ftx, hftx⟩
  rcases hround (y * (FloatSpec.Core.Raux.bpow beta s + 1)) with ⟨fpy, hfpy⟩
  rcases hround (y - py) with ⟨fqy, hfqy⟩
  rcases hround (qy + py) with ⟨fhy, hfhy⟩
  rcases hround (y - hy) with ⟨fty, hfty⟩
  rcases hround (hx * hy) with ⟨fx1y1, hfx1y1⟩
  rcases hround (hx * ty) with ⟨fx1y2, hfx1y2⟩
  rcases hround (tx * hy) with ⟨fx2y1, hfx2y1⟩
  rcases hround (tx * ty) with ⟨fx2y2, hfx2y2⟩
  rcases hround (x * y) with ⟨fr, hfr⟩
  rcases hround (-r + x1y1) with ⟨ft1, hft1⟩
  rcases hround (t1 + x1y2) with ⟨ft2, hft2⟩
  rcases hround (t2 + x2y1) with ⟨ft3, hft3⟩
  rcases hround (t3 + x2y2) with ⟨ft4, hft4⟩
  let nt1 := Fopp (beta:=beta) ft1
  let nt2 := Fopp (beta:=beta) ft2
  let nt3 := Fopp (beta:=beta) ft3
  let nt4 := Fopp (beta:=beta) ft4
  have hnval (f : FloatSpec.Core.Defs.FlocqFloat beta) :
      _root_.F2R (beta:=beta) (Fopp (beta:=beta) f) = -_root_.F2R (beta:=beta) f := by
    have h := Fopp_correct (beta:=beta) f
    simpa only [wp, PostCond.noThrow, pure, Fopp_correct_check, Id.run,
      ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h True.intro
  have hopp {z : ℝ} {f : FloatSpec.Core.Defs.FlocqFloat beta}
      (hf : Closest (beta:=beta) bo (beta : ℝ) z f) :
      Closest (beta:=beta) bo (beta : ℝ) (-z) (Fopp (beta:=beta) f) := by
    have h := ClosestOpp (beta:=beta) bo (beta : ℝ) f z
    simpa only [wp, PostCond.noThrow, pure, ClosestOpp_check, Id.run,
      ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h hf
  have hD2 : Closest (beta:=beta) bo (beta : ℝ)
      (_root_.F2R (beta:=beta) fr - _root_.F2R (beta:=beta) fx1y1) nt1 := by
    convert hopp hft1.2.1 using 1 <;>
      simp [nt1, r, x1y1, hfr.2.2, hfx1y1.2.2] <;> ring
  have hD3 : Closest (beta:=beta) bo (beta : ℝ)
      (_root_.F2R (beta:=beta) nt1 - _root_.F2R (beta:=beta) fx1y2) nt2 := by
    convert hopp hft2.2.1 using 1 <;>
      simp [nt1, nt2, t1, x1y2, hnval, hft1.2.2, hfx1y2.2.2] <;> ring
  have hD4 : Closest (beta:=beta) bo (beta : ℝ)
      (_root_.F2R (beta:=beta) nt2 - _root_.F2R (beta:=beta) fx2y1) nt3 := by
    convert hopp hft3.2.1 using 1 <;>
      simp [nt2, nt3, t2, x2y1, hnval, hft2.2.2, hfx2y1.2.2] <;> ring
  have hD5 : Closest (beta:=beta) bo (beta : ℝ)
      (_root_.F2R (beta:=beta) nt3 - _root_.F2R (beta:=beta) fx2y2) nt4 := by
    convert hopp hft4.2.1 using 1 <;>
      simp [nt3, nt4, t3, x2y2, hnval, hft3.2.2, hfx2y2.2.2] <;> ring
  have hfxBound := (FcanonicBound (beta:=beta) beta bo fx) hfxCan
  have hfyBound := (FcanonicBound (beta:=beta) beta bo fy) hfyCan
  have hExact (hExp : -bo.dExp ≤ fx.Fexp + fy.Fexp) : x * y = r + t4 := by
    have h := Dekker1 bo beta prec.toNat fx fy fpx fqx fhx ftx fpy fqy fhy fty
      fx1y1 fx1y2 fx2y1 fx2y2 fr nt1 nt2 nt3 nt4 rfl hβ hvNum hprecisionNat
      hfxCan hfyCan hExp
      (by simpa [hfxVal, hsNat, FloatSpec.Core.Raux.bpow] using hfpx.2.1)
      (by simpa [hfxVal, hfpx.2.2] using hfqx.2.1)
      (by simpa [hfqx.2.2, hfpx.2.2] using hfhx.2.1)
      (by simpa [hfxVal, hfhx.2.2] using hftx.2.1)
      (by simpa [hfyVal, hsNat, FloatSpec.Core.Raux.bpow] using hfpy.2.1)
      (by simpa [hfyVal, hfpy.2.2] using hfqy.2.1)
      (by simpa [hfqy.2.2, hfpy.2.2] using hfhy.2.1)
      (by simpa [hfyVal, hfhy.2.2] using hfty.2.1)
      (by simpa [hfhx.2.2, hfhy.2.2] using hfx1y1.2.1)
      (by simpa [hfhx.2.2, hfty.2.2] using hfx1y2.2.1)
      (by simpa [hftx.2.2, hfhy.2.2] using hfx2y1.2.1)
      (by simpa [hftx.2.2, hfty.2.2] using hfx2y2.2.1)
      (by simpa [hfxVal, hfyVal] using hfr.2.1) hD2 hD3 hD4 hD5 hdExpPos hBranchNat
    simpa [hfxVal, hfyVal, hfr.2.2, nt4, hnval, hft4.2.2] using h
  constructor
  · intro hUnder
    rcases hUnder with hzero | hlower
    · exact False.elim ((mul_ne_zero hx0 hy0) hzero)
    · apply hExact
      have h := underf_mult_aux' (beta:=beta) bo prec fx fy
      simpa only [wp, PostCond.noThrow, pure, underf_mult_aux'_check, Id.run, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h
        ⟨hβ, by omega, by simpa [bo, pGivesBound] using hpBound, hfxBound, hfyBound,
          by simpa [hboExp, hfxVal, hfyVal] using hlower⟩
  · by_cases hExp : -bo.dExp ≤ fx.Fexp + fy.Fexp
    · have hz : x * y - (r + t4) = 0 := sub_eq_zero.mpr (hExact hExp)
      change |x * y - (r + t4)| ≤ _
      rw [hz, abs_zero]
      exact mul_nonneg (by norm_num) (le_of_lt (by
        simpa [FloatSpec.Core.Raux.bpow] using
          zpow_pos (show (0 : ℝ) < beta by exact_mod_cast (by omega : (0 : Int) < beta)) emin))
    · have h := Dekker2 bo beta prec.toNat fx fy fpx fqx fhx ftx fpy fqy fhy fty
        fx1y1 fx1y2 fx2y1 fx2y2 fr nt1 nt2 nt3 nt4 rfl hβ hvNum hprecisionNat
        hfxCan hfyCan
        (by simpa [hfxVal, hsNat, FloatSpec.Core.Raux.bpow] using hfpx.2.1)
        (by simpa [hfxVal, hfpx.2.2] using hfqx.2.1)
        (by simpa [hfqx.2.2, hfpx.2.2] using hfhx.2.1)
        (by simpa [hfxVal, hfhx.2.2] using hftx.2.1)
        (by simpa [hfyVal, hsNat, FloatSpec.Core.Raux.bpow] using hfpy.2.1)
        (by simpa [hfyVal, hfpy.2.2] using hfqy.2.1)
        (by simpa [hfqy.2.2, hfpy.2.2] using hfhy.2.1)
        (by simpa [hfyVal, hfhy.2.2] using hfty.2.1)
        (by simpa [hfhx.2.2, hfhy.2.2] using hfx1y1.2.1)
        (by simpa [hfhx.2.2, hfty.2.2] using hfx1y2.2.1)
        (by simpa [hftx.2.2, hfhy.2.2] using hfx2y1.2.1)
        (by simpa [hftx.2.2, hfty.2.2] using hfx2y2.2.1)
        (by simpa [hfxVal, hfyVal] using hfr.2.1) hD2 hD3 hD4 hD5 hBranchNat
      change |x * y - (r + t4)| ≤
        (7 / 2 : ℝ) * FloatSpec.Core.Raux.bpow beta emin
      simpa [hfxVal, hfyVal, hfr.2.2, nt4, hnval,
        hft4.2.2, hboExp, FloatSpec.Core.Raux.bpow] using h

-- (reserved) ErrFMA_bounded will be added next after validating preceding lemmas

-- Coq: `ErrFMA_bounded` — formats of r1, r2, r3 in compensated FMA scheme
noncomputable def ErrFMA_bounded_check (emin prec : Int)
    (choice : Int → Bool) (a x y : ℝ) : Unit :=
  ()

/-- Audit gap for Coq `ErrFMA_bounded`; the former theorem had postcondition
`True` and proved no boundedness property. -/
theorem ErrFMA_bounded (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hβ : 1 < beta)
    (Fa : generic_format beta (FLT_exp emin prec) a)
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (V1_Und1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |a * x|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
    let alpha2 := (y + u2) - alpha1
    let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
    let beta2 := (u1 + alpha1) - beta1
    let gamma := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
      (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
    let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (gamma + alpha2)
    let r3 := (gamma + alpha2) - r2
    generic_format beta (FLT_exp emin prec) r1 ∧
      generic_format beta (FLT_exp emin prec) r2 ∧
      generic_format beta (FLT_exp emin prec) r3 := by
  classical
  haveI : FloatSpec.Core.Generic_fmt.Monotone_exp (FLT_exp emin prec) := by
    simpa [FLT_exp] using
      (inferInstance :
        FloatSpec.Core.Generic_fmt.Monotone_exp
          (FloatSpec.Core.FLT.FLT_exp prec emin))
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
  let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
  let alpha2 := (y + u2) - alpha1
  let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
  let beta2 := (u1 + alpha1) - beta1
  let gamma := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
    (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
  let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (gamma + alpha2)
  change generic_format beta (FLT_exp emin prec) r1 ∧
    generic_format beta (FLT_exp emin prec) r2 ∧
    generic_format beta (FLT_exp emin prec) (gamma + alpha2 - r2)
  constructor
  · exact FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := beta) (fexp := FLT_exp emin prec)
      (rnd := rnd) (x := a * x + y) hβ
  constructor
  · exact FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := beta) (fexp := FLT_exp emin prec)
      (rnd := rnd) (x := gamma + alpha2) hβ
  ·
    have hu2_fmt : generic_format beta (FLT_exp emin prec) u2 := by
      have hprod_err :
          generic_format beta (FLT_exp emin prec)
            (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) -
              a * x) := by
        exact mult_error_FLT (beta := beta) (prec := prec)
          (rnd := rnd) (emin := emin) (x := a) (y := x)
          hβ Fa Fx (by
            intro hprod_ne
            rcases V1_Und1 with hzero | hbound
            · exact False.elim (hprod_ne hzero)
            · exact hbound)
      have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
        (beta := beta) (fexp := FLT_exp emin prec)
        (x := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) -
          a * x)
      simp only [wp, PostCond.noThrow, PredTrans.pure, Id.run, pure, Bind.bind] at hopp
      have hneg_fmt := hopp hprod_err
      have hu2_eq :
          u2 =
            -(FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) -
              a * x) := by
        dsimp [u2]
        ring
      simpa [hu2_eq] using hneg_fmt
    have halpha1_fmt : generic_format beta (FLT_exp emin prec) alpha1 := by
      exact FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := beta) (fexp := FLT_exp emin prec)
        (rnd := rnd) (x := y + u2) hβ
    have halpha2_fmt : generic_format beta (FLT_exp emin prec) alpha2 := by
      have hadd_err :
          generic_format beta (FLT_exp emin prec)
            (FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice)
              (y + u2) - (y + u2)) :=
        plus_error (beta := beta) (fexp := FLT_exp emin prec)
          (choice := choice) (x := y) (y := u2) hβ Fy hu2_fmt
      have hadd_err_core :
          generic_format beta (FLT_exp emin prec)
            (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
              (y + u2) - (y + u2)) := by
        simpa [FloatSpec.Calc.Round.round, Znearest,
          FloatSpec.Compat.Scaffold.ZnearestMode, rnd] using hadd_err
      have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
        (beta := beta) (fexp := FLT_exp emin prec)
        (x :=
          FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
            (y + u2) - (y + u2))
      simp only [wp, PostCond.noThrow, PredTrans.pure, Id.run, pure, Bind.bind] at hopp
      have hneg_fmt := hopp hadd_err_core
      have halpha2_eq :
          alpha2 =
            -(FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
              (y + u2) - (y + u2)) := by
        dsimp [alpha2]
        ring
      simpa [halpha2_eq] using hneg_fmt
    have hgamma_fmt : generic_format beta (FLT_exp emin prec) gamma := by
      exact FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := beta) (fexp := FLT_exp emin prec)
        (rnd := rnd)
        (x := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
            (beta1 - r1) + beta2) hβ
    have hr3_err :
        generic_format beta (FLT_exp emin prec)
          (FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice)
            (gamma + alpha2) - (gamma + alpha2)) :=
      plus_error (beta := beta) (fexp := FLT_exp emin prec)
        (choice := choice) (x := gamma) (y := alpha2) hβ hgamma_fmt halpha2_fmt
    have hr3_err_core :
        generic_format beta (FLT_exp emin prec)
          (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
            (gamma + alpha2) - (gamma + alpha2)) := by
      simpa [FloatSpec.Calc.Round.round, Znearest,
        FloatSpec.Compat.Scaffold.ZnearestMode, rnd] using hr3_err
    have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := FLT_exp emin prec)
      (x :=
        FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
          (gamma + alpha2) - (gamma + alpha2))
    simp only [wp, PostCond.noThrow, PredTrans.pure, Id.run, pure, Bind.bind] at hopp
    have hneg_fmt := hopp hr3_err_core
    have hr3_eq :
        gamma + alpha2 - r2 =
          -(FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
            (gamma + alpha2) - (gamma + alpha2)) := by
      dsimp [r2]
      ring
    simpa [hr3_eq] using hneg_fmt

-- Coq: `ErrFMA_correct` — r1 + r2 + r3 = a*x + y
noncomputable def ErrFMA_correct_check (emin prec : Int)
    (choice : Int → Bool) (a x y : ℝ) : Unit :=
  ()

/-- Zero-product branch of Coq `ErrFMA_correct`.

When the product input is exactly zero, the compensated FMA reconstruction
collapses by `round(0)=0` and `round(y)=y` for formatted `y`.  The nonzero
branch still requires the lower Pff `FmaErr` reconstruction theorem. -/
theorem ErrFMA_correct_of_product_eq_zero (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hβ : 1 < beta)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (hprod : a * x = 0) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
    let alpha2 := (y + u2) - alpha1
    let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
    let beta2 := (u1 + alpha1) - beta1
    let gamma := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
      (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
    let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (gamma + alpha2)
    let r3 := (gamma + alpha2) - r2
    a * x + y = r1 + r2 + r3 := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  have hround0 :
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd 0 = 0 := by
    have hrnd0 : rnd (0 : ℝ) = (0 : Int) := by
      simpa [rnd] using
        (FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) (0 : Int))
    simp [FloatSpec.Core.Generic_fmt.roundR,
      FloatSpec.Core.Generic_fmt.scaled_mantissa, hrnd0]
  have hround_y :
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd y = y :=
    FloatSpec.Core.Generic_fmt.roundR_generic
      (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd)
      (x := y) hβ Fy
  dsimp
  simp [rnd, hprod, hround0, hround_y]

/-- Final algebraic wrapper step of Coq `ErrFMA_correct`.

The lower Pff `FmaErr` payload reconstructs the exact value as
`r1 + gamma + alpha2`.  The public theorem returns `r1 + r2 + r3`, where
`r3 = gamma + alpha2 - r2`; this helper packages that last let-bound
algebraic rewrite. -/
theorem ErrFMA_correct_from_core_equality
    (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hcore :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
      let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
      let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
      let u2 := a * x - u1
      let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
      let alpha2 := (y + u2) - alpha1
      let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
      let beta2 := (u1 + alpha1) - beta1
      let gamma := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
        (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
      a * x + y = r1 + gamma + alpha2) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
    let alpha2 := (y + u2) - alpha1
    let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
    let beta2 := (u1 + alpha1) - beta1
    let gamma := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
      (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
    let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (gamma + alpha2)
    let r3 := (gamma + alpha2) - r2
    a * x + y = r1 + r2 + r3 := by
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
  let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
  let alpha2 := (y + u2) - alpha1
  let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
  let beta2 := (u1 + alpha1) - beta1
  let gamma := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
    (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
  let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (gamma + alpha2)
  let r3 := (gamma + alpha2) - r2
  change a * x + y = r1 + r2 + r3
  have hcore' : a * x + y = r1 + gamma + alpha2 := by
    simpa [rnd, r1, u1, u2, alpha1, alpha2, beta1, beta2, gamma] using hcore
  rw [hcore']
  change r1 + gamma + alpha2 = r1 + r2 + r3
  dsimp [r3]
  ring

/-- Real-value alignment between the public Flocq ErrFMA wrapper variables and
the lower Pff float witnesses consumed by `FmaErr`. -/
def ErrFMA_real_values (emin prec : Int) (choice : Int → Bool)
    (a x y : ℝ)
    (fa fx fy fr1 fu1 fu2 fal1 fal2 fbe1 fbe2 fga :
      FloatSpec.Core.Defs.FlocqFloat 2) : Prop :=
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let r1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x + y)
  let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let alpha1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (y + u2)
  let alpha2 := (y + u2) - alpha1
  let beta1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (u1 + alpha1)
  let beta2 := (u1 + alpha1) - beta1
  let gamma := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
    (FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
  _root_.F2R (beta:=2) fa = a ∧
    _root_.F2R (beta:=2) fx = x ∧
    _root_.F2R (beta:=2) fy = y ∧
    _root_.F2R (beta:=2) fr1 = r1 ∧
    _root_.F2R (beta:=2) fu1 = u1 ∧
    _root_.F2R (beta:=2) fu2 = u2 ∧
    _root_.F2R (beta:=2) fal1 = alpha1 ∧
    _root_.F2R (beta:=2) fal2 = alpha2 ∧
    _root_.F2R (beta:=2) fbe1 = beta1 ∧
    _root_.F2R (beta:=2) fbe2 = beta2 ∧
    _root_.F2R (beta:=2) fga = gamma

/-- Pff witnesses for the nearest-rounding steps in Coq `ErrFMA_correct`.

The public wrapper destructs `round_N_is_pff_round` for the rounded values
`r1`, `u1`, `alpha1`, `beta1`, `gat`, and `gamma`.  This helper packages those
six witnesses with their closestness and real-value equations. -/
theorem ErrFMA_round_N_witnesses (emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hβ : 1 < (2 : Int))
    (hprec : precisionNotZero prec)
    (hemin : emin ≤ 0) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let bnd : Fbound := make_bound 2 prec emin
    let bo : Fbound_skel := toFboundSkel bnd
    let witness := fun (input rounded : ℝ)
        (f : FloatSpec.Core.Defs.FlocqFloat 2) =>
      Fcanonic (beta:=2) 2 bo f ∧
        Closest (beta:=2) bo (2 : ℝ) input f ∧
        _root_.F2R (beta:=2) f = rounded
    let r1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x + y)
    let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let alpha1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (y + u2)
    let alpha2 := (y + u2) - alpha1
    let beta1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (u1 + alpha1)
    let beta2 := (u1 + alpha1) - beta1
    let gat := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (beta1 - r1)
    let gamma := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (gat + beta2)
    ∃ fr1 fu1 fal1 fbe1 fgat fga : FloatSpec.Core.Defs.FlocqFloat 2,
      witness (a * x + y) r1 fr1 ∧
        witness (a * x) u1 fu1 ∧
        witness (y + u2) alpha1 fal1 ∧
        witness (u1 + alpha1) beta1 fbe1 ∧
        witness (beta1 - r1) gat fgat ∧
        witness (gat + beta2) gamma fga := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let bnd : Fbound := make_bound 2 prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  let r1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x + y)
  let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let alpha1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (y + u2)
  let alpha2 := (y + u2) - alpha1
  let beta1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (u1 + alpha1)
  let beta2 := (u1 + alpha1) - beta1
  let gat := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (beta1 - r1)
  let gamma := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (gat + beta2)
  have hpBound : pGivesBound 2 bnd prec := by
    have h := make_bound_p 2 prec emin (hp := by exact hprec)
    have hv : (make_bound 2 prec emin).vNum =
        Zpower_nat 2 (prec.natAbs) := by
      simpa [wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound, bnd] using hv
  have hbnd_dExp : -bnd.dExp = emin := by
    have h := make_bound_Emin 2 prec emin (hp := by exact hprec)
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using
        h hemin
    omega
  rcases (round_N_is_pff_round (beta := 2) (b := bnd) (p := prec)
      (choice := choice) (r := a * x + y)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨fr1, hfr1_can, hfr1_closest, hfr1_val⟩
  rcases (round_N_is_pff_round (beta := 2) (b := bnd) (p := prec)
      (choice := choice) (r := a * x)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨fu1, hfu1_can, hfu1_closest, hfu1_val⟩
  rcases (round_N_is_pff_round (beta := 2) (b := bnd) (p := prec)
      (choice := choice) (r := y + u2)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨fal1, hfal1_can, hfal1_closest, hfal1_val⟩
  rcases (round_N_is_pff_round (beta := 2) (b := bnd) (p := prec)
      (choice := choice) (r := u1 + alpha1)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨fbe1, hfbe1_can, hfbe1_closest, hfbe1_val⟩
  rcases (round_N_is_pff_round (beta := 2) (b := bnd) (p := prec)
      (choice := choice) (r := beta1 - r1)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨fgat, hfgat_can, hfgat_closest, hfgat_val⟩
  rcases (round_N_is_pff_round (beta := 2) (b := bnd) (p := prec)
      (choice := choice) (r := gat + beta2)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨fga, hfga_can, hfga_closest, hfga_val⟩
  refine ⟨fr1, fu1, fal1, fbe1, fgat, fga, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hfr1_can, hfr1_closest, by simpa [r1, rnd, hbnd_dExp] using hfr1_val⟩
  · exact ⟨hfu1_can, hfu1_closest, by simpa [u1, rnd, hbnd_dExp] using hfu1_val⟩
  · exact ⟨hfal1_can, hfal1_closest, by simpa [alpha1, rnd, hbnd_dExp] using hfal1_val⟩
  · exact ⟨hfbe1_can, hfbe1_closest, by simpa [beta1, rnd, hbnd_dExp] using hfbe1_val⟩
  · exact ⟨hfgat_can, hfgat_closest, by simpa [gat, rnd, hbnd_dExp] using hfgat_val⟩
  · exact ⟨hfga_can, hfga_closest, by simpa [gamma, rnd, hbnd_dExp] using hfga_val⟩

/-- Formatted exact error values in Coq `ErrFMA_correct`.

The public FMA wrapper needs Pff-side witnesses for the unrounded compensation
errors `u2`, `alpha2`, and `beta2` before calling the lower `FmaErr` payload.
This helper ports the generic-format part of those witness constructions. -/
theorem ErrFMA_error_value_formats (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hβ : 1 < beta)
    (Fa : generic_format beta (FLT_exp emin prec) a)
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (Und1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |a * x|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
    let alpha2 := (y + u2) - alpha1
    let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
    let beta2 := (u1 + alpha1) - beta1
    generic_format beta (FLT_exp emin prec) u2 ∧
      generic_format beta (FLT_exp emin prec) alpha2 ∧
      generic_format beta (FLT_exp emin prec) beta2 := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
  let alpha2 := (y + u2) - alpha1
  let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
  let beta2 := (u1 + alpha1) - beta1
  haveI : FloatSpec.Core.Generic_fmt.Monotone_exp (FLT_exp emin prec) := by
    simpa [FLT_exp] using
      (inferInstance :
        FloatSpec.Core.Generic_fmt.Monotone_exp
          (FloatSpec.Core.FLT.FLT_exp prec emin))
  have hu2_fmt : generic_format beta (FLT_exp emin prec) u2 := by
    have hprod_err :
        generic_format beta (FLT_exp emin prec)
          (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) -
            a * x) := by
      exact mult_error_FLT (beta := beta) (prec := prec)
        (rnd := rnd) (emin := emin) (x := a) (y := x)
        hβ Fa Fx (by
          intro hprod_ne
          rcases Und1 with hzero | hbound
          · exact False.elim (hprod_ne hzero)
          · exact hbound)
    have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := FLT_exp emin prec)
      (x := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) -
        a * x)
    simp only [wp, PostCond.noThrow, PredTrans.pure, Id.run, pure, Bind.bind] at hopp
    have hneg_fmt := hopp hprod_err
    have hu2_eq :
        u2 =
          -(FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) -
            a * x) := by
      dsimp [u2, u1]
      ring
    simpa [hu2_eq] using hneg_fmt
  have hu1_fmt : generic_format beta (FLT_exp emin prec) u1 := by
    exact FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := beta) (fexp := FLT_exp emin prec)
      (rnd := rnd) (x := a * x) hβ
  have halpha1_fmt : generic_format beta (FLT_exp emin prec) alpha1 := by
    exact FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := beta) (fexp := FLT_exp emin prec)
      (rnd := rnd) (x := y + u2) hβ
  have halpha2_fmt : generic_format beta (FLT_exp emin prec) alpha2 := by
    have hadd_err :
        generic_format beta (FLT_exp emin prec)
          (FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice)
            (y + u2) - (y + u2)) :=
      plus_error (beta := beta) (fexp := FLT_exp emin prec)
        (choice := choice) (x := y) (y := u2) hβ Fy hu2_fmt
    have hadd_err_core :
        generic_format beta (FLT_exp emin prec)
          (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
            (y + u2) - (y + u2)) := by
      simpa [FloatSpec.Calc.Round.round, FloatSpec.Compat.Scaffold.ZnearestMode,
        Znearest, rnd] using hadd_err
    have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := FLT_exp emin prec)
      (x := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
        (y + u2) - (y + u2))
    simp only [wp, PostCond.noThrow, PredTrans.pure, Id.run, pure, Bind.bind] at hopp
    have hneg_fmt := hopp hadd_err_core
    have halpha2_eq :
        alpha2 =
          -(FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
            (y + u2) - (y + u2)) := by
      dsimp [alpha2, alpha1]
      ring
    simpa [halpha2_eq] using hneg_fmt
  have hbeta2_fmt : generic_format beta (FLT_exp emin prec) beta2 := by
    have hadd_err :
        generic_format beta (FLT_exp emin prec)
          (FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice)
            (u1 + alpha1) - (u1 + alpha1)) :=
      plus_error (beta := beta) (fexp := FLT_exp emin prec)
        (choice := choice) (x := u1) (y := alpha1) hβ hu1_fmt halpha1_fmt
    have hadd_err_core :
        generic_format beta (FLT_exp emin prec)
          (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
            (u1 + alpha1) - (u1 + alpha1)) := by
      simpa [FloatSpec.Calc.Round.round, FloatSpec.Compat.Scaffold.ZnearestMode,
        Znearest, rnd] using hadd_err
    have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := FLT_exp emin prec)
      (x := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
        (u1 + alpha1) - (u1 + alpha1))
    simp only [wp, PostCond.noThrow, PredTrans.pure, Id.run, pure, Bind.bind] at hopp
    have hneg_fmt := hopp hadd_err_core
    have hbeta2_eq :
        beta2 =
          -(FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
            (u1 + alpha1) - (u1 + alpha1)) := by
      dsimp [beta2, beta1]
      ring
    simpa [hbeta2_eq] using hneg_fmt
  exact ⟨hu2_fmt, halpha2_fmt, hbeta2_fmt⟩

/-- Bounded Pff-side witnesses for the exact error values in `ErrFMA_correct`.

This is the wrapper-side analogue of `ErrFmaAppr_format_witnesses`, but for the
exact FMA reconstruction path.  It converts the formatted inputs and the three
unrounded compensation errors into bounded Pff floats with matching real
values. -/
theorem ErrFMA_error_value_witnesses (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hβ : 1 < beta)
    (hprec : precisionNotZero prec)
    (hemin : emin ≤ 0)
    (Fa : generic_format beta (FLT_exp emin prec) a)
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (Und1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |a * x|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let bnd : Fbound := make_bound beta prec emin
    let bo : Fbound_skel := toFboundSkel bnd
    let witness := fun (value : ℝ) (f : FloatSpec.Core.Defs.FlocqFloat beta) =>
      _root_.F2R (beta:=beta) f = value ∧ Fbounded (beta:=beta) bo f
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
    let alpha2 := (y + u2) - alpha1
    let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
    let beta2 := (u1 + alpha1) - beta1
    ∃ fa fx fy fu2 falpha2 fbeta2 : FloatSpec.Core.Defs.FlocqFloat beta,
      witness a fa ∧ witness x fx ∧ witness y fy ∧
        witness u2 fu2 ∧ witness alpha2 falpha2 ∧ witness beta2 fbeta2 := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let bnd : Fbound := make_bound beta prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
  let alpha2 := (y + u2) - alpha1
  let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
  let beta2 := (u1 + alpha1) - beta1
  have hpBound : pGivesBound beta bnd prec := by
    have h := make_bound_p beta prec emin (hp := by exact hprec)
    have hv : (make_bound beta prec emin).vNum =
        Zpower_nat beta (prec.natAbs) := by
      simpa [wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound, bnd] using hv
  have hbnd_dExp : -bnd.dExp = emin := by
    have h := make_bound_Emin beta prec emin (hp := by exact hprec)
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using
        h hemin
    omega
  have herror_fmt :
      generic_format beta (FLT_exp emin prec) u2 ∧
        generic_format beta (FLT_exp emin prec) alpha2 ∧
        generic_format beta (FLT_exp emin prec) beta2 := by
    simpa [rnd, u1, u2, alpha1, alpha2, beta1, beta2] using
      ErrFMA_error_value_formats (beta := beta) (emin := emin) (prec := prec)
        (choice := choice) (a := a) (x := x) (y := y)
        hβ Fa Fx Fy Und1
  have Fa_bnd : generic_format beta (FLT_exp (-bnd.dExp) prec) a := by
    simpa [hbnd_dExp] using Fa
  have Fx_bnd : generic_format beta (FLT_exp (-bnd.dExp) prec) x := by
    simpa [hbnd_dExp] using Fx
  have Fy_bnd : generic_format beta (FLT_exp (-bnd.dExp) prec) y := by
    simpa [hbnd_dExp] using Fy
  have Fu2_bnd : generic_format beta (FLT_exp (-bnd.dExp) prec) u2 := by
    simpa [hbnd_dExp] using herror_fmt.1
  have Falpha2_bnd : generic_format beta (FLT_exp (-bnd.dExp) prec) alpha2 := by
    simpa [hbnd_dExp] using herror_fmt.2.1
  have Fbeta2_bnd : generic_format beta (FLT_exp (-bnd.dExp) prec) beta2 := by
    simpa [hbnd_dExp] using herror_fmt.2.2
  rcases (by
      have h := format_is_flocq_bounded beta bnd prec a
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨Fa_bnd, hpBound, hprec, hβ⟩) with
    ⟨fa, hfa_val, hfa_bound⟩
  rcases (by
      have h := format_is_flocq_bounded beta bnd prec x
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨Fx_bnd, hpBound, hprec, hβ⟩) with
    ⟨fx, hfx_val, hfx_bound⟩
  rcases (by
      have h := format_is_flocq_bounded beta bnd prec y
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨Fy_bnd, hpBound, hprec, hβ⟩) with
    ⟨fy, hfy_val, hfy_bound⟩
  rcases (by
      have h := format_is_flocq_bounded beta bnd prec u2
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨Fu2_bnd, hpBound, hprec, hβ⟩) with
    ⟨fu2, hfu2_val, hfu2_bound⟩
  rcases (by
      have h := format_is_flocq_bounded beta bnd prec alpha2
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨Falpha2_bnd, hpBound, hprec, hβ⟩) with
    ⟨falpha2, hfalpha2_val, hfalpha2_bound⟩
  rcases (by
      have h := format_is_flocq_bounded beta bnd prec beta2
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨Fbeta2_bnd, hpBound, hprec, hβ⟩) with
    ⟨fbeta2, hfbeta2_val, hfbeta2_bound⟩
  exact ⟨fa, fx, fy, fu2, falpha2, fbeta2,
    ⟨hfa_val, hfa_bound⟩,
    ⟨hfx_val, hfx_bound⟩,
    ⟨hfy_val, hfy_bound⟩,
    ⟨hfu2_val, hfu2_bound⟩,
    ⟨hfalpha2_val, hfalpha2_bound⟩,
    ⟨hfbeta2_val, hfbeta2_bound⟩⟩

/-- Wrapper-side value and closestness package for `ErrFMA_correct`.

This combines the formatted exact-error witnesses with the six nearest-rounding
witnesses.  The resulting facts match the real-value and closestness premises
of `ErrFMA_correct_from_FmaErr_payload`; the remaining public-wrapper work is
the separate `fdiff`/`fcorr` correction split. -/
theorem ErrFMA_value_and_round_witnesses
    (emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hβ : 1 < (2 : Int))
    (hprec : precisionNotZero prec)
    (hemin : emin ≤ 0)
    (Fa : generic_format 2 (FLT_exp emin prec) a)
    (Fx : generic_format 2 (FLT_exp emin prec) x)
    (Fy : generic_format 2 (FLT_exp emin prec) y)
    (Und1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow 2 (emin + 2 * prec - 1) ≤ |a * x|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let bnd : Fbound := make_bound 2 prec emin
    let bo : Fbound_skel := toFboundSkel bnd
    let r1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x + y)
    let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let alpha1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (y + u2)
    let alpha2 := (y + u2) - alpha1
    let beta1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (u1 + alpha1)
    let beta2 := (u1 + alpha1) - beta1
    let gat := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (beta1 - r1)
    let gamma := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (gat + beta2)
    ∃ fa fx fy fr1 fu1 fu2 fal1 fal2 fbe1 fbe2 fgat fga :
        FloatSpec.Core.Defs.FlocqFloat 2,
      ErrFMA_real_values emin prec choice a x y
        fa fx fy fr1 fu1 fu2 fal1 fal2 fbe1 fbe2 fga ∧
      Fbounded (beta:=2) bo fa ∧
      Fbounded (beta:=2) bo fx ∧
      Fbounded (beta:=2) bo fy ∧
      Fbounded (beta:=2) bo fu2 ∧
      Fbounded (beta:=2) bo fal2 ∧
      Fbounded (beta:=2) bo fbe2 ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fx) fu1 ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fy + _root_.F2R (beta:=2) fu2) fal1 ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fx +
          _root_.F2R (beta:=2) fy) fr1 ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fu1 + _root_.F2R (beta:=2) fal1) fbe1 ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fbe1 - _root_.F2R (beta:=2) fr1) fgat ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fgat + _root_.F2R (beta:=2) fbe2) fga := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let bnd : Fbound := make_bound 2 prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  let r1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x + y)
  let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let alpha1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (y + u2)
  let alpha2 := (y + u2) - alpha1
  let beta1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (u1 + alpha1)
  let beta2 := (u1 + alpha1) - beta1
  let gat := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (beta1 - r1)
  let gamma := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (gat + beta2)
  rcases (ErrFMA_error_value_witnesses (beta := 2) (emin := emin) (prec := prec)
      (choice := choice) (a := a) (x := x) (y := y)
      hβ hprec hemin Fa Fx Fy Und1) with
    ⟨fa, fx, fy, fu2, fal2, fbe2, hfa, hfx, hfy, hfu2, hfal2, hfbe2⟩
  rcases hfa with ⟨hfa_val, hfa_bound⟩
  rcases hfx with ⟨hfx_val, hfx_bound⟩
  rcases hfy with ⟨hfy_val, hfy_bound⟩
  rcases hfu2 with ⟨hfu2_val, hfu2_bound⟩
  rcases hfal2 with ⟨hfal2_val, hfal2_bound⟩
  rcases hfbe2 with ⟨hfbe2_val, hfbe2_bound⟩
  rcases (ErrFMA_round_N_witnesses (emin := emin) (prec := prec)
      (choice := choice) (a := a) (x := x) (y := y)
      hβ hprec hemin) with
    ⟨fr1, fu1, fal1, fbe1, fgat, fga,
      hfr1, hfu1, hfal1, hfbe1, hfgat, hfga⟩
  rcases hfr1 with ⟨_, hfr1_closest, hfr1_val⟩
  rcases hfu1 with ⟨_, hfu1_closest, hfu1_val⟩
  rcases hfal1 with ⟨_, hfal1_closest, hfal1_val⟩
  rcases hfbe1 with ⟨_, hfbe1_closest, hfbe1_val⟩
  rcases hfgat with ⟨_, hfgat_closest, hfgat_val⟩
  rcases hfga with ⟨_, hfga_closest, hfga_val⟩
  have hvals :
      ErrFMA_real_values emin prec choice a x y
        fa fx fy fr1 fu1 fu2 fal1 fal2 fbe1 fbe2 fga := by
    simp only [ErrFMA_real_values, rnd, r1, u1, u2, alpha1, alpha2, beta1,
      beta2, gamma, hfa_val, hfx_val, hfy_val, hfr1_val, hfu1_val, hfu2_val,
      hfal1_val, hfal2_val, hfbe1_val, hfbe2_val, hfga_val, and_self]
  refine ⟨fa, fx, fy, fr1, fu1, fu2, fal1, fal2, fbe1, fbe2, fgat, fga,
    hvals, hfa_bound, hfx_bound, hfy_bound, hfu2_bound, hfal2_bound,
    hfbe2_bound, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hfa_val, hfx_val, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hfu1_closest
  · simpa [hfy_val, hfu2_val] using hfal1_closest
  · simpa [hfa_val, hfx_val, hfy_val] using hfr1_closest
  · simpa [hfu1_val, hfal1_val] using hfbe1_closest
  · simpa [hfbe1_val, hfr1_val] using hfgat_closest
  · simpa [hfgat_val, hfbe2_val] using hfga_closest

/-- Correction witnesses for the `alpha2 = 0` branch of `ErrFMA_correct`.

When the second exact compensation error is zero, the rounded `be1` and `r1`
have the same real input.  Therefore the exact-difference witness can be the
bounded zero float, and the correction witness can be `be2` itself. -/
theorem ErrFMA_correction_witnesses_of_alpha2_zero
    (emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hβ : 1 < (2 : Int))
    (hprec : precisionNotZero prec)
    (hemin : emin ≤ 0)
    (Fa : generic_format 2 (FLT_exp emin prec) a)
    (Fx : generic_format 2 (FLT_exp emin prec) x)
    (Fy : generic_format 2 (FLT_exp emin prec) y)
    (Und1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow 2 (emin + 2 * prec - 1) ≤ |a * x|)
    (halpha2_zero :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
      let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
      let u2 := a * x - u1
      let alpha1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (y + u2)
      let alpha2 := (y + u2) - alpha1
      alpha2 = 0) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let bnd : Fbound := make_bound 2 prec emin
    let bo : Fbound_skel := toFboundSkel bnd
    ∃ fa fx fy fr1 fu1 fu2 fal1 fal2 fbe1 fbe2 fdiff fgat fcorr fga :
        FloatSpec.Core.Defs.FlocqFloat 2,
      ErrFMA_real_values emin prec choice a x y
        fa fx fy fr1 fu1 fu2 fal1 fal2 fbe1 fbe2 fga ∧
      Fbounded (beta:=2) bo fa ∧
      Fbounded (beta:=2) bo fx ∧
      Fbounded (beta:=2) bo fy ∧
      Fbounded (beta:=2) bo fdiff ∧
      _root_.F2R (beta:=2) fdiff =
        _root_.F2R (beta:=2) fbe1 - _root_.F2R (beta:=2) fr1 ∧
      _root_.F2R (beta:=2) fu2 =
        _root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fx -
          _root_.F2R (beta:=2) fu1 ∧
      _root_.F2R (beta:=2) fal2 =
        _root_.F2R (beta:=2) fy + _root_.F2R (beta:=2) fu2 -
          _root_.F2R (beta:=2) fal1 ∧
      _root_.F2R (beta:=2) fbe2 =
        _root_.F2R (beta:=2) fu1 + _root_.F2R (beta:=2) fal1 -
          _root_.F2R (beta:=2) fbe1 ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fx) fu1 ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fy + _root_.F2R (beta:=2) fu2) fal1 ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fx +
          _root_.F2R (beta:=2) fy) fr1 ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fu1 + _root_.F2R (beta:=2) fal1) fbe1 ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fbe1 - _root_.F2R (beta:=2) fr1) fgat ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fgat + _root_.F2R (beta:=2) fbe2) fga ∧
      (_root_.F2R (beta:=2) fbe2 = 0 ∨
        (Fbounded (beta:=2) bo fcorr ∧
          _root_.F2R (beta:=2) fcorr =
            _root_.F2R (beta:=2) fgat + _root_.F2R (beta:=2) fbe2)) := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let bnd : Fbound := make_bound 2 prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  let r1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x + y)
  let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let alpha1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (y + u2)
  let alpha2 := (y + u2) - alpha1
  let beta1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (u1 + alpha1)
  let beta2 := (u1 + alpha1) - beta1
  let gat := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (beta1 - r1)
  let gamma := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (gat + beta2)
  rcases (ErrFMA_error_value_witnesses (beta := 2) (emin := emin) (prec := prec)
      (choice := choice) (a := a) (x := x) (y := y)
      hβ hprec hemin Fa Fx Fy Und1) with
    ⟨fa, fx, fy, fu2, fal2, fbe2, hfa, hfx, hfy, hfu2, hfal2, hfbe2⟩
  rcases hfa with ⟨hfa_val, hfa_bound⟩
  rcases hfx with ⟨hfx_val, hfx_bound⟩
  rcases hfy with ⟨hfy_val, hfy_bound⟩
  rcases hfu2 with ⟨hfu2_val, _hfu2_bound⟩
  rcases hfal2 with ⟨hfal2_val, _hfal2_bound⟩
  rcases hfbe2 with ⟨hfbe2_val, hfbe2_bound⟩
  rcases (ErrFMA_round_N_witnesses (emin := emin) (prec := prec)
      (choice := choice) (a := a) (x := x) (y := y)
      hβ hprec hemin) with
    ⟨fr1, fu1, fal1, fbe1, fgat, fga,
      hfr1, hfu1, hfal1, hfbe1, hfgat, hfga⟩
  rcases hfr1 with ⟨_, hfr1_closest, hfr1_val⟩
  rcases hfu1 with ⟨_, hfu1_closest, hfu1_val⟩
  rcases hfal1 with ⟨_, hfal1_closest, hfal1_val⟩
  rcases hfbe1 with ⟨_, hfbe1_closest, hfbe1_val⟩
  rcases hfgat with ⟨_, hfgat_closest, hfgat_val⟩
  rcases hfga with ⟨_, hfga_closest, hfga_val⟩
  let fdiff : FloatSpec.Core.Defs.FlocqFloat 2 := Fzero 2 (-bo.dExp)
  let fcorr : FloatSpec.Core.Defs.FlocqFloat 2 := fbe2
  have hvals :
      ErrFMA_real_values emin prec choice a x y
        fa fx fy fr1 fu1 fu2 fal1 fal2 fbe1 fbe2 fga := by
    simp only [ErrFMA_real_values, rnd, r1, u1, u2, alpha1, alpha2, beta1,
      beta2, gamma, hfa_val, hfx_val, hfy_val, hfr1_val, hfu1_val, hfu2_val,
      hfal1_val, hfal2_val, hfbe1_val, hfbe2_val, hfga_val, and_self]
  have halpha2_zero' : alpha2 = 0 := by
    simpa [rnd, u1, u2, alpha1, alpha2] using halpha2_zero
  have hinput_eq : u1 + alpha1 = a * x + y := by
    dsimp [alpha2, u2] at halpha2_zero'
    nlinarith
  have hbeta1_r1 : beta1 = r1 := by
    simp [beta1, r1, hinput_eq]
  have hbe1_fr1 :
      _root_.F2R (beta:=2) fbe1 = _root_.F2R (beta:=2) fr1 := by
    calc
      _root_.F2R (beta:=2) fbe1 = beta1 := by
        simpa [beta1] using hfbe1_val
      _ = r1 := hbeta1_r1
      _ = _root_.F2R (beta:=2) fr1 := by
        simpa [r1] using hfr1_val.symm
  have hfdiff_bound : Fbounded (beta:=2) bo fdiff := by
    have h := FboundedFzero (beta:=2) bo
    simpa [fdiff] using h True.intro
  have hfdiff_zero : _root_.F2R (beta:=2) fdiff = 0 := by
    simp [fdiff, Fzero, _root_.F2R, FloatSpec.Core.Defs.F2R]
  have hfdiff_val :
      _root_.F2R (beta:=2) fdiff =
        _root_.F2R (beta:=2) fbe1 - _root_.F2R (beta:=2) fr1 := by
    rw [hfdiff_zero, hbe1_fr1]
    ring
  have hgat_zero : gat = 0 := by
    have harg : beta1 - r1 = 0 := by
      rw [hbeta1_r1]
      ring
    have hround :
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (beta1 - r1) = 0 := by
      rw [harg]
      exact roundR_Znearest_zero emin prec choice
    simpa [gat] using hround
  have hfgat_zero : _root_.F2R (beta:=2) fgat = 0 := by
    calc
      _root_.F2R (beta:=2) fgat = gat := by
        simpa [gat] using hfgat_val
      _ = 0 := hgat_zero
  have hu2_payload :
      _root_.F2R (beta:=2) fu2 =
        _root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fx -
          _root_.F2R (beta:=2) fu1 := by
    rw [hfu2_val, hfa_val, hfx_val, hfu1_val]
  have hal2_payload :
      _root_.F2R (beta:=2) fal2 =
        _root_.F2R (beta:=2) fy + _root_.F2R (beta:=2) fu2 -
          _root_.F2R (beta:=2) fal1 := by
    rw [hfal2_val, hfy_val, hfu2_val, hfal1_val]
  have hbe2_payload :
      _root_.F2R (beta:=2) fbe2 =
        _root_.F2R (beta:=2) fu1 + _root_.F2R (beta:=2) fal1 -
          _root_.F2R (beta:=2) fbe1 := by
    rw [hfbe2_val, hfu1_val, hfal1_val, hfbe1_val]
  have hsplit :
      _root_.F2R (beta:=2) fbe2 = 0 ∨
        (Fbounded (beta:=2) bo fcorr ∧
          _root_.F2R (beta:=2) fcorr =
            _root_.F2R (beta:=2) fgat + _root_.F2R (beta:=2) fbe2) := by
    right
    refine ⟨by simpa [fcorr, bo, bnd] using hfbe2_bound, ?_⟩
    rw [hfgat_zero]
    simp [fcorr]
  refine ⟨fa, fx, fy, fr1, fu1, fu2, fal1, fal2, fbe1, fbe2, fdiff, fgat,
    fcorr, fga, hvals, hfa_bound, hfx_bound, hfy_bound, hfdiff_bound,
    hfdiff_val, hu2_payload, hal2_payload, hbe2_payload, ?_, ?_, ?_, ?_, ?_,
    ?_, hsplit⟩
  · simpa [hfa_val, hfx_val] using hfu1_closest
  · simpa [hfy_val, hfu2_val] using hfal1_closest
  · simpa [hfa_val, hfx_val, hfy_val] using hfr1_closest
  · simpa [hfu1_val, hfal1_val] using hfbe1_closest
  · simpa [hfbe1_val, hfr1_val] using hfgat_closest
  · simpa [hfgat_val, hfbe2_val] using hfga_closest

/-- Correction witnesses for the `u2 = 0` branch of `ErrFMA_correct`.

If the product error `u2` is zero, then `alpha1` is the rounding of the
already formatted value `y`, so `alpha2 = 0`.  This helper reduces that branch
to `ErrFMA_correction_witnesses_of_alpha2_zero`. -/
theorem ErrFMA_correction_witnesses_of_u2_zero
    (emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hβ : 1 < (2 : Int))
    (hprec : precisionNotZero prec)
    (hemin : emin ≤ 0)
    (Fa : generic_format 2 (FLT_exp emin prec) a)
    (Fx : generic_format 2 (FLT_exp emin prec) x)
    (Fy : generic_format 2 (FLT_exp emin prec) y)
    (Und1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow 2 (emin + 2 * prec - 1) ≤ |a * x|)
    (hu2_zero :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
      let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
      let u2 := a * x - u1
      u2 = 0) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let bnd : Fbound := make_bound 2 prec emin
    let bo : Fbound_skel := toFboundSkel bnd
    ∃ fa fx fy fr1 fu1 fu2 fal1 fal2 fbe1 fbe2 fdiff fgat fcorr fga :
        FloatSpec.Core.Defs.FlocqFloat 2,
      ErrFMA_real_values emin prec choice a x y
        fa fx fy fr1 fu1 fu2 fal1 fal2 fbe1 fbe2 fga ∧
      Fbounded (beta:=2) bo fa ∧
      Fbounded (beta:=2) bo fx ∧
      Fbounded (beta:=2) bo fy ∧
      Fbounded (beta:=2) bo fdiff ∧
      _root_.F2R (beta:=2) fdiff =
        _root_.F2R (beta:=2) fbe1 - _root_.F2R (beta:=2) fr1 ∧
      _root_.F2R (beta:=2) fu2 =
        _root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fx -
          _root_.F2R (beta:=2) fu1 ∧
      _root_.F2R (beta:=2) fal2 =
        _root_.F2R (beta:=2) fy + _root_.F2R (beta:=2) fu2 -
          _root_.F2R (beta:=2) fal1 ∧
      _root_.F2R (beta:=2) fbe2 =
        _root_.F2R (beta:=2) fu1 + _root_.F2R (beta:=2) fal1 -
          _root_.F2R (beta:=2) fbe1 ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fx) fu1 ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fy + _root_.F2R (beta:=2) fu2) fal1 ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fx +
          _root_.F2R (beta:=2) fy) fr1 ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fu1 + _root_.F2R (beta:=2) fal1) fbe1 ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fbe1 - _root_.F2R (beta:=2) fr1) fgat ∧
      Closest (beta:=2) bo (2 : ℝ)
        (_root_.F2R (beta:=2) fgat + _root_.F2R (beta:=2) fbe2) fga ∧
      (_root_.F2R (beta:=2) fbe2 = 0 ∨
        (Fbounded (beta:=2) bo fcorr ∧
          _root_.F2R (beta:=2) fcorr =
            _root_.F2R (beta:=2) fgat + _root_.F2R (beta:=2) fbe2)) := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let alpha1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (y + u2)
  let alpha2 := (y + u2) - alpha1
  have hu2_zero' : u2 = 0 := by
    simpa [rnd, u1, u2] using hu2_zero
  have hround_y :
      FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd y = y :=
    FloatSpec.Core.Generic_fmt.roundR_generic
      (beta := 2) (fexp := FLT_exp emin prec) (rnd := rnd)
      (x := y) hβ Fy
  have halpha1_y : alpha1 = y := by
    simpa [alpha1, hu2_zero'] using hround_y
  have halpha2_zero :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
      let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
      let u2 := a * x - u1
      let alpha1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (y + u2)
      let alpha2 := (y + u2) - alpha1
      alpha2 = 0 := by
    change alpha2 = 0
    rw [show alpha2 = y + u2 - alpha1 by rfl, hu2_zero', halpha1_y]
    ring
  simpa using
    ErrFMA_correction_witnesses_of_alpha2_zero
      (emin := emin) (prec := prec) (choice := choice) (a := a) (x := x) (y := y)
      hβ hprec hemin Fa Fx Fy Und1 halpha2_zero

noncomputable def ErrFMA_correct_from_FmaErr_payload_check
    (emin prec : Int) (choice : Int → Bool) (a x y : ℝ) : Unit :=
  ()

/-- Wrapper bridge from lower `Pff.FmaErr` to Coq `Pff2Flocq.ErrFMA_correct`.

Once the public wrapper has produced Pff witnesses for all rounded values and
the correction split required by `FmaErr`, this lemma turns the lower Pff
reconstruction into the public Flocq equality `r1 + r2 + r3 = a*x + y`. -/
theorem ErrFMA_correct_from_FmaErr_payload
    (emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (bo : Fbound_skel) (precision : Nat)
    (fa fx fy fr1 fu1 fu2 fal1 fal2 fbe1 fbe2 fdiff fgat fcorr fga :
      FloatSpec.Core.Defs.FlocqFloat 2) :
    ⦃⌜ErrFMA_real_values emin prec choice a x y
          fa fx fy fr1 fu1 fu2 fal1 fal2 fbe1 fbe2 fga ∧
        1 < (2 : Int) ∧ precision ≠ 0 ∧
        1 < bo.vNum ∧
        bo.vNum = Zpower_nat 2 precision ∧
        (∀ r : ℝ, -bo.dExp ≤ (boundR (beta:=2) 2 r).Fexp) ∧
        TotalP (Closest (beta:=2) bo (2 : ℝ)) ∧
        Fbounded (beta:=2) bo fa ∧
        Fbounded (beta:=2) bo fx ∧
        Fbounded (beta:=2) bo fy ∧
        -bo.dExp ≤ fa.Fexp + fx.Fexp ∧
        Fbounded (beta:=2) bo fdiff ∧
        _root_.F2R (beta:=2) fdiff =
          _root_.F2R (beta:=2) fbe1 - _root_.F2R (beta:=2) fr1 ∧
        _root_.F2R (beta:=2) fu2 =
          _root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fx -
            _root_.F2R (beta:=2) fu1 ∧
        _root_.F2R (beta:=2) fal2 =
          _root_.F2R (beta:=2) fy + _root_.F2R (beta:=2) fu2 -
            _root_.F2R (beta:=2) fal1 ∧
        _root_.F2R (beta:=2) fbe2 =
          _root_.F2R (beta:=2) fu1 + _root_.F2R (beta:=2) fal1 -
            _root_.F2R (beta:=2) fbe1 ∧
        Closest (beta:=2) bo (2 : ℝ)
          (_root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fx) fu1 ∧
        Closest (beta:=2) bo (2 : ℝ)
          (_root_.F2R (beta:=2) fy + _root_.F2R (beta:=2) fu2) fal1 ∧
        Closest (beta:=2) bo (2 : ℝ)
          (_root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fx +
            _root_.F2R (beta:=2) fy) fr1 ∧
        Closest (beta:=2) bo (2 : ℝ)
          (_root_.F2R (beta:=2) fu1 + _root_.F2R (beta:=2) fal1) fbe1 ∧
        Closest (beta:=2) bo (2 : ℝ)
          (_root_.F2R (beta:=2) fbe1 - _root_.F2R (beta:=2) fr1) fgat ∧
        Closest (beta:=2) bo (2 : ℝ)
          (_root_.F2R (beta:=2) fgat + _root_.F2R (beta:=2) fbe2) fga ∧
        (_root_.F2R (beta:=2) fbe2 = 0 ∨
          (Fbounded (beta:=2) bo fcorr ∧
            _root_.F2R (beta:=2) fcorr =
              _root_.F2R (beta:=2) fgat + _root_.F2R (beta:=2) fbe2))⌝⦄
    (pure (ErrFMA_correct_from_FmaErr_payload_check emin prec choice a x y) :
      Id Unit)
    ⦃⇓_ => ⌜let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
      let r1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x + y)
      let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
      let u2 := a * x - u1
      let alpha1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (y + u2)
      let alpha2 := (y + u2) - alpha1
      let beta1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (u1 + alpha1)
      let beta2 := (u1 + alpha1) - beta1
      let gamma := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
        (FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
      let r2 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (gamma + alpha2)
      let r3 := (gamma + alpha2) - r2
      a * x + y = r1 + r2 + r3⌝⦄ := by
  intro h
  rcases h with
    ⟨hvals, hradix, hprecision, hvnum_gt, hvnum, hBoundExp, hTotal,
      hfa_bound, hfx_bound, hfy_bound, hprod_exp, hdiff_bound, hdiff_val,
      hu2_val, hal2_val, hbe2_val, hu1_closest, hal1_closest, hr1_closest,
      hbe1_closest, hgat_closest, hga_closest, hsplit⟩
  simp only [wp, PostCond.noThrow, pure,
    ErrFMA_correct_from_FmaErr_payload_check, Id.run, ULift.up_down]
  rcases hvals with
    ⟨hfa_val, hfx_val, hfy_val, hfr1_val, _hfu1_val, _hfu2_val,
      _hfal1_val, hfal2_val, _hfbe1_val, _hfbe2_val, hfga_val⟩
  have hfma := FmaErr_from_correction_split (beta:=2) bo 2 precision
    fa fx fy fr1 fu1 fu2 fal1 fal2 fbe1 fbe2 fdiff fgat fcorr fga
  have hfma_out :
      (_root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fx +
          _root_.F2R (beta:=2) fy =
        _root_.F2R (beta:=2) fr1 + _root_.F2R (beta:=2) fga +
          _root_.F2R (beta:=2) fal2) ∧
      ∃ ga_e al2_e : FloatSpec.Core.Defs.FlocqFloat 2,
        _root_.F2R (beta:=2) ga_e = _root_.F2R (beta:=2) fga ∧
        _root_.F2R (beta:=2) al2_e = _root_.F2R (beta:=2) fal2 ∧
        Fbounded (beta:=2) bo ga_e ∧
        Fbounded (beta:=2) bo al2_e ∧
        al2_e.Fexp ≤ ga_e.Fexp := by
    simpa only [wp, PostCond.noThrow, pure, FmaErr_from_correction_split_check, Id.run,
      ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using
      hfma ⟨rfl, hradix, hprecision, hvnum_gt, hvnum, hBoundExp, hTotal,
        hfa_bound, hfx_bound, hfy_bound, hprod_exp, hdiff_bound, hdiff_val,
        hu2_val, hal2_val, hbe2_val, hu1_closest, hal1_closest, hr1_closest,
        hbe1_closest, hgat_closest, hga_closest, hsplit⟩
  have hcore :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
      let r1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x + y)
      let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
      let u2 := a * x - u1
      let alpha1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (y + u2)
      let alpha2 := (y + u2) - alpha1
      let beta1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (u1 + alpha1)
      let beta2 := (u1 + alpha1) - beta1
      let gamma := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
        (FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
      a * x + y = r1 + gamma + alpha2 := by
    exact by
      simpa [ErrFMA_real_values, hfa_val, hfx_val, hfy_val, hfr1_val,
        hfal2_val, hfga_val] using hfma_out.1
  have hpublic := ErrFMA_correct_from_core_equality
    (beta := 2) (emin := emin) (prec := prec) (choice := choice)
    (a := a) (x := x) (y := y) hcore
  simpa using hpublic

/-- Coq theorem: `ErrFMA_correct`.

This public wrapper records the final algebraic handoff used after the lower
Pff `FmaErr` reconstruction: from the core equality
`a*x+y = r1 + gamma + alpha2`, it derives the exposed split
`a*x+y = r1 + r2 + r3`. -/
theorem ErrFMA_correct_from_core_payload (emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hcore :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
      let r1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x + y)
      let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
      let u2 := a * x - u1
      let alpha1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (y + u2)
      let alpha2 := (y + u2) - alpha1
      let beta1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (u1 + alpha1)
      let beta2 := (u1 + alpha1) - beta1
      let gamma := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
        (FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
      a * x + y = r1 + gamma + alpha2) :
    ⦃⌜True⌝⦄
    (pure (ErrFMA_correct_check emin prec choice a x y) : Id Unit)
    ⦃⇓_ => ⌜let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
      let r1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x + y)
      let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
      let u2 := a * x - u1
      let alpha1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (y + u2)
      let alpha2 := (y + u2) - alpha1
      let beta1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (u1 + alpha1)
      let beta2 := (u1 + alpha1) - beta1
      let gamma := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
        (FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
      let r2 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (gamma + alpha2)
      let r3 := (gamma + alpha2) - r2
      a * x + y = r1 + r2 + r3⌝⦄ := by
  intro _
  have hpublic := ErrFMA_correct_from_core_equality
    (beta := 2) (emin := emin) (prec := prec) (choice := choice)
    (a := a) (x := x) (y := y) hcore
  simpa [wp, PostCond.noThrow, pure, ErrFMA_correct_check, Id.run] using hpublic

/-- Coq: `mult_error_FLT_ge_bpow'`.
Nearest-even specialization of `Prop.Mult_error.mult_error_FLT_ge_bpow`, with
the upstream zero-error disjunct and exponent weakening. -/
theorem mult_error_FLT_ge_bpow' (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
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

private noncomputable def flocqCanonicalFloat
    (beta : Int) [ValidRadix beta] (fexp : Int → Int) (x : ℝ) :
    FloatSpec.Core.Defs.FlocqFloat beta :=
  FloatSpec.Core.Defs.FlocqFloat.mk
    (FloatSpec.Core.Raux.Ztrunc
      (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x))
    (FloatSpec.Core.Generic_fmt.cexp beta fexp x)

private theorem F2R_flocqCanonicalFloat
    (beta : Int) [ValidRadix beta] (fexp : Int → Int) [FloatSpec.Core.Generic_fmt.Valid_exp fexp]
    (x : ℝ)
    (hx : generic_format beta fexp x) :
    _root_.F2R (flocqCanonicalFloat beta fexp x) = x := by
  simpa [flocqCanonicalFloat, FloatSpec.Core.Generic_fmt.generic_format,
    _root_.F2R, FloatSpec.Core.Defs.F2R] using hx.symm

private theorem abs_roundR_ge_generic
    (beta : Int) [ValidRadix beta] (fexp : Int → Int) [FloatSpec.Core.Generic_fmt.Valid_exp fexp]
    (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x y : ℝ)
    (hβ : 1 < beta)
    (hxF : generic_format beta fexp x)
    (hxle : x ≤ |y|) :
    x ≤ |FloatSpec.Core.Generic_fmt.roundR beta fexp rnd y| := by
  by_cases hy : 0 ≤ y
  · have hy_abs : |y| = y := abs_of_nonneg hy
    have hxle' : x ≤ y := by simpa [hy_abs] using hxle
    have hx_le_r : x ≤ FloatSpec.Core.Generic_fmt.roundR beta fexp rnd y :=
      FloatSpec.Core.Generic_fmt.roundR_ge_generic
        (beta := beta) (fexp := fexp) (rnd := rnd) (x := x) (y := y)
        hβ hxF hxle'
    exact le_trans hx_le_r (le_abs_self _)
  · have hy' : y ≤ 0 := le_of_not_ge hy
    have hy_abs : |y| = -y := abs_of_nonpos hy'
    have hxle' : x ≤ -y := by simpa [hy_abs] using hxle
    have hx_le_rneg :
        x ≤ FloatSpec.Core.Generic_fmt.roundR beta fexp
          (FloatSpec.Core.Generic_fmt.Zrnd_opp rnd) (-y) :=
      FloatSpec.Core.Generic_fmt.roundR_ge_generic
        (beta := beta) (fexp := fexp)
        (rnd := FloatSpec.Core.Generic_fmt.Zrnd_opp rnd)
        (x := x) (y := -y) hβ hxF hxle'
    have h_opp : FloatSpec.Core.Generic_fmt.roundR beta fexp rnd y =
        - FloatSpec.Core.Generic_fmt.roundR beta fexp
          (FloatSpec.Core.Generic_fmt.Zrnd_opp rnd) (-y) := by
      have h := FloatSpec.Core.Generic_fmt.roundR_opp
        (beta := beta) (fexp := fexp) (rnd := rnd) (x := -y) hβ
      simpa [neg_neg] using h
    have hx_le_abs :
        x ≤ |FloatSpec.Core.Generic_fmt.roundR beta fexp
          (FloatSpec.Core.Generic_fmt.Zrnd_opp rnd) (-y)| :=
      le_trans hx_le_rneg (le_abs_self _)
    simpa [h_opp, abs_neg] using hx_le_abs

private theorem F2R_sum3_ge_bpow
    (beta : Int) [ValidRadix beta] (fexp : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp fexp]
    (x y z : ℝ) (e : Int)
    (hβ : 1 < beta)
    (hx_fmt : generic_format beta fexp x)
    (hy_fmt : generic_format beta fexp y)
    (hz_fmt : generic_format beta fexp z)
    (hx_e : e ≤ FloatSpec.Core.Generic_fmt.cexp beta fexp x)
    (hy_e : e ≤ FloatSpec.Core.Generic_fmt.cexp beta fexp y)
    (hz_e : e ≤ FloatSpec.Core.Generic_fmt.cexp beta fexp z)
    (hsum_ne : x + y + z ≠ 0) :
    FloatSpec.Core.Raux.bpow beta e ≤ |x + y + z| := by
  let fx := flocqCanonicalFloat beta fexp x
  let fy := flocqCanonicalFloat beta fexp y
  let fz := flocqCanonicalFloat beta fexp z
  let fxy := FloatSpec.Calc.Operations.Fplus beta fx fy
  let fxyz := FloatSpec.Calc.Operations.Fplus beta fxy fz
  have hfx : _root_.F2R fx = x := by
    simpa [fx] using F2R_flocqCanonicalFloat beta fexp x hx_fmt
  have hfy : _root_.F2R fy = y := by
    simpa [fy] using F2R_flocqCanonicalFloat beta fexp y hy_fmt
  have hfz : _root_.F2R fz = z := by
    simpa [fz] using F2R_flocqCanonicalFloat beta fexp z hz_fmt
  have hfx_raw : (fx.Fnum : ℝ) * (beta : ℝ) ^ fx.Fexp = x := by
    simpa [_root_.F2R, FloatSpec.Core.Defs.F2R] using hfx
  have hfy_raw : (fy.Fnum : ℝ) * (beta : ℝ) ^ fy.Fexp = y := by
    simpa [_root_.F2R, FloatSpec.Core.Defs.F2R] using hfy
  have hfz_raw : (fz.Fnum : ℝ) * (beta : ℝ) ^ fz.Fexp = z := by
    simpa [_root_.F2R, FloatSpec.Core.Defs.F2R] using hfz
  have hfxy_val : _root_.F2R fxy = x + y := by
    have h := FloatSpec.Calc.Operations.F2R_plus (beta := beta) fx fy
    simpa [fxy, _root_.F2R, FloatSpec.Core.Defs.F2R, hfx_raw, hfy_raw] using h hβ
  have hfxy_raw : (fxy.Fnum : ℝ) * (beta : ℝ) ^ fxy.Fexp = x + y := by
    simpa [_root_.F2R, FloatSpec.Core.Defs.F2R] using hfxy_val
  have hfxyz_val : _root_.F2R fxyz = x + y + z := by
    have h := FloatSpec.Calc.Operations.F2R_plus (beta := beta) fxy fz
    simpa [fxyz, _root_.F2R, FloatSpec.Core.Defs.F2R, hfxy_raw, hfz_raw, add_assoc] using h hβ
  have hfxy_exp : fxy.Fexp = min fx.Fexp fy.Fexp := by
    have h := FloatSpec.Calc.Operations.Fexp_Fplus_spec (beta := beta) fx fy
    exact h True.intro
  have hfxyz_exp : fxyz.Fexp = min fxy.Fexp fz.Fexp := by
    have h := FloatSpec.Calc.Operations.Fexp_Fplus_spec (beta := beta) fxy fz
    exact h True.intro
  have hfx_exp : fx.Fexp = FloatSpec.Core.Generic_fmt.cexp beta fexp x := rfl
  have hfy_exp : fy.Fexp = FloatSpec.Core.Generic_fmt.cexp beta fexp y := rfl
  have hfz_exp : fz.Fexp = FloatSpec.Core.Generic_fmt.cexp beta fexp z := rfl
  have he_le_exp : e ≤ fxyz.Fexp := by
    rw [hfxyz_exp, hfxy_exp]
    exact le_min
      (le_min (by simpa [hfx_exp] using hx_e) (by simpa [hfy_exp] using hy_e))
      (by simpa [hfz_exp] using hz_e)
  have hpow_le : FloatSpec.Core.Raux.bpow beta e ≤
      FloatSpec.Core.Raux.bpow beta fxyz.Fexp := by
    have h := FloatSpec.Core.Raux.bpow_le beta e fxyz.Fexp hβ he_le_exp
    exact h True.intro
  have hfxyz_ne : _root_.F2R fxyz ≠ 0 := by
    intro hzero
    apply hsum_ne
    simpa [hfxyz_val] using hzero
  have hF2R := F2R_ge (beta := beta) fxyz hfxyz_ne hβ
  exact le_trans hpow_le (by simpa [hfxyz_val] using hF2R)

-- Coq: `ErrFMA_bounded_simpl` — simplified boundedness of r1, r2, r3
noncomputable def ErrFMA_bounded_simpl_check (emin prec : Int)
    (a x y : ℝ) : Unit :=
  ()

-- Coq: `ErrFMA_bounded_simpl` — in the ErrFMA V2 setting (nearest-even),
-- the intermediate results `r1`, `r2`, `r3` are in format.
theorem ErrFMA_bounded_simpl (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (a x y : ℝ)
    (hβ : 1 < beta) (hprec : 3 ≤ prec)
    (Fa : generic_format beta (FLT_exp emin prec) a)
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (U1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) ≤ |a * x|)
    (_U2 : y = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec) ≤ |y|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
    let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
    let alpha2 := (y + u2) - alpha1
    let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
    let beta2 := (u1 + alpha1) - beta1
    let gamma := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
      (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
    let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (gamma + alpha2)
    let r3 := (gamma + alpha2) - r2
    generic_format beta (FLT_exp emin prec) r1 ∧
      generic_format beta (FLT_exp emin prec) r2 ∧
      generic_format beta (FLT_exp emin prec) r3 := by
  have V1_Und1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |a * x| := by
    rcases U1 with hzero | hbound
    · exact Or.inl hzero
    · right
      have hβR : (1 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast (le_of_lt hβ)
      have hpow_le :
          FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤
            FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) := by
        have hexp_le : emin + 2 * prec - 1 ≤ emin + 4 * prec - 3 := by
          omega
        simpa [FloatSpec.Core.Raux.bpow] using zpow_le_zpow_right₀ hβR hexp_le
      exact le_trans hpow_le hbound
  exact ErrFMA_bounded (beta := beta) (emin := emin) (prec := prec)
    (choice := fun t : Int => !(decide (2 ∣ t))) (a := a) (x := x) (y := y)
    hβ Fa Fx Fy V1_Und1

/-- Coq: `V2_Und2`.
In the ErrFMA V2 construction, with nearest-even rounding, non-underflow of `y`
implies the rounded `alpha1 := round_flt (y + u2)` is either zero or has
magnitude at least `bpow (emin + prec)`. -/
theorem V2_Und2 (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
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
theorem V2_Und4 (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
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

/-- Coq: `V2_Und5`.
In the ErrFMA V2 construction, with nearest-even rounding, non-underflow of
`a*x` and `y` implies `r1 := round_flt (a*x+y)` is either zero or has magnitude
at least `bpow (emin + prec - 1)`. -/
theorem V2_Und5 (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (a x y : ℝ)
    (hβ : 1 < beta) (hprec : 3 ≤ prec)
    (Fa : generic_format beta (FLT_exp emin prec) a)
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (U1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) ≤ |a * x|)
    (U2 : y = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec) ≤ |y|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
    let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
    a * x ≠ 0 →
      r1 = 0 ∨
        FloatSpec.Core.Raux.bpow beta (emin + prec - 1) ≤ |r1| := by
  dsimp
  intro hax_ne
  let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
  let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
  let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  by_cases hr1_zero : r1 = 0
  · exact Or.inl hr1_zero
  right
  haveI : FloatSpec.Core.Generic_fmt.Monotone_exp (FLT_exp emin prec) := by
    simpa [FLT_exp] using
      (inferInstance :
        FloatSpec.Core.Generic_fmt.Monotone_exp (FloatSpec.Core.FLT.FLT_exp prec emin))
  have hU1_bound :
      FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) ≤ |a * x| := by
    rcases U1 with hzero | hbound
    · exact False.elim (hax_ne hzero)
    · exact hbound
  have htarget_fmt :
      generic_format beta (FLT_exp emin prec)
        (FloatSpec.Core.Raux.bpow beta (emin + prec - 1)) := by
    have htrip := FloatSpec.Core.FLT.generic_format_FLT_bpow
      (prec := prec) (emin := emin) (beta := beta)
      (e := emin + prec - 1)
    have hemin_le : emin ≤ emin + prec - 1 := by
      have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
      omega
    simpa [FLT_exp, FloatSpec.Core.Raux.bpow] using htrip ⟨hβ, hemin_le⟩
  rcases U2 with hy_zero | hy_bound
  · have htarget_le_ax :
        FloatSpec.Core.Raux.bpow beta (emin + prec - 1) ≤ |a * x| := by
      have hpow_le :
          FloatSpec.Core.Raux.bpow beta (emin + prec - 1) ≤
            FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) := by
        have hβR : (1 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast (le_of_lt hβ)
        have hexp_le : emin + prec - 1 ≤ emin + 4 * prec - 3 := by omega
        simpa [FloatSpec.Core.Raux.bpow] using zpow_le_zpow_right₀ hβR hexp_le
      exact le_trans hpow_le hU1_bound
    have hround :=
      abs_roundR_ge_generic (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd)
        (x := FloatSpec.Core.Raux.bpow beta (emin + prec - 1))
        (y := a * x) hβ htarget_fmt htarget_le_ax
    simpa [r1, hy_zero] using hround
  · have hfmt_u1 :
        generic_format beta (FLT_exp emin prec) u1 := by
      simpa [u1, rnd] using
        (FloatSpec.Core.Generic_fmt.generic_format_roundR
          (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd)
          (x := a * x) hβ)
    have hu2_fmt :
        generic_format beta (FLT_exp emin prec) u2 := by
      have hprod_err_fmt :
          generic_format beta (FLT_exp emin prec)
            (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) - a * x) := by
        exact
          mult_error_FLT
            (beta := beta) (prec := prec) (emin := emin) (rnd := rnd)
            (x := a) (y := x) hβ Fa Fx
            (by
              intro hax_ne'
              have hpow_le :
                  FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤
                    FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) := by
                have hβR : (1 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast (le_of_lt hβ)
                have hexp_le : emin + 2 * prec - 1 ≤ emin + 4 * prec - 3 := by
                  omega
                simpa [FloatSpec.Core.Raux.bpow] using zpow_le_zpow_right₀ hβR hexp_le
              exact le_trans hpow_le hU1_bound)
      have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
        (beta := beta) (fexp := FLT_exp emin prec)
        (x := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) - a * x)
      simp only [wp, PostCond.noThrow, PredTrans.pure, Id.run, pure, Bind.bind] at hopp
      have hneg := hopp hprod_err_fmt
      simpa [u2, u1, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
    by_cases hu2_zero : u2 = 0
    · have hweaken_y :
          FloatSpec.Core.Raux.bpow beta ((emin + prec - 1) + prec) ≤ |y| := by
        have hβR : (1 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast (le_of_lt hβ)
        have hpow_le :
            FloatSpec.Core.Raux.bpow beta ((emin + prec - 1) + prec) ≤
              FloatSpec.Core.Raux.bpow beta (emin + 2 * prec) := by
          have hexp_le : (emin + prec - 1) + prec ≤ emin + 2 * prec := by omega
          simpa [FloatSpec.Core.Raux.bpow] using zpow_le_zpow_right₀ hβR hexp_le
        exact le_trans hpow_le hy_bound
      have hround :=
        round_FLT_plus_ge (beta := beta) (rnd := rnd)
          (emin := emin) (prec := prec) (x := y) (y := u1)
          (e := emin + prec - 1) hβ Fy hfmt_u1 hweaken_y
          (by
            intro hzero
            apply hr1_zero
            have hax_decomp : a * x = u1 + u2 := by
              dsimp [u1, u2]
              ring
            have hr1_eq :
                r1 = FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u1) := by
              dsimp [r1]
              congr 1
              rw [hax_decomp, hu2_zero]
              ring
            simpa [hr1_eq] using hzero)
      have hr1_eq :
          r1 = FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u1) := by
        dsimp [r1]
        congr 1
        have hax_decomp : a * x = u1 + u2 := by
          dsimp [u1, u2]
          ring
        rw [hax_decomp, hu2_zero]
        ring
      change FloatSpec.Core.Raux.bpow beta (emin + prec - 1) ≤ |r1|
      rw [hr1_eq]
      exact hround
    · have hu1_strong :
          FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) ≤ |u1| := by
        have hfmt_strong_bpow :
            generic_format beta (FLT_exp emin prec)
              (FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3)) := by
          have htrip := FloatSpec.Core.FLT.generic_format_FLT_bpow
            (prec := prec) (emin := emin) (beta := beta)
            (e := emin + 4 * prec - 3)
          have hemin_le : emin ≤ emin + 4 * prec - 3 := by omega
          simpa [FLT_exp, FloatSpec.Core.Raux.bpow] using htrip ⟨hβ, hemin_le⟩
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
      have hu2_bound :
          FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 2) ≤ |u2| := by
        have hraw := mult_error_FLT_ge_bpow'
          (beta := beta) (emin := emin) (prec := prec)
          (a := a) (b := x) (e := emin + 4 * prec - 3)
          hβ Fa Fx (Or.inr hU1_bound)
        dsimp [rnd] at hraw
        rcases hraw with hzero | hbound
        · exact False.elim (hu2_zero (by simpa [u2, u1] using hzero))
        · have hexp : (emin + 4 * prec - 3) + 1 - 2 * prec =
              emin + 2 * prec - 2 := by omega
          simpa [u2, u1, hexp] using hbound
      have hu1_cexp :
          emin + prec - 1 ≤ FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp emin prec) u1 := by
        have hu1_exp : emin + 4 * prec - 2 - 1 = emin + 4 * prec - 3 := by
          omega
        have hcexp :=
          FloatSpec.Core.Generic_fmt.cexp_ge_bpow
            (beta := beta) (fexp := FLT_exp emin prec)
            (x := u1) (e := emin + 4 * prec - 2) hβ
            (by simpa [FloatSpec.Core.Raux.bpow, hu1_exp] using hu1_strong)
        have hle_fexp : emin + prec - 1 ≤ FLT_exp emin prec (emin + 4 * prec - 2) := by
          simp [FLT_exp, FloatSpec.Core.FLT.FLT_exp]
          omega
        exact le_trans hle_fexp hcexp
      have hy_cexp :
          emin + prec - 1 ≤ FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp emin prec) y := by
        have hcexp :=
          FloatSpec.Core.Generic_fmt.cexp_ge_bpow
            (beta := beta) (fexp := FLT_exp emin prec)
            (x := y) (e := emin + 2 * prec + 1) hβ
            (by simpa [FloatSpec.Core.Raux.bpow] using hy_bound)
        have hle_fexp : emin + prec - 1 ≤ FLT_exp emin prec (emin + 2 * prec + 1) := by
          simp [FLT_exp, FloatSpec.Core.FLT.FLT_exp]
          omega
        exact le_trans hle_fexp hcexp
      have hu2_cexp :
          emin + prec - 1 ≤ FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp emin prec) u2 := by
        have hu2_exp : emin + 2 * prec - 1 - 1 = emin + 2 * prec - 2 := by
          omega
        have hcexp :=
          FloatSpec.Core.Generic_fmt.cexp_ge_bpow
            (beta := beta) (fexp := FLT_exp emin prec)
            (x := u2) (e := emin + 2 * prec - 1) hβ
            (by simpa [FloatSpec.Core.Raux.bpow, hu2_exp] using hu2_bound)
        have hle_fexp : emin + prec - 1 ≤ FLT_exp emin prec (emin + 2 * prec - 1) := by
          simp [FLT_exp, FloatSpec.Core.FLT.FLT_exp]
          omega
        exact le_trans hle_fexp hcexp
      have hsum_ne : u1 + y + u2 ≠ 0 := by
        intro hsum0
        apply hr1_zero
        have hax_decomp : a * x = u1 + u2 := by
          dsimp [u1, u2]
          ring
        have hr1_eq :
            r1 = FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + y + u2) := by
          dsimp [r1]
          congr 1
          rw [hax_decomp]
          ring
        have hrnd0 : rnd (0 : ℝ) = (0 : Int) := by
          simpa using (FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) (0 : Int))
        simpa [hr1_eq, hsum0, FloatSpec.Core.Generic_fmt.roundR,
          FloatSpec.Core.Generic_fmt.scaled_mantissa, hrnd0]
      have hraw :
          FloatSpec.Core.Raux.bpow beta (emin + prec - 1) ≤ |u1 + y + u2| :=
        F2R_sum3_ge_bpow (beta := beta) (fexp := FLT_exp emin prec)
          (x := u1) (y := y) (z := u2) (e := emin + prec - 1)
          hβ hfmt_u1 Fy hu2_fmt hu1_cexp hy_cexp hu2_cexp hsum_ne
      have hround :=
        abs_roundR_ge_generic (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd)
          (x := FloatSpec.Core.Raux.bpow beta (emin + prec - 1))
          (y := u1 + y + u2) hβ htarget_fmt hraw
      have hr1_eq :
          r1 = FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + y + u2) := by
        have hax_decomp : a * x = u1 + u2 := by
          dsimp [u1, u2]
          ring
        dsimp [r1]
        congr 1
        rw [hax_decomp]
        ring
      change FloatSpec.Core.Raux.bpow beta (emin + prec - 1) ≤ |r1|
      rw [hr1_eq]
      exact hround

/-
Coq lemma: `ErrFMA_correct_simpl`

In the ErrFMA V2 section, Coq proves a simplified correctness result stating
that the compensated sum r1 + r2 + r3 equals a*x + y. We mirror the statement
with our hoare-triple style skeleton and defer the proof.
-/

noncomputable def ErrFMA_correct_simpl_check (emin prec : Int)
    (a x y : ℝ) : Unit :=
  ()

/-- Zero-product branch of Coq `ErrFMA_correct_simpl`.

This is the first branch of the upstream simplified V2 proof, specialized to
nearest-even rounding. The remaining branches still depend on the full
`ErrFMA_correct`/`FmaErr` payload stack. -/
theorem ErrFMA_correct_simpl_of_product_eq_zero (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (a x y : ℝ)
    (hβ : 1 < beta)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (hprod : a * x = 0) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
    let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
    let alpha2 := (y + u2) - alpha1
    let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
    let beta2 := (u1 + alpha1) - beta1
    let gamma := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
      (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
    let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (gamma + alpha2)
    let r3 := (gamma + alpha2) - r2
    a * x + y = r1 + r2 + r3 := by
  simpa using
    ErrFMA_correct_of_product_eq_zero
      (beta := beta) (emin := emin) (prec := prec)
      (choice := fun t : Int => !(decide (2 ∣ t)))
      (a := a) (x := x) (y := y) hβ Fy hprod

/-- `u2 = 0` branch of Coq `ErrFMA_correct_simpl`.

Once `u2 := a*x - round(a*x)` vanishes, the product `a*x` is formatted.
The remaining compensation term is the addition error for `a*x + y`, hence it
is fixed by the same rounding operation. -/
theorem ErrFMA_correct_simpl_of_u2_eq_zero (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (a x y : ℝ)
    (hβ : 1 < beta)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (hu2 :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
      let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
      a * x - u1 = 0) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
    let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
    let alpha2 := (y + u2) - alpha1
    let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
    let beta2 := (u1 + alpha1) - beta1
    let gamma := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
      (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
    let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (gamma + alpha2)
    let r3 := (gamma + alpha2) - r2
    a * x + y = r1 + r2 + r3 := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
  let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
  have hu1_eq : FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) = a * x := by
    dsimp [rnd] at hu2
    linarith
  have hround0 :
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd 0 = 0 := by
    have hrnd0 : rnd (0 : ℝ) = (0 : Int) := by
      simpa [rnd] using
        (FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) (0 : Int))
    simp [FloatSpec.Core.Generic_fmt.roundR,
      FloatSpec.Core.Generic_fmt.scaled_mantissa, hrnd0]
  have hround_y :
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd y = y :=
    FloatSpec.Core.Generic_fmt.roundR_generic
      (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd)
      (x := y) hβ Fy
  haveI : FloatSpec.Core.Generic_fmt.Monotone_exp (FLT_exp emin prec) := by
    simpa [FLT_exp] using
      (inferInstance :
        FloatSpec.Core.Generic_fmt.Monotone_exp
          (FloatSpec.Core.FLT.FLT_exp prec emin))
  have hax_fmt : generic_format beta (FLT_exp emin prec) (a * x) := by
    have hfmt := FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd)
      (x := a * x) hβ
    simpa [hu1_eq] using hfmt
  have hadd_err_fmt :
      generic_format beta (FLT_exp emin prec) (r1 - (a * x + y)) := by
    have h := plus_error (beta := beta) (fexp := FLT_exp emin prec)
      (choice := fun t : Int => !(decide (2 ∣ t))) (x := a * x) (y := y)
      hβ hax_fmt Fy
    simpa [FloatSpec.Calc.Round.round, FloatSpec.Compat.Scaffold.ZnearestMode,
      Znearest, rnd, r1] using h
  have hcomp_fmt :
      generic_format beta (FLT_exp emin prec) (a * x + y - r1) := by
    have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := FLT_exp emin prec) (x := r1 - (a * x + y))
    have hneg := hopp hadd_err_fmt
    have hrewrite : -(r1 - (a * x + y)) = a * x + y - r1 := by ring
    simpa [hrewrite] using hneg
  have hround_comp :
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y - r1) =
        a * x + y - r1 :=
    FloatSpec.Core.Generic_fmt.roundR_generic
      (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd)
      (x := a * x + y - r1) hβ hcomp_fmt
  dsimp
  simp [rnd, r1, hu1_eq, hround_y, hround0, hround_comp]

/-- `y = 0` branch of Coq `ErrFMA_correct_simpl`.

When the addend is zero, the simplified V2 reconstruction reduces to the
product rounding error `u2 := a*x - round(a*x)`. The V2 underflow lower bound
is stronger than the one required by `mult_error_FLT`, so `u2` is formatted and
all remaining rounded correction terms are fixed points. -/
theorem ErrFMA_correct_simpl_of_y_eq_zero (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (a x y : ℝ)
    (hβ : 1 < beta)
    (hprec : 3 ≤ prec)
    (Fa : generic_format beta (FLT_exp emin prec) a)
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (U1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) ≤ |a * x|)
    (hy : y = 0) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
    let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
    let alpha2 := (y + u2) - alpha1
    let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
    let beta2 := (u1 + alpha1) - beta1
    let gamma := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
      (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
    let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (gamma + alpha2)
    let r3 := (gamma + alpha2) - r2
    a * x + y = r1 + r2 + r3 := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
  let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  have hround0 :
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd 0 = 0 := by
    have hrnd0 : rnd (0 : ℝ) = (0 : Int) := by
      simpa [rnd] using
        (FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) (0 : Int))
    simp [FloatSpec.Core.Generic_fmt.roundR,
      FloatSpec.Core.Generic_fmt.scaled_mantissa, hrnd0]
  have hu2_fmt : generic_format beta (FLT_exp emin prec) u2 := by
    have hprod_err :
        generic_format beta (FLT_exp emin prec)
          (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) -
            a * x) := by
      exact mult_error_FLT (beta := beta) (prec := prec)
        (rnd := rnd) (emin := emin) (x := a) (y := x)
        hβ Fa Fx (by
          intro hprod_ne
          rcases U1 with hzero | hbound
          · exact False.elim (hprod_ne hzero)
          ·
            have hexp_le : emin + 2 * prec - 1 ≤ emin + 4 * prec - 3 := by
              omega
            have hbpow_le :
                FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤
                  FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) := by
              have h := FloatSpec.Core.Raux.bpow_le beta
                (emin + 2 * prec - 1) (emin + 4 * prec - 3) hβ hexp_le
              change (beta : ℝ) ^ (emin + 2 * prec - 1) ≤
                (beta : ℝ) ^ (emin + 4 * prec - 3)
              simpa [wp, PostCond.noThrow, pure,
                FloatSpec.Core.Raux.bpow_le_check, PredTrans.pure,
                PredTrans.apply, SPred.down_pure_nil] using h True.intro
            exact le_trans hbpow_le hbound)
    have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := FLT_exp emin prec)
      (x := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) -
        a * x)
    simp only [wp, PostCond.noThrow, PredTrans.pure, Id.run, pure, Bind.bind] at hopp
    have hneg_fmt := hopp hprod_err
    have hu2_eq :
        u2 =
          -(FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) -
            a * x) := by
      dsimp [u2, u1]
      ring
    simpa [hu2_eq] using hneg_fmt
  have hround_u2 :
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd u2 = u2 :=
    FloatSpec.Core.Generic_fmt.roundR_generic
      (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd)
      (x := u2) hβ hu2_fmt
  dsimp
  simp [rnd, u1, u2, hy, hround0, hround_u2]

/-- Final algebraic wrapper step of Coq `ErrFMA_correct_simpl`.

This is the nearest-even specialization of `ErrFMA_correct_from_core_equality`.
The lower FMA payload reconstructs `a*x+y` as `r1 + gamma + alpha2`; the public
simplified theorem returns the let-bound split `r1 + r2 + r3`. -/
theorem ErrFMA_correct_simpl_from_core_equality
    (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (a x y : ℝ)
    (hcore :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
      let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
      let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
      let u2 := a * x - u1
      let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
      let alpha2 := (y + u2) - alpha1
      let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
      let beta2 := (u1 + alpha1) - beta1
      let gamma := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
        (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
      a * x + y = r1 + gamma + alpha2) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
    let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
    let alpha2 := (y + u2) - alpha1
    let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
    let beta2 := (u1 + alpha1) - beta1
    let gamma := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
      (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
    let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (gamma + alpha2)
    let r3 := (gamma + alpha2) - r2
    a * x + y = r1 + r2 + r3 := by
  simpa using
    ErrFMA_correct_from_core_equality
      (beta := beta) (emin := emin) (prec := prec)
      (choice := fun t : Int => !(decide (2 ∣ t)))
      (a := a) (x := x) (y := y) hcore

noncomputable def ErrFMA_correct_simpl_from_FmaErr_payload_check
    (emin prec : Int) (a x y : ℝ) : Unit :=
  ()

/-- Nearest-even specialization of `ErrFMA_correct_from_FmaErr_payload`.

This is the checked wrapper bridge needed before the public
`ErrFMA_correct_simpl` theorem can call the lower Pff `FmaErr` reconstruction. -/
theorem ErrFMA_correct_simpl_from_FmaErr_payload
    (emin prec : Int) [Prec_gt_0 prec]
    (a x y : ℝ)
    (bo : Fbound_skel) (precision : Nat)
    (fa fx fy fr1 fu1 fu2 fal1 fal2 fbe1 fbe2 fdiff fgat fcorr fga :
      FloatSpec.Core.Defs.FlocqFloat 2) :
    ⦃⌜ErrFMA_real_values emin prec (fun t : Int => !(decide (2 ∣ t))) a x y
          fa fx fy fr1 fu1 fu2 fal1 fal2 fbe1 fbe2 fga ∧
        1 < (2 : Int) ∧ precision ≠ 0 ∧
        1 < bo.vNum ∧
        bo.vNum = Zpower_nat 2 precision ∧
        (∀ r : ℝ, -bo.dExp ≤ (boundR (beta:=2) 2 r).Fexp) ∧
        TotalP (Closest (beta:=2) bo (2 : ℝ)) ∧
        Fbounded (beta:=2) bo fa ∧
        Fbounded (beta:=2) bo fx ∧
        Fbounded (beta:=2) bo fy ∧
        -bo.dExp ≤ fa.Fexp + fx.Fexp ∧
        Fbounded (beta:=2) bo fdiff ∧
        _root_.F2R (beta:=2) fdiff =
          _root_.F2R (beta:=2) fbe1 - _root_.F2R (beta:=2) fr1 ∧
        _root_.F2R (beta:=2) fu2 =
          _root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fx -
            _root_.F2R (beta:=2) fu1 ∧
        _root_.F2R (beta:=2) fal2 =
          _root_.F2R (beta:=2) fy + _root_.F2R (beta:=2) fu2 -
            _root_.F2R (beta:=2) fal1 ∧
        _root_.F2R (beta:=2) fbe2 =
          _root_.F2R (beta:=2) fu1 + _root_.F2R (beta:=2) fal1 -
            _root_.F2R (beta:=2) fbe1 ∧
        Closest (beta:=2) bo (2 : ℝ)
          (_root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fx) fu1 ∧
        Closest (beta:=2) bo (2 : ℝ)
          (_root_.F2R (beta:=2) fy + _root_.F2R (beta:=2) fu2) fal1 ∧
        Closest (beta:=2) bo (2 : ℝ)
          (_root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fx +
            _root_.F2R (beta:=2) fy) fr1 ∧
        Closest (beta:=2) bo (2 : ℝ)
          (_root_.F2R (beta:=2) fu1 + _root_.F2R (beta:=2) fal1) fbe1 ∧
        Closest (beta:=2) bo (2 : ℝ)
          (_root_.F2R (beta:=2) fbe1 - _root_.F2R (beta:=2) fr1) fgat ∧
        Closest (beta:=2) bo (2 : ℝ)
          (_root_.F2R (beta:=2) fgat + _root_.F2R (beta:=2) fbe2) fga ∧
        (_root_.F2R (beta:=2) fbe2 = 0 ∨
          (Fbounded (beta:=2) bo fcorr ∧
            _root_.F2R (beta:=2) fcorr =
              _root_.F2R (beta:=2) fgat + _root_.F2R (beta:=2) fbe2))⌝⦄
    (pure (ErrFMA_correct_simpl_from_FmaErr_payload_check emin prec a x y) :
      Id Unit)
    ⦃⇓_ => ⌜let rnd :=
        FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
      let r1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x + y)
      let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
      let u2 := a * x - u1
      let alpha1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (y + u2)
      let alpha2 := (y + u2) - alpha1
      let beta1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (u1 + alpha1)
      let beta2 := (u1 + alpha1) - beta1
      let gamma := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
        (FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
      let r2 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (gamma + alpha2)
      let r3 := (gamma + alpha2) - r2
      a * x + y = r1 + r2 + r3⌝⦄ := by
  intro h
  simp only [wp, PostCond.noThrow, pure,
    ErrFMA_correct_simpl_from_FmaErr_payload_check, Id.run, ULift.up_down]
  have hgeneral := ErrFMA_correct_from_FmaErr_payload
    (emin := emin) (prec := prec) (choice := fun t : Int => !(decide (2 ∣ t)))
    (a := a) (x := x) (y := y)
    (bo := bo) (precision := precision)
    (fa := fa) (fx := fx) (fy := fy) (fr1 := fr1) (fu1 := fu1) (fu2 := fu2)
    (fal1 := fal1) (fal2 := fal2) (fbe1 := fbe1) (fbe2 := fbe2)
    (fdiff := fdiff) (fgat := fgat) (fcorr := fcorr) (fga := fga)
  simpa only [wp, PostCond.noThrow, pure,
    ErrFMA_correct_from_FmaErr_payload_check, Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using
    hgeneral h

-- Coq: `ErrFMA_correct_simpl` — simplified equality r1 + r2 + r3 = a * x + y
-- under the ErrFMA V2 construction with ties-to-even rounding.
/-- Coq theorem: `ErrFMA_correct_simpl`.

This nearest-even public wrapper is the simplified specialization of
`ErrFMA_correct`: once the lower payload supplies
`a*x+y = r1 + gamma + alpha2`, the final split follows from the checked
algebraic bridge. -/
theorem ErrFMA_correct_simpl_from_core_payload (emin prec : Int) [Prec_gt_0 prec]
    (a x y : ℝ)
    (hcore :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
      let r1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x + y)
      let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
      let u2 := a * x - u1
      let alpha1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (y + u2)
      let alpha2 := (y + u2) - alpha1
      let beta1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (u1 + alpha1)
      let beta2 := (u1 + alpha1) - beta1
      let gamma := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
        (FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
      a * x + y = r1 + gamma + alpha2) :
    ⦃⌜True⌝⦄
    (pure (ErrFMA_correct_simpl_check emin prec a x y) : Id Unit)
    ⦃⇓_ => ⌜let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
      let r1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x + y)
      let u1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (a * x)
      let u2 := a * x - u1
      let alpha1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (y + u2)
      let alpha2 := (y + u2) - alpha1
      let beta1 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (u1 + alpha1)
      let beta2 := (u1 + alpha1) - beta1
      let gamma := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
        (FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
      let r2 := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (gamma + alpha2)
      let r3 := (gamma + alpha2) - r2
      a * x + y = r1 + r2 + r3⌝⦄ := by
  intro _
  have hpublic := ErrFMA_correct_simpl_from_core_equality
    (beta := 2) (emin := emin) (prec := prec)
    (a := a) (x := x) (y := y) hcore
  simpa [wp, PostCond.noThrow, pure, ErrFMA_correct_simpl_check, Id.run] using
    hpublic

/-- Coq `Pff2Flocq.ErrFMA_correct`.  All Pff floats and rounded-mode facts are
constructed from the Flocq inputs; the public theorem exposes only the source
format and non-underflow hypotheses. -/
theorem ErrFMA_correct (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hEven : Even beta)
    (hprecision : 3 ≤ prec)
    (hemin : emin ≤ 0)
    (Fa : generic_format beta (FLT_exp emin prec) a)
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (V1_Und1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |a * x|)
    (V1_Und2 :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
      let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
      let u2 := a * x - u1
      let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
      alpha1 = 0 ∨ FloatSpec.Core.Raux.bpow beta (emin + prec) ≤ |alpha1|)
    (V1_Und4 :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
      let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
      let u2 := a * x - u1
      let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
      let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
      beta1 = 0 ∨ FloatSpec.Core.Raux.bpow beta (emin + prec + 1) ≤ |beta1|)
    (V1_Und5 :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
      let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
      r1 = 0 ∨ FloatSpec.Core.Raux.bpow beta (emin + prec - 1) ≤ |r1|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
    let alpha2 := (y + u2) - alpha1
    let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
    let beta2 := (u1 + alpha1) - beta1
    let gamma := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
      (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
    let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (gamma + alpha2)
    let r3 := gamma + alpha2 - r2
    a * x + y = r1 + r2 + r3 := by
  classical
  rcases V1_Und1 with hprodZero | hprodLower
  · exact ErrFMA_correct_of_product_eq_zero beta emin prec choice a x y
      ValidRadix.valid Fy hprodZero
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
  let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
  let alpha2 := y + u2 - alpha1
  let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
  let beta2 := u1 + alpha1 - beta1
  let gat := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (beta1 - r1)
  let gamma := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (gat + beta2)
  have hβ : 1 < beta := ValidRadix.valid
  have hprec : precisionNotZero prec := by unfold precisionNotZero; omega
  have hprecPos : 0 ≤ prec := by omega
  have habsPrec : prec.natAbs = prec.toNat := by omega
  have hprecNat : (prec.toNat : Int) = prec := Int.toNat_of_nonneg hprecPos
  let bnd : Fbound := make_bound beta prec emin (hβ:=hβ)
  let bo : Fbound_skel := toFboundSkel bnd
  have hpBound : pGivesBound beta bnd prec := by
    have h := make_bound_p beta prec emin
    have hv : bnd.vNum = Zpower_nat beta prec.natAbs := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound] using hv
  have hvNum : bo.vNum = Zpower_nat beta prec.toNat := by
    simpa [bo, pGivesBound, habsPrec] using hpBound
  have hbndExp : -bnd.dExp = emin := by
    have h := make_bound_Emin beta prec emin
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using h hemin
    omega
  have hboExp : -bo.dExp = emin := by simpa [bo] using hbndExp
  let P := fun z : ℝ => fun f : FloatSpec.Core.Defs.FlocqFloat beta =>
    f = RND_Closest (beta:=beta) bo beta prec choice z
  have hcan (z : ℝ) :
      Fcanonic (beta:=beta) beta bo (RND_Closest (beta:=beta) bo beta prec choice z) := by
    have h := RND_Closest_canonic (beta:=beta) bo beta prec choice z
    simpa only [wp, PostCond.noThrow, pure, RND_Closest_canonic_check,
      Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨rfl, hβ, hprec, hvNum⟩
  have hclose (z : ℝ) : Closest (beta:=beta) bo (beta : ℝ) z
      (RND_Closest (beta:=beta) bo beta prec choice z) := by
    have h := RND_Closest_correct (beta:=beta) bo beta prec choice z
    simpa only [wp, PostCond.noThrow, pure, RND_Closest_correct_check,
      Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨rfl, hβ, hprec, hvNum⟩
  have hval (z : ℝ) :
      _root_.F2R (beta:=beta) (RND_Closest (beta:=beta) bo beta prec choice z) =
        FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd z := by
    have h := pff_round_N_is_round beta bnd prec choice z hpBound hprec hβ
    simpa [bo, rnd, hbndExp] using h
  let fr1 := RND_Closest (beta:=beta) bo beta prec choice (a * x + y)
  let fu1 := RND_Closest (beta:=beta) bo beta prec choice (a * x)
  let fal1 := RND_Closest (beta:=beta) bo beta prec choice (y + u2)
  let fbe1 := RND_Closest (beta:=beta) bo beta prec choice (u1 + alpha1)
  let fgat := RND_Closest (beta:=beta) bo beta prec choice (beta1 - r1)
  let fga := RND_Closest (beta:=beta) bo beta prec choice (gat + beta2)
  have hfr1Val : _root_.F2R (beta:=beta) fr1 = r1 := by simpa [fr1, r1] using hval (a*x+y)
  have hfu1Val : _root_.F2R (beta:=beta) fu1 = u1 := by simpa [fu1, u1] using hval (a*x)
  have hfal1Val : _root_.F2R (beta:=beta) fal1 = alpha1 := by
    simpa [fal1, alpha1] using hval (y+u2)
  have hfbe1Val : _root_.F2R (beta:=beta) fbe1 = beta1 := by
    simpa [fbe1, beta1] using hval (u1+alpha1)
  have hfgatVal : _root_.F2R (beta:=beta) fgat = gat := by
    simpa [fgat, gat] using hval (beta1-r1)
  have hfgaVal : _root_.F2R (beta:=beta) fga = gamma := by
    simpa [fga, gamma] using hval (gat+beta2)
  rcases ErrFMA_error_value_witnesses beta emin prec choice a x y hβ hprec hemin
      Fa Fx Fy (Or.inr hprodLower) with
    ⟨fa, fx, fy, fu2, fal2, fbe2, hfa, hfx, hfy, hfu2, hfal2, hfbe2⟩
  have hfal1Can : Fcanonic (beta:=beta) beta bo fal1 := by simpa [fal1] using hcan (y+u2)
  have hfu1Can : Fcanonic (beta:=beta) beta bo fu1 := by simpa [fu1] using hcan (a*x)
  have hfbe1Can : Fcanonic (beta:=beta) beta bo fbe1 := by simpa [fbe1] using hcan (u1+alpha1)
  have hfr1Can : Fcanonic (beta:=beta) beta bo fr1 := by simpa [fr1] using hcan (a*x+y)
  have hfal1Bound : Fbounded (beta:=beta) bo fal1 :=
    (FcanonicBound (beta:=beta) beta bo fal1) hfal1Can
  have hfu1Bound : Fbounded (beta:=beta) bo fu1 :=
    (FcanonicBound (beta:=beta) beta bo fu1) hfu1Can
  have hfbe1Bound : Fbounded (beta:=beta) bo fbe1 :=
    (FcanonicBound (beta:=beta) beta bo fbe1) hfbe1Can
  have hfal1Exp : -bo.dExp < fal1.Fexp ∨ _root_.F2R (beta:=beta) fal1 = 0 := by
    rcases V1_Und2 with hz | hm
    · right; simpa [hfal1Val] using hz
    · left
      have h := FloatFexp_gt beta bnd prec emin fal1
      have he : emin < fal1.Fexp := by
        simpa only [wp, PostCond.noThrow, FloatFexp_gt_check, pure, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h
          ⟨hpBound, by simpa [bo] using hfal1Bound,
            by simpa [hfal1Val, hboExp, FloatSpec.Core.Raux.bpow] using hm,
            hβ, by omega⟩
      omega
  have hUnd3 := V1_Und3 beta emin prec choice a x y hβ hprecision Fa Fx Fy
      (Or.inr hprodLower)
  have hfu1Exp : -bo.dExp < fu1.Fexp ∨ _root_.F2R (beta:=beta) fu1 = 0 := by
    rcases hUnd3 with hz | hm
    · right; simpa [hfu1Val] using hz
    · left
      have h := FloatFexp_gt beta bnd prec emin fu1
      have he : emin < fu1.Fexp := by
        simpa only [wp, PostCond.noThrow, FloatFexp_gt_check, pure, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h
          ⟨hpBound, by simpa [bo] using hfu1Bound,
            by simpa [hfu1Val, hboExp, FloatSpec.Core.Raux.bpow] using hm,
            hβ, by omega⟩
      omega
  have hfbe1Exp : -bo.dExp + 1 < fbe1.Fexp ∨ _root_.F2R (beta:=beta) fbe1 = 0 := by
    rcases V1_Und4 with hz | hm
    · right; simpa [hfbe1Val] using hz
    · left
      have h := FloatFexp_gt beta bnd prec (emin + 1) fbe1
      have : emin + 1 < fbe1.Fexp := by
        simpa only [wp, PostCond.noThrow, FloatFexp_gt_check, pure, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h
          ⟨hpBound, by simpa [bo] using hfbe1Bound,
            by simpa [hfbe1Val, FloatSpec.Core.Raux.bpow, add_assoc,
              add_comm, add_left_comm] using hm,
            hβ, by omega⟩
      omega
  have hfr1Normal : Fnormal (beta:=beta) beta bo fr1 ∨
      _root_.F2R (beta:=beta) fr1 = 0 := by
    rcases V1_Und5 with hz | hm
    · right; simpa [hfr1Val] using hz
    · left
      have h := CanonicGeNormal beta bnd prec fr1
      simpa [wp, PostCond.noThrow, CanonicGeNormal_check, pure,
        PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, PFnormal, bo] using h
        ⟨by simpa [bo] using hfr1Can, hpBound, hprec,
          by simpa [hfr1Val, hbndExp, FloatSpec.Core.Raux.bpow] using hm, hβ⟩
  have hprodExp : -bo.dExp ≤ fa.Fexp + fx.Fexp := by
    have h := underf_mult_aux' (beta:=beta) bo prec fa fx
    simpa only [wp, PostCond.noThrow, pure, underf_mult_aux'_check, Id.run, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h
      ⟨hβ, hprec, by simpa [bo, pGivesBound] using hpBound, hfa.2, hfx.2,
        by simpa [hboExp, hfa.1, hfx.1] using hprodLower⟩
  have hPClosest : ∀ z f, P z f → Closest (beta:=beta) bo (beta : ℝ) z f := by
    intro z f hf; subst f; exact hclose z
  have hPCompat : ∀ r s f g, P r f → P s g → r = s →
      _root_.F2R (beta:=beta) f = _root_.F2R (beta:=beta) g := by
    intro r s f g hf hg hrs
    subst f; subst g; subst s; rfl
  have hfma := FmaErr (beta:=beta) bo beta prec.toNat P
    fa fx fy fr1 fu1 fu2 fal1 fal2 fbe1 fbe2 fgat fga
  have hcorePff :
      _root_.F2R (beta:=beta) fa * _root_.F2R (beta:=beta) fx +
          _root_.F2R (beta:=beta) fy =
        _root_.F2R (beta:=beta) fr1 + _root_.F2R (beta:=beta) fga +
          _root_.F2R (beta:=beta) fal2 := by
    simpa only [wp, PostCond.noThrow, pure, FmaErr_check, Id.run, ULift.up_down,
      PredTrans.pure, PredTrans.apply, SPred.down_pure_nil]
      using hfma
        ⟨rfl, hβ, hvNum, by omega, hEven, hPClosest, hPCompat,
          hfa.2, hfx.2, hfy.2, hfbe1Can, hfr1Can, hfal1Can, hfu1Can,
          hfal1Exp, hfu1Exp, hfbe1Exp, hfr1Normal, hprodExp,
          by simpa [fu1, hfa.1, hfx.1, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hclose (a*x),
          by rw [hfu2.1, hfa.1, hfx.1, hfu1Val],
          by simpa [fal1, hfy.1, hfu2.1] using hclose (y+u2),
          by rw [hfal2.1, hfy.1, hfu2.1, hfal1Val],
          by rw [hfbe2.1, hfu1Val, hfal1Val, hfbe1Val],
          by simpa [fgat, hfbe1Val, hfr1Val] using hclose (beta1-r1),
          by simpa [fga, hfgatVal, hfbe2.1] using hclose (gat+beta2),
          by simp [P, fr1, hfa.1, hfx.1, hfy.1],
          by simp [P, fbe1, hfu1Val, hfal1Val]⟩
  have hcore : a * x + y = r1 + gamma + alpha2 := by
    simpa [hfa.1, hfx.1, hfy.1, hfr1Val, hfgaVal, hfal2.1] using hcorePff
  simpa [rnd, r1, u1, u2, alpha1, alpha2, beta1, beta2, gat, gamma] using
    ErrFMA_correct_from_core_equality beta emin prec choice a x y hcore

/-- Coq `Pff2Flocq.ErrFMA_correct_simpl`.  The nearest-even V2 hypotheses are
used to derive the four V1 non-underflow obligations before applying the
source-shaped `ErrFMA_correct` theorem. -/
theorem ErrFMA_correct_simpl (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (a x y : ℝ)
    (hEven : Even beta)
    (hprecision : 3 ≤ prec)
    (hemin : emin ≤ 0)
    (Fa : generic_format beta (FLT_exp emin prec) a)
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (U1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 4 * prec - 3) ≤ |a * x|)
    (U2 : y = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec) ≤ |y|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
    let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let alpha1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u2)
    let alpha2 := (y + u2) - alpha1
    let beta1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u1 + alpha1)
    let beta2 := (u1 + alpha1) - beta1
    let gamma := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
      (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (beta1 - r1) + beta2)
    let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (gamma + alpha2)
    let r3 := gamma + alpha2 - r2
    a * x + y = r1 + r2 + r3 := by
  classical
  let choice := fun t : Int => !(decide (2 ∣ t))
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  by_cases hprod : a * x = 0
  · simpa [choice, rnd] using
      ErrFMA_correct_simpl_of_product_eq_zero beta emin prec a x y
        (ValidRadix.valid (beta := beta)) Fy hprod
  by_cases hu2 : u2 = 0
  · simpa [choice, rnd, u1, u2] using
      ErrFMA_correct_simpl_of_u2_eq_zero beta emin prec a x y
        (ValidRadix.valid (beta := beta)) Fy (by simpa [choice, rnd, u1, u2] using hu2)
  by_cases hy : y = 0
  · simpa [choice, rnd] using
      ErrFMA_correct_simpl_of_y_eq_zero beta emin prec a x y
        (ValidRadix.valid (beta := beta)) hprecision Fa Fx U1 hy
  have hβ : 1 < beta := ValidRadix.valid
  have V1_Und1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |a * x| := by
    right
    rcases U1 with hz | hb
    · exact False.elim (hprod hz)
    · have hp := FloatSpec.Core.Raux.bpow_le beta
          (emin + 2 * prec - 1) (emin + 4 * prec - 3) hβ (by omega)
      exact le_trans (hp True.intro) hb
  have V1_Und2 := V2_Und2 beta emin prec a x y hβ hprecision Fa Fx Fy U1 U2
  have V1_Und4 := V2_Und4 beta emin prec a x y hβ hprecision Fa Fx Fy U1
  have V1_Und5 := V2_Und5 beta emin prec a x y hβ hprecision Fa Fx Fy U1 U2
  simpa [choice, rnd, u1, u2] using
    ErrFMA_correct beta emin prec choice a x y hEven hprecision hemin Fa Fx Fy
      V1_Und1
      (by simpa [choice, rnd, u1, u2] using V1_Und2 hy)
      (by simpa [choice, rnd, u1, u2] using V1_Und4 hprod)
      (by simpa [choice, rnd] using V1_Und5 hprod)

/-- Zero-product branch of Coq `ErrFmaAppr_correct`.

When `a*x = 0`, the approximate FMA residual is exactly zero: all rounded
correction terms collapse by `round(0)=0`, while the formatted input `y` is
fixed by rounding. -/
theorem ErrFmaAppr_correct_of_product_eq_zero (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hβ : 1 < beta)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (hprod : a * x = 0) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let v1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u1)
    let v2 := (y + u1) - v1
    let t1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (v1 - r1)
    let t2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u2 + v2)
    let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (t1 + t2)
    |r1 + r2 - (a * x + y)| ≤
      ((3 * (beta : ℝ) / 2 + 1 / 2) *
        FloatSpec.Core.Raux.bpow beta (2 - 2 * prec) * |r1|) := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hround0 :
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd 0 = 0 := by
    have hrnd0 : rnd (0 : ℝ) = (0 : Int) := by
      simpa [rnd] using
        (FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) (0 : Int))
    simp [FloatSpec.Core.Generic_fmt.roundR,
      FloatSpec.Core.Generic_fmt.scaled_mantissa, hrnd0]
  have hround_y :
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd y = y :=
    FloatSpec.Core.Generic_fmt.roundR_generic
      (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd)
      (x := y) hβ Fy
  dsimp
  have hrhs_nonneg :
      0 ≤ (3 * (beta : ℝ) / 2 + 1 / 2) *
        FloatSpec.Core.Raux.bpow beta (2 - 2 * prec) * |y| := by
    have hcoef_nonneg : 0 ≤ 3 * (beta : ℝ) / 2 + 1 / 2 := by
      nlinarith [le_of_lt hbpos_real]
    have hbpow_nonneg :
        0 ≤ FloatSpec.Core.Raux.bpow beta (2 - 2 * prec) := by
      exact le_of_lt (by
        simpa [FloatSpec.Core.Raux.bpow] using
          zpow_pos hbpos_real (2 - 2 * prec))
    exact mul_nonneg (mul_nonneg hcoef_nonneg hbpow_nonneg) (abs_nonneg y)
  simpa [rnd, hprod, hround0, hround_y, one_div] using hrhs_nonneg

/-- Initial format assertions in Coq `ErrFmaAppr_correct`.

The approximation proof first proves that the product error
`u2 := a*x - round(a*x)` and the addition error
`v2 := y + u1 - round(y + u1)` are in the FLT format.  The first follows from
`mult_error_FLT`, and the second from `plus_error` after `u1` is known to be a
rounded, hence formatted, value. -/
theorem ErrFmaAppr_format_u2_v2 (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hβ : 1 < beta)
    (Fa : generic_format beta (FLT_exp emin prec) a)
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (Und1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |a * x|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let v1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u1)
    let v2 := (y + u1) - v1
    generic_format beta (FLT_exp emin prec) u2 ∧
      generic_format beta (FLT_exp emin prec) v2 := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let v1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u1)
  let v2 := (y + u1) - v1
  haveI : FloatSpec.Core.Generic_fmt.Monotone_exp (FLT_exp emin prec) := by
    simpa [FLT_exp] using
      (inferInstance :
        FloatSpec.Core.Generic_fmt.Monotone_exp
          (FloatSpec.Core.FLT.FLT_exp prec emin))
  have hu2_fmt : generic_format beta (FLT_exp emin prec) u2 := by
    have hprod_err :
        generic_format beta (FLT_exp emin prec)
          (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) -
            a * x) := by
      exact mult_error_FLT (beta := beta) (prec := prec)
        (rnd := rnd) (emin := emin) (x := a) (y := x)
        hβ Fa Fx (by
          intro hprod_ne
          rcases Und1 with hzero | hbound
          · exact False.elim (hprod_ne hzero)
          · exact hbound)
    have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := FLT_exp emin prec)
      (x := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) -
        a * x)
    simp only [wp, PostCond.noThrow, PredTrans.pure, Id.run, pure, Bind.bind] at hopp
    have hneg_fmt := hopp hprod_err
    have hu2_eq :
        u2 =
          -(FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x) -
            a * x) := by
      dsimp [u2, u1]
      ring
    simpa [hu2_eq] using hneg_fmt
  have hu1_fmt : generic_format beta (FLT_exp emin prec) u1 := by
    exact FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := beta) (fexp := FLT_exp emin prec)
      (rnd := rnd) (x := a * x) hβ
  have hv2_fmt : generic_format beta (FLT_exp emin prec) v2 := by
    have hadd_err :
        generic_format beta (FLT_exp emin prec)
          (FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice)
            (y + u1) - (y + u1)) :=
      plus_error (beta := beta) (fexp := FLT_exp emin prec)
        (choice := choice) (x := y) (y := u1) hβ Fy hu1_fmt
    have hadd_err_core :
        generic_format beta (FLT_exp emin prec)
          (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
            (y + u1) - (y + u1)) := by
      simpa [FloatSpec.Calc.Round.round, FloatSpec.Compat.Scaffold.ZnearestMode,
        Znearest, rnd] using hadd_err
    have hopp := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := FLT_exp emin prec)
      (x := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
        (y + u1) - (y + u1))
    simp only [wp, PostCond.noThrow, PredTrans.pure, Id.run, pure, Bind.bind] at hopp
    have hneg_fmt := hopp hadd_err_core
    have hv2_eq :
        v2 =
          -(FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd
            (y + u1) - (y + u1)) := by
      dsimp [v2, v1]
      ring
    simpa [hv2_eq] using hneg_fmt
  exact ⟨hu2_fmt, hv2_fmt⟩

/-- Bounded Pff-side value witnesses in Coq `ErrFmaAppr_correct`.

After proving that `u2` and `v2` are formatted, the upstream proof converts
`a`, `x`, `y`, `u2`, and `v2` into bounded Pff floats.  This helper packages
the same bridge in the local Flocq-float representation used by `Pff.lean`. -/
theorem ErrFmaAppr_format_witnesses (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hβ : 1 < beta)
    (hprec : precisionNotZero prec)
    (hemin : emin ≤ 0)
    (Fa : generic_format beta (FLT_exp emin prec) a)
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (Und1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |a * x|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let bnd : Fbound := make_bound beta prec emin
    let bo : Fbound_skel := toFboundSkel bnd
    let witness := fun (value : ℝ) (f : FloatSpec.Core.Defs.FlocqFloat beta) =>
      _root_.F2R (beta:=beta) f = value ∧ Fbounded (beta:=beta) bo f
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let v1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u1)
    let v2 := (y + u1) - v1
    ∃ fa fx fy fu2 fv2 : FloatSpec.Core.Defs.FlocqFloat beta,
      witness a fa ∧ witness x fx ∧ witness y fy ∧
        witness u2 fu2 ∧ witness v2 fv2 := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let bnd : Fbound := make_bound beta prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let v1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u1)
  let v2 := (y + u1) - v1
  have hpBound : pGivesBound beta bnd prec := by
    have h := make_bound_p beta prec emin (hp := by exact hprec)
    have hv : (make_bound beta prec emin).vNum =
        Zpower_nat beta (prec.natAbs) := by
      simpa [wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound, bnd] using hv
  have hbnd_dExp : -bnd.dExp = emin := by
    have h := make_bound_Emin beta prec emin (hp := by exact hprec)
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using
        h hemin
    omega
  have hu2v2_fmt :
      generic_format beta (FLT_exp emin prec) u2 ∧
        generic_format beta (FLT_exp emin prec) v2 := by
    simpa [rnd, u1, u2, v1, v2] using
      ErrFmaAppr_format_u2_v2 (beta := beta) (emin := emin) (prec := prec)
        (choice := choice) (a := a) (x := x) (y := y)
        hβ Fa Fx Fy Und1
  have Fa_bnd : generic_format beta (FLT_exp (-bnd.dExp) prec) a := by
    simpa [hbnd_dExp] using Fa
  have Fx_bnd : generic_format beta (FLT_exp (-bnd.dExp) prec) x := by
    simpa [hbnd_dExp] using Fx
  have Fy_bnd : generic_format beta (FLT_exp (-bnd.dExp) prec) y := by
    simpa [hbnd_dExp] using Fy
  have Fu2_bnd : generic_format beta (FLT_exp (-bnd.dExp) prec) u2 := by
    simpa [hbnd_dExp] using hu2v2_fmt.1
  have Fv2_bnd : generic_format beta (FLT_exp (-bnd.dExp) prec) v2 := by
    simpa [hbnd_dExp] using hu2v2_fmt.2
  rcases (by
      have h := format_is_flocq_bounded beta bnd prec a
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨Fa_bnd, hpBound, hprec, hβ⟩) with
    ⟨fa, hfa_val, hfa_bound⟩
  rcases (by
      have h := format_is_flocq_bounded beta bnd prec x
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨Fx_bnd, hpBound, hprec, hβ⟩) with
    ⟨fx, hfx_val, hfx_bound⟩
  rcases (by
      have h := format_is_flocq_bounded beta bnd prec y
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨Fy_bnd, hpBound, hprec, hβ⟩) with
    ⟨fy, hfy_val, hfy_bound⟩
  rcases (by
      have h := format_is_flocq_bounded beta bnd prec u2
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨Fu2_bnd, hpBound, hprec, hβ⟩) with
    ⟨fu2, hfu2_val, hfu2_bound⟩
  rcases (by
      have h := format_is_flocq_bounded beta bnd prec v2
      simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
        using h ⟨Fv2_bnd, hpBound, hprec, hβ⟩) with
    ⟨fv2, hfv2_val, hfv2_bound⟩
  exact ⟨fa, fx, fy, fu2, fv2,
    ⟨hfa_val, hfa_bound⟩,
    ⟨hfx_val, hfx_bound⟩,
    ⟨hfy_val, hfy_bound⟩,
    ⟨hfu2_val, hfu2_bound⟩,
    ⟨hfv2_val, hfv2_bound⟩⟩

/-- Pff witnesses for the nearest-rounding steps in Coq `ErrFmaAppr_correct`.

The upstream proof destructs `round_N_is_pff_round` six times, for `r1`,
`u1`, `v1`, `t1`, `t2`, and `r2`.  This helper packages exactly that bridge:
each rounded real is represented by a canonical bounded Pff float that is
closest to the corresponding exact real input. -/
theorem ErrFmaAppr_round_N_witnesses (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hβ : 1 < beta)
    (hprec : precisionNotZero prec)
    (hemin : emin ≤ 0) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let bnd : Fbound := make_bound beta prec emin
    let bo : Fbound_skel := toFboundSkel bnd
    let witness := fun (input rounded : ℝ) (f : FloatSpec.Core.Defs.FlocqFloat beta) =>
      Fcanonic (beta:=beta) beta bo f ∧
        Closest (beta:=beta) bo (beta : ℝ) input f ∧
        _root_.F2R (beta:=beta) f = rounded
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let v1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u1)
    let v2 := (y + u1) - v1
    let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
    let t1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (v1 - r1)
    let t2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u2 + v2)
    let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (t1 + t2)
    ∃ fr1 fu1 fv1 ft1 ft2 fr2 : FloatSpec.Core.Defs.FlocqFloat beta,
      witness (a * x + y) r1 fr1 ∧
        witness (a * x) u1 fu1 ∧
        witness (y + u1) v1 fv1 ∧
        witness (v1 - r1) t1 ft1 ∧
        witness (u2 + v2) t2 ft2 ∧
        witness (t1 + t2) r2 fr2 := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let bnd : Fbound := make_bound beta prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let v1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u1)
  let v2 := (y + u1) - v1
  let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
  let t1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (v1 - r1)
  let t2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u2 + v2)
  let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (t1 + t2)
  have hpBound : pGivesBound beta bnd prec := by
    have h := make_bound_p beta prec emin (hp := by exact hprec)
    have hv : (make_bound beta prec emin).vNum =
        Zpower_nat beta (prec.natAbs) := by
      simpa [wp, PostCond.noThrow, make_bound_p_check, pure, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h True.intro
    simpa [pGivesBound, bnd] using hv
  have hbnd_dExp : -bnd.dExp = emin := by
    have h := make_bound_Emin beta prec emin (hp := by exact hprec)
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using
        h hemin
    omega
  rcases (round_N_is_pff_round (beta := beta) (b := bnd) (p := prec)
      (choice := choice) (r := a * x + y)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨fr1, hfr1_can, hfr1_closest, hfr1_val⟩
  rcases (round_N_is_pff_round (beta := beta) (b := bnd) (p := prec)
      (choice := choice) (r := a * x)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨fu1, hfu1_can, hfu1_closest, hfu1_val⟩
  rcases (round_N_is_pff_round (beta := beta) (b := bnd) (p := prec)
      (choice := choice) (r := y + u1)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨fv1, hfv1_can, hfv1_closest, hfv1_val⟩
  rcases (round_N_is_pff_round (beta := beta) (b := bnd) (p := prec)
      (choice := choice) (r := v1 - r1)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨ft1, hft1_can, hft1_closest, hft1_val⟩
  rcases (round_N_is_pff_round (beta := beta) (b := bnd) (p := prec)
      (choice := choice) (r := u2 + v2)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨ft2, hft2_can, hft2_closest, hft2_val⟩
  rcases (round_N_is_pff_round (beta := beta) (b := bnd) (p := prec)
      (choice := choice) (r := t1 + t2)
      (hpBound := hpBound) (hprec := hprec) (hbeta := hβ)) with
    ⟨fr2, hfr2_can, hfr2_closest, hfr2_val⟩
  refine ⟨fr1, fu1, fv1, ft1, ft2, fr2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hfr1_can, hfr1_closest, by simpa [r1, rnd, hbnd_dExp] using hfr1_val⟩
  · exact ⟨hfu1_can, hfu1_closest, by simpa [u1, rnd, hbnd_dExp] using hfu1_val⟩
  · exact ⟨hfv1_can, hfv1_closest, by simpa [v1, rnd, hbnd_dExp] using hfv1_val⟩
  · exact ⟨hft1_can, hft1_closest, by simpa [t1, rnd, hbnd_dExp] using hft1_val⟩
  · exact ⟨hft2_can, hft2_closest, by simpa [t2, rnd, hbnd_dExp] using hft2_val⟩
  · exact ⟨hfr2_can, hfr2_closest, by simpa [r2, rnd, hbnd_dExp] using hfr2_val⟩

/-- Checked wrapper-side payload for Coq `ErrFmaAppr_correct`.

This restores a nontrivial public theorem at the upstream name without claiming
the still-missing lower Pff `ErrFmaApprox` error-bound payload.  It proves the
zero-product branch and packages the formatted residuals, bounded value
witnesses, and six nearest-rounding witnesses that the Coq proof establishes
before invoking that lower payload. -/
theorem ErrFmaAppr_correct_from_zero_branch_and_rounding_witnesses
    (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hβ : 1 < beta)
    (hprec : precisionNotZero prec)
    (hemin : emin ≤ 0)
    (Fa : generic_format beta (FLT_exp emin prec) a)
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (Und1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |a * x|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let bnd : Fbound := make_bound beta prec emin
    let bo : Fbound_skel := toFboundSkel bnd
    let valueWitness := fun (value : ℝ) (f : FloatSpec.Core.Defs.FlocqFloat beta) =>
      _root_.F2R (beta:=beta) f = value ∧ Fbounded (beta:=beta) bo f
    let roundWitness := fun (input rounded : ℝ)
        (f : FloatSpec.Core.Defs.FlocqFloat beta) =>
      Fcanonic (beta:=beta) beta bo f ∧
        Closest (beta:=beta) bo (beta : ℝ) input f ∧
        _root_.F2R (beta:=beta) f = rounded
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let v1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u1)
    let v2 := (y + u1) - v1
    let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
    let t1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (v1 - r1)
    let t2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u2 + v2)
    let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (t1 + t2)
    (a * x = 0 →
      |r1 + r2 - (a * x + y)| ≤
        ((3 * (beta : ℝ) / 2 + 1 / 2) *
          FloatSpec.Core.Raux.bpow beta (2 - 2 * prec) * |r1|)) ∧
      generic_format beta (FLT_exp emin prec) u2 ∧
      generic_format beta (FLT_exp emin prec) v2 ∧
      (∃ fa fx fy fu2 fv2 : FloatSpec.Core.Defs.FlocqFloat beta,
        valueWitness a fa ∧ valueWitness x fx ∧ valueWitness y fy ∧
          valueWitness u2 fu2 ∧ valueWitness v2 fv2) ∧
      (∃ fr1 fu1 fv1 ft1 ft2 fr2 : FloatSpec.Core.Defs.FlocqFloat beta,
        roundWitness (a * x + y) r1 fr1 ∧
          roundWitness (a * x) u1 fu1 ∧
          roundWitness (y + u1) v1 fv1 ∧
          roundWitness (v1 - r1) t1 ft1 ∧
          roundWitness (u2 + v2) t2 ft2 ∧
          roundWitness (t1 + t2) r2 fr2) := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let bnd : Fbound := make_bound beta prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let v1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u1)
  let v2 := (y + u1) - v1
  let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
  let t1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (v1 - r1)
  let t2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u2 + v2)
  let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (t1 + t2)
  have hzero :
      a * x = 0 →
        |r1 + r2 - (a * x + y)| ≤
          ((3 * (beta : ℝ) / 2 + 1 / 2) *
            FloatSpec.Core.Raux.bpow beta (2 - 2 * prec) * |r1|) := by
    intro hprod
    simpa [rnd, r1, u1, u2, v1, v2, t1, t2, r2] using
      ErrFmaAppr_correct_of_product_eq_zero
        (beta := beta) (emin := emin) (prec := prec)
        (choice := choice) (a := a) (x := x) (y := y)
        hβ Fy hprod
  have hformats :
      generic_format beta (FLT_exp emin prec) u2 ∧
        generic_format beta (FLT_exp emin prec) v2 := by
    simpa [rnd, u1, u2, v1, v2] using
      ErrFmaAppr_format_u2_v2
        (beta := beta) (emin := emin) (prec := prec)
        (choice := choice) (a := a) (x := x) (y := y)
        hβ Fa Fx Fy Und1
  have hvalues :
      ∃ fa fx fy fu2 fv2 : FloatSpec.Core.Defs.FlocqFloat beta,
        (_root_.F2R (beta:=beta) fa = a ∧ Fbounded (beta:=beta) bo fa) ∧
          (_root_.F2R (beta:=beta) fx = x ∧ Fbounded (beta:=beta) bo fx) ∧
          (_root_.F2R (beta:=beta) fy = y ∧ Fbounded (beta:=beta) bo fy) ∧
          (_root_.F2R (beta:=beta) fu2 = u2 ∧ Fbounded (beta:=beta) bo fu2) ∧
          (_root_.F2R (beta:=beta) fv2 = v2 ∧ Fbounded (beta:=beta) bo fv2) := by
    simpa [rnd, bnd, bo, u1, u2, v1, v2] using
      ErrFmaAppr_format_witnesses
        (beta := beta) (emin := emin) (prec := prec)
        (choice := choice) (a := a) (x := x) (y := y)
        hβ hprec hemin Fa Fx Fy Und1
  have hrounds :
      ∃ fr1 fu1 fv1 ft1 ft2 fr2 : FloatSpec.Core.Defs.FlocqFloat beta,
        (Fcanonic (beta:=beta) beta bo fr1 ∧
          Closest (beta:=beta) bo (beta : ℝ) (a * x + y) fr1 ∧
          _root_.F2R (beta:=beta) fr1 = r1) ∧
        (Fcanonic (beta:=beta) beta bo fu1 ∧
          Closest (beta:=beta) bo (beta : ℝ) (a * x) fu1 ∧
          _root_.F2R (beta:=beta) fu1 = u1) ∧
        (Fcanonic (beta:=beta) beta bo fv1 ∧
          Closest (beta:=beta) bo (beta : ℝ) (y + u1) fv1 ∧
          _root_.F2R (beta:=beta) fv1 = v1) ∧
        (Fcanonic (beta:=beta) beta bo ft1 ∧
          Closest (beta:=beta) bo (beta : ℝ) (v1 - r1) ft1 ∧
          _root_.F2R (beta:=beta) ft1 = t1) ∧
        (Fcanonic (beta:=beta) beta bo ft2 ∧
          Closest (beta:=beta) bo (beta : ℝ) (u2 + v2) ft2 ∧
          _root_.F2R (beta:=beta) ft2 = t2) ∧
        (Fcanonic (beta:=beta) beta bo fr2 ∧
          Closest (beta:=beta) bo (beta : ℝ) (t1 + t2) fr2 ∧
          _root_.F2R (beta:=beta) fr2 = r2) := by
    simpa [rnd, bnd, bo, u1, u2, v1, v2, r1, t1, t2, r2] using
      ErrFmaAppr_round_N_witnesses
        (beta := beta) (emin := emin) (prec := prec)
        (choice := choice) (a := a) (x := x) (y := y)
        hβ hprec hemin
  rcases hvalues with
    ⟨fa, fx, fy, fu2, fv2, hfa, hfx, hfy, hfu2, hfv2⟩
  rcases hrounds with
    ⟨fr1, fu1, fv1, ft1, ft2, fr2, hfr1, hfu1, hfv1, hft1, hft2, hfr2⟩
  exact ⟨hzero, hformats.1, hformats.2,
    ⟨fa, fx, fy, fu2, fv2,
      hfa, hfx, hfy, hfu2, hfv2⟩,
    ⟨fr1, fu1, fv1, ft1, ft2, fr2, hfr1, hfu1, hfv1, hft1, hft2, hfr2⟩⟩

/-- Coq `Pff2Flocq.ErrFmaAppr_correct`.  The format and rounding floats are
constructed internally; the five source non-underflow hypotheses are used
only to establish the normal-or-zero premises of Pff's `ErrFmaApprox`. -/
theorem ErrFmaAppr_correct
    (beta emin prec : Int) [ValidRadix beta] [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ)
    (hprecision : 4 ≤ prec)
    (hemin : emin ≤ 0)
    (Fa : generic_format beta (FLT_exp emin prec) a)
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (Und1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |a * x|)
    (Und2 :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
      let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
      let v1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u1)
      v1 = 0 ∨ FloatSpec.Core.Raux.bpow beta (emin + prec - 1) ≤ |v1|)
    (Und3 :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
      let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
      r1 = 0 ∨ FloatSpec.Core.Raux.bpow beta (emin + prec - 1) ≤ |r1|)
    (Und4 :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
      let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
      let u2 := a * x - u1
      let v1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u1)
      let v2 := y + u1 - v1
      let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
      let t1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (v1 - r1)
      let t2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u2 + v2)
      let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (t1 + t2)
      r2 = 0 ∨ FloatSpec.Core.Raux.bpow beta (emin + prec - 1) ≤ |r2|)
    (Und5 :
      let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
      let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
      let u2 := a * x - u1
      let v1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u1)
      let v2 := y + u1 - v1
      let t2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u2 + v2)
      t2 = 0 ∨ FloatSpec.Core.Raux.bpow beta (emin + prec - 1) ≤ |t2|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
    let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
    let u2 := a * x - u1
    let v1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u1)
    let v2 := y + u1 - v1
    let t1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (v1 - r1)
    let t2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u2 + v2)
    let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (t1 + t2)
    |r1 + r2 - (a * x + y)| ≤
      (3 * (beta : ℝ) / 2 + 1 / 2) *
        FloatSpec.Core.Raux.bpow beta (2 - 2 * prec) * |r1| := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let u1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x)
  let u2 := a * x - u1
  let v1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (y + u1)
  let v2 := y + u1 - v1
  let r1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (a * x + y)
  let t1 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (v1 - r1)
  let t2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (u2 + v2)
  let r2 := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (t1 + t2)
  have hβ : 1 < beta := ValidRadix.valid
  rcases Und1 with hprod | hprodLower
  · simpa [rnd, u1, u2, v1, v2, r1, t1, t2, r2] using
      ErrFmaAppr_correct_of_product_eq_zero beta emin prec choice a x y hβ Fy hprod
  have Und1 : a * x = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |a * x| :=
    Or.inr hprodLower
  have hprec : precisionNotZero prec := by unfold precisionNotZero; omega
  let bnd : Fbound := make_bound beta prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  have hpBound : pGivesBound beta bnd prec := by
    have h := make_bound_p beta prec emin
    have hv : bnd.vNum = Zpower_nat beta prec.natAbs := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound] using hv
  have hbndExp : -bnd.dExp = emin := by
    have h := make_bound_Emin beta prec emin
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using h hemin
    omega
  have hboExp : -bo.dExp = emin := by simpa [bo] using hbndExp
  have hprecNonneg : 0 ≤ prec := by omega
  have habsPrec : prec.natAbs = prec.toNat := by omega
  have hprecNat : (prec.toNat : Int) = prec := Int.toNat_of_nonneg hprecNonneg
  have hprecisionNat : 4 ≤ prec.toNat := by omega
  have hvNum : bo.vNum = Zpower_nat beta prec.toNat := by
    simpa [bo, pGivesBound, habsPrec] using hpBound
  rcases ErrFmaAppr_format_witnesses beta emin prec choice a x y hβ hprec hemin
      Fa Fx Fy Und1 with
    ⟨fa, fx, fy, fu2, fv2, hfa, hfx, hfy, hfu2, hfv2⟩
  rcases ErrFmaAppr_round_N_witnesses beta emin prec choice a x y hβ hprec hemin with
    ⟨fr1, fu1, fv1, ft1, ft2, fr2, hfr1, hfu1, hfv1, hft1, hft2, hfr2⟩
  have hnormalOrZero (z : ℝ) (f : FloatSpec.Core.Defs.FlocqFloat beta)
      (hcan : Fcanonic (beta:=beta) beta bo f)
      (hval : _root_.F2R (beta:=beta) f = z)
      (hUnd : z = 0 ∨
        FloatSpec.Core.Raux.bpow beta (emin + prec - 1) ≤ |z|) :
      Fnormal (beta:=beta) beta bo f ∨ _root_.F2R (beta:=beta) f = 0 := by
    rcases hUnd with hz | hm
    · right; simpa [hval] using hz
    · left
      have h := CanonicGeNormal beta bnd prec f
      simpa [wp, PostCond.noThrow, CanonicGeNormal_check, pure,
        PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, PFnormal, bo] using h
        ⟨by simpa [bo] using hcan, hpBound, hprec,
          by simpa [hval, hbndExp, FloatSpec.Core.Raux.bpow] using hm, hβ⟩
  have hfu1Und : u1 = 0 ∨
      FloatSpec.Core.Raux.bpow beta (emin + prec - 1) ≤ |u1| := by
    rcases V1_Und3 beta emin prec choice a x y hβ (by omega) Fa Fx Fy Und1 with hz | hm
    · exact Or.inl (by simpa [rnd, u1] using hz)
    · right
      have hp := FloatSpec.Core.Raux.bpow_le beta
        (emin + prec - 1) (emin + prec) hβ (by omega)
      have hp' : FloatSpec.Core.Raux.bpow beta (emin + prec - 1) ≤
          FloatSpec.Core.Raux.bpow beta (emin + prec) := by
        change (beta : ℝ) ^ (emin + prec - 1) ≤ (beta : ℝ) ^ (emin + prec)
        simpa [wp, PostCond.noThrow, pure,
          FloatSpec.Core.Raux.bpow_le_check, PredTrans.pure,
          PredTrans.apply, SPred.down_pure_nil] using hp True.intro
      exact le_trans
        hp'
        (by simpa [rnd, u1] using hm)
  have hfu1NZ := hnormalOrZero u1 fu1 hfu1.1
      (by simpa [rnd, u1] using hfu1.2.2) hfu1Und
  have hfv1NZ := hnormalOrZero v1 fv1 hfv1.1
      (by simpa [rnd, u1, v1] using hfv1.2.2) (by simpa [rnd, u1, v1] using Und2)
  have hfr1NZ := hnormalOrZero r1 fr1 hfr1.1
      (by simpa [rnd, r1] using hfr1.2.2) (by simpa [rnd, r1] using Und3)
  have hfr2NZ := hnormalOrZero r2 fr2 hfr2.1
      (by simpa [rnd, u1, u2, v1, v2, r1, t1, t2, r2] using hfr2.2.2)
      (by simpa [rnd, u1, u2, v1, v2, r1, t1, t2, r2] using Und4)
  have hft2NZ := hnormalOrZero t2 ft2 hft2.1
      (by simpa [rnd, u1, u2, v1, v2, t2] using hft2.2.2)
      (by simpa [rnd, u1, u2, v1, v2, t2] using Und5)
  have hprodExp : -bo.dExp ≤ fa.Fexp + fx.Fexp := by
    have h := underf_mult_aux' (beta:=beta) bo prec fa fx
    simpa only [wp, PostCond.noThrow, pure, underf_mult_aux'_check, Id.run, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h
      ⟨hβ, by omega, by simpa [bo, pGivesBound] using hpBound, hfa.2, hfx.2,
        by simpa [hboExp, hfa.1, hfx.1] using hprodLower⟩
  have hcore := ErrFmaApprox bo beta prec.toNat
    fa fx fy fu1 fu2 fv1 fv2 fr1 ft1 ft2 fr2 rfl hβ hvNum
      hprecisionNat hfy.2 hfa.2 hfx.2 hfu1NZ hfv1NZ hfr1NZ hfr2NZ
      hft2NZ hprodExp
      (by simpa [bo, hfa.1, hfx.1, hfy.1] using hfr1.2.1)
      (by simpa [bo, hfa.1, hfx.1] using hfu1.2.1)
      (by rw [hfu2.1, hfa.1, hfx.1, hfu1.2.2])
      (by simpa [bo, hfu1.2.2, hfy.1, add_comm] using hfv1.2.1)
      (by rw [hfv2.1, hfy.1, hfu1.2.2, hfv1.2.2]; ring)
      (by simpa [bo, hfv1.2.2, hfr1.2.2] using hft1.2.1)
      (by simpa [bo, hfu2.1, hfv2.1] using hft2.2.1)
      (by simpa [bo, hft1.2.2, hft2.2.2] using hfr2.2.1)
  simpa [rnd, u1, u2, v1, v2, r1, t1, t2, r2, hfa.1, hfx.1, hfy.1,
    hfr1.2.2, hfr2.2.2, hprecNat, FloatSpec.Core.Raux.bpow] using hcore

/-
Coq theorem: `Axpy`

The public Flocq theorem concludes that the computed value is either the
directed down or directed up rounding of `y + a*x`.  Upstream obtains the
intermediate `MinOrMax` fact from Pff's `Axpy_opt`; this helper factors only
the final Pff-to-Flocq conversion step.
-/

noncomputable def Axpy_from_min_or_max_check (emin prec : Int)
    (a x y tv : ℝ) : Unit :=
  ()

/-- Final wrapper step of Coq `Axpy`.

If a bounded Pff float representing `tv` is already known to be either the
lower or upper extremal rounded value of `y + a*x`, then `tv` is the concrete
Flocq down- or up-rounding of `y + a*x`. The missing upstream payload remains
the lower Pff theorem `Axpy_opt`, which supplies the `isMin ∨ isMax` premise. -/
theorem Axpy_from_min_or_max (emin prec : Int) [Prec_gt_0 prec]
    (a x y tv : ℝ) :
    ⦃⌜precisionNotZero prec ∧ emin ≤ 0 ∧
        ∃ ftv : FloatSpec.Core.Defs.FlocqFloat 2,
          _root_.F2R (beta:=2) ftv = tv ∧
          (isMin (beta:=2) (toFboundSkel (make_bound 2 prec emin)) 2
              (y + a * x) ftv ∨
            isMax (beta:=2) (toFboundSkel (make_bound 2 prec emin)) 2
              (y + a * x) ftv)⌝⦄
    (pure (Axpy_from_min_or_max_check emin prec a x y tv) : Id Unit)
    ⦃⇓_ => ⌜tv =
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
            FloatSpec.Core.Generic_fmt.rnd_floor (y + a * x) ∨
        tv =
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
            FloatSpec.Core.Generic_fmt.rnd_ceil (y + a * x)⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hprec, hemin, ftv, hftv_val, hMinOrMax⟩
  simp only [wp, PostCond.noThrow, pure, Axpy_from_min_or_max_check,
    Id.run, ULift.up_down]
  let bnd : Fbound := make_bound 2 prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  have hβ : (1 : Int) < 2 := by decide
  have hpBound : pGivesBound 2 bnd prec := by
    have h := make_bound_p 2 prec emin (hp := by exact hprec)
    have hv : (make_bound 2 prec emin).vNum =
        Zpower_nat 2 (prec.natAbs) := by
      simpa [wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound, bnd] using hv
  have hbnd_dExp : -bnd.dExp = emin := by
    have h := make_bound_Emin 2 prec emin (hp := by exact hprec)
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using
        h hemin
    omega
  have hprec_pos : 0 < prec := lt_trans Int.zero_lt_one hprec
  have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos
  have hp_abs_toNat : prec.natAbs = prec.toNat := by
    apply Nat.cast_injective (R := Int)
    rw [Int.natAbs_of_nonneg hprec_nonneg, Int.toNat_of_nonneg hprec_nonneg]
  have hpBound_toNat : bnd.vNum = Zpower_nat 2 prec.toNat := by
    unfold pGivesBound at hpBound
    calc
      bnd.vNum = Zpower_nat 2 (prec.natAbs) := hpBound
      _ = Zpower_nat 2 prec.toNat := by rw [hp_abs_toNat]
  have hvnum : bo.vNum = Zpower_nat 2 prec.toNat := by
    unfold bo toFboundSkel
    exact hpBound_toNat
  have hMinUnique :
      ∀ (r : ℝ) (p q : FloatSpec.Core.Defs.FlocqFloat 2),
        isMin (beta:=2) bo 2 r p →
        isMin (beta:=2) bo 2 r q →
        _root_.F2R (beta:=2) p = _root_.F2R (beta:=2) q := by
    have h := MinUniqueP (beta:=2) bo 2
    simpa only [wp, PostCond.noThrow, pure, MinUniqueP_check,
      Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h True.intro
  have hMaxUnique :
      ∀ (r : ℝ) (p q : FloatSpec.Core.Defs.FlocqFloat 2),
        isMax (beta:=2) bo 2 r p →
        isMax (beta:=2) bo 2 r q →
        _root_.F2R (beta:=2) p = _root_.F2R (beta:=2) q := by
    have h := MaxUniqueP (beta:=2) bo 2
    simpa only [wp, PostCond.noThrow, pure, MaxUniqueP_check,
      Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h True.intro
  rcases hMinOrMax with hMin | hMax
  · left
    have hRndMin :
        isMin (beta:=2) bo 2 (y + a * x)
          (RND_Min (beta:=2) bo 2 prec (y + a * x)) := by
      have h := RND_Min_correct (beta:=2) bo 2 prec (y + a * x)
      simpa only [wp, PostCond.noThrow, pure, RND_Min_correct_check,
        Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨rfl, hβ, hprec, hvnum⟩
    have hval_eq :
        _root_.F2R (beta:=2) ftv =
          _root_.F2R (beta:=2) (RND_Min (beta:=2) bo 2 prec (y + a * x)) :=
      hMinUnique (y + a * x) ftv
        (RND_Min (beta:=2) bo 2 prec (y + a * x)) (by simpa [bo, bnd] using hMin) hRndMin
    have hround := pff_round_DN_is_round 2 bnd prec (y + a * x)
      hpBound hprec hβ
    calc
      tv = _root_.F2R (beta:=2) ftv := hftv_val.symm
      _ = _root_.F2R (beta:=2) (RND_Min (beta:=2) bo 2 prec (y + a * x)) := hval_eq
      _ = FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-bnd.dExp) prec)
            FloatSpec.Core.Generic_fmt.rnd_floor (y + a * x) := by
              simpa [bo] using hround
      _ = FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
            FloatSpec.Core.Generic_fmt.rnd_floor (y + a * x) := by
              rw [hbnd_dExp]
  · right
    have hRndMax :
        isMax (beta:=2) bo 2 (y + a * x)
          (RND_Max (beta:=2) bo 2 prec (y + a * x)) := by
      have h := RND_Max_correct (beta:=2) bo 2 prec (y + a * x)
      simpa only [wp, PostCond.noThrow, pure, RND_Max_correct_check,
        Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h ⟨rfl, hβ, hprec, hvnum⟩
    have hval_eq :
        _root_.F2R (beta:=2) ftv =
          _root_.F2R (beta:=2) (RND_Max (beta:=2) bo 2 prec (y + a * x)) :=
      hMaxUnique (y + a * x) ftv
        (RND_Max (beta:=2) bo 2 prec (y + a * x)) (by simpa [bo, bnd] using hMax) hRndMax
    have hround := pff_round_UP_is_round 2 bnd prec (y + a * x)
      hpBound hprec hβ
    calc
      tv = _root_.F2R (beta:=2) ftv := hftv_val.symm
      _ = _root_.F2R (beta:=2) (RND_Max (beta:=2) bo 2 prec (y + a * x)) := hval_eq
      _ = FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-bnd.dExp) prec)
            FloatSpec.Core.Generic_fmt.rnd_ceil (y + a * x) := by
              simpa [bo] using hround
      _ = FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
            FloatSpec.Core.Generic_fmt.rnd_ceil (y + a * x) := by
              rw [hbnd_dExp]

/-- Coq theorem: `Axpy`.

The upstream proof builds the Pff witnesses for `ta`, `tx`, `ty`, the rounded
product, and the final rounded value, then calls Pff's `Axpy_opt` to obtain the
`MinOrMax` payload.  This public wrapper records the final checked conversion
from that lower Pff payload to the Flocq down/up rounding disjunction. -/
theorem Axpy_from_final_min_or_max_payload (emin prec : Int) [Prec_gt_0 prec]
    (a x y tv : ℝ) (ftv : FloatSpec.Core.Defs.FlocqFloat 2)
    (hprec : precisionNotZero prec)
    (hemin : emin ≤ 0)
    (hftv_val : _root_.F2R (beta:=2) ftv = tv)
    (hMinOrMax :
      MinOrMax (beta:=2) (toFboundSkel (make_bound 2 prec emin)) 2
        (y + a * x) ftv) :
    ⦃⌜True⌝⦄
    (pure (Axpy_from_min_or_max_check emin prec a x y tv) : Id Unit)
    ⦃⇓_ => ⌜tv =
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
            FloatSpec.Core.Generic_fmt.rnd_floor (y + a * x) ∨
        tv =
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
            FloatSpec.Core.Generic_fmt.rnd_ceil (y + a * x)⌝⦄ := by
  intro _
  have hbridge := Axpy_from_min_or_max (emin := emin) (prec := prec)
    (a := a) (x := x) (y := y) (tv := tv)
  simpa [wp, PostCond.noThrow, pure, Axpy_from_min_or_max_check, Id.run,
    MinOrMax] using
    hbridge ⟨hprec, hemin, ftv, hftv_val, by
      simpa [MinOrMax] using hMinOrMax⟩

/-- Coq `Pff2Flocq.Axpy`: the translated algorithm constructs its Pff
witnesses and invokes `Pff.Axpy_opt`; no `MinOrMax` payload is exposed. -/
theorem Axpy (emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y ta tx ty : ℝ)
    (hprecision : 1 < prec)
    (hemin : emin ≤ 0)
    (Fta : generic_format 2 (FLT_exp emin prec) ta)
    (Ftx : generic_format 2 (FLT_exp emin prec) tx)
    (Fty : generic_format 2 (FLT_exp emin prec) ty)
    (H1 : (5 + 4 * FloatSpec.Core.Raux.bpow 2 (-prec)) /
        (1 - FloatSpec.Core.Raux.bpow 2 (-prec)) *
        (|ta * tx| + FloatSpec.Core.Raux.bpow 2 (emin - 1)) ≤ |ty|)
    (H2 : |y - ty| + |a * x - ta * tx| ≤
        FloatSpec.Core.Raux.bpow 2 (-prec - 2) *
            (1 - FloatSpec.Core.Raux.bpow 2 (1 - prec)) * |ty| -
          FloatSpec.Core.Raux.bpow 2 (-prec - 2) * |ta * tx| -
          FloatSpec.Core.Raux.bpow 2 (emin - 2)) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
    let tv := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
      (ty + FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (ta * tx))
    tv = FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
        FloatSpec.Core.Generic_fmt.rnd_floor (y + a * x) ∨
      tv = FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
        FloatSpec.Core.Generic_fmt.rnd_ceil (y + a * x) := by
  classical
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let g := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (ta * tx)
  let tv := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd (ty + g)
  have hβ : (1 : Int) < 2 := by decide
  have hprec : precisionNotZero prec := hprecision
  have hprecPos : 0 ≤ prec := by omega
  have hprecNat : (prec.toNat : Int) = prec := Int.toNat_of_nonneg hprecPos
  have habsPrec : prec.natAbs = prec.toNat := by omega
  let bnd : Fbound := make_bound 2 prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  have hpBound : pGivesBound 2 bnd prec := by
    have h := make_bound_p 2 prec emin
    have hv : bnd.vNum = Zpower_nat 2 prec.natAbs := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_p_check, pure] using h True.intro
    simpa [pGivesBound] using hv
  have hvNum : bo.vNum = Zpower_nat 2 prec.toNat := by
    simpa [bo, pGivesBound, habsPrec] using hpBound
  have hbndExp : -bnd.dExp = emin := by
    have h := make_bound_Emin 2 prec emin
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using h hemin
    omega
  have hboExp : -bo.dExp = emin := by simpa [bo] using hbndExp
  have hformat (z : ℝ) (hz : generic_format 2 (FLT_exp emin prec) z) :
      ∃ f : FloatSpec.Core.Defs.FlocqFloat 2,
        _root_.F2R (beta:=2) f = z ∧ Fbounded (beta:=2) bo f := by
    have hz' : generic_format 2 (FLT_exp (-bnd.dExp) prec) z := by
      simpa [hbndExp] using hz
    rcases (by
        have h := format_is_flocq_bounded 2 bnd prec z
        simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
          using h ⟨hz', hpBound, hprec, hβ⟩) with ⟨f, hfVal, hfBound⟩
    exact ⟨f, hfVal, by simpa [bo, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hfBound⟩
  rcases hformat ta Fta with ⟨fta, hftaVal, hftaBound⟩
  rcases hformat tx Ftx with ⟨ftx, hftxVal, hftxBound⟩
  rcases hformat ty Fty with ⟨fty, hftyVal, hftyBound⟩
  rcases round_N_is_pff_round (beta:=2) (b:=bnd) (p:=prec)
      (choice:=choice) (r:=ta * tx) hpBound hprec hβ with
    ⟨fg, hfgCan, hfgClose, hfgVal⟩
  have hfgAlg : _root_.F2R (beta:=2) fg = g := by
    simpa [g, rnd, hbndExp] using hfgVal
  rcases round_N_is_pff_round (beta:=2) (b:=bnd) (p:=prec)
      (choice:=choice) (r:=ty + g) hpBound hprec hβ with
    ⟨ftv, hftvCan, hftvClose, hftvVal⟩
  have hftvAlg : _root_.F2R (beta:=2) ftv = tv := by
    simpa [tv, rnd, hbndExp] using hftvVal
  have hproductClose : Closest (beta:=2) bo (2 : ℝ)
      (_root_.F2R (beta:=2) fta * _root_.F2R (beta:=2) ftx) fg := by
    simpa [bo, hftaVal, hftxVal] using hfgClose
  have hsumClose : Closest (beta:=2) bo (2 : ℝ)
      (_root_.F2R (beta:=2) fg + _root_.F2R (beta:=2) fty) ftv := by
    simpa [bo, hfgAlg, hftyVal, add_comm] using hftvClose
  have hlarge :
      (5 + 4 * (2 : ℝ) ^ (-(prec.toNat : Int))) *
          (1 - (2 : ℝ) ^ (-(prec.toNat : Int)))⁻¹ *
          (|_root_.F2R (beta:=2) fta * _root_.F2R (beta:=2) ftx| +
            (2 : ℝ) ^ (-bo.dExp - 1)) ≤ |_root_.F2R (beta:=2) fty| := by
    simpa [hprecNat, hftaVal, hftxVal, hftyVal, hboExp,
      FloatSpec.Core.Raux.bpow, div_eq_mul_inv, mul_assoc] using H1
  have herror :
      |y - _root_.F2R (beta:=2) fty| +
          |a * x - _root_.F2R (beta:=2) fta * _root_.F2R (beta:=2) ftx| ≤
        (2 : ℝ) ^ (-(prec.toNat : Int) - 2) *
            (1 - (2 : ℝ) ^ (1 - (prec.toNat : Int))) *
            |_root_.F2R (beta:=2) fty| -
          (2 : ℝ) ^ (-(prec.toNat : Int) - 2) *
            |_root_.F2R (beta:=2) fta * _root_.F2R (beta:=2) ftx| -
          (2 : ℝ) ^ (-bo.dExp - 2) := by
    simpa [hprecNat, hftaVal, hftxVal, hftyVal, hboExp,
      FloatSpec.Core.Raux.bpow] using H2
  have hMinMax : MinOrMax (beta:=2) bo 2 (a * x + y) ftv := by
    have h := Axpy_opt (beta:=2) bo prec.toNat fta ftx fty fg ftv a x y
    simpa only [wp, PostCond.noThrow, pure, Axpy_opt_check,
      Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h
      ⟨hftaBound, hftxBound, hftyBound, hfgClose.1, hftvClose.1,
        hproductClose, hsumClose, by simpa [bo] using hftvCan,
        by simpa [bo] using hfgCan, hlarge, herror, rfl, by omega, hvNum⟩
  have hbridge := Axpy_from_min_or_max (emin:=emin) (prec:=prec)
    (a:=a) (x:=x) (y:=y) (tv:=tv)
  simpa [wp, PostCond.noThrow, pure, Axpy_from_min_or_max_check, Id.run,
    g, tv] using
    hbridge ⟨hprec, hemin, ftv, hftvAlg, by
      simpa [MinOrMax, bo, bnd, add_comm] using hMinMax⟩

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
    Here `round_flt := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode`. -/
theorem format_dp (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜generic_format 2 (FLT_exp emin prec) a ∧
        generic_format 2 (FLT_exp emin prec) b ∧
        generic_format 2 (FLT_exp emin prec) c ∧
        (b * b ≠ 0 → (2 : ℝ) ^ (emin + 3 * prec) ≤ |b * b|)⌝⦄
    (pure (format_dp_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode
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
    Here `round_flt := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode`. -/
theorem format_dq (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜generic_format 2 (FLT_exp emin prec) a ∧
        generic_format 2 (FLT_exp emin prec) b ∧
        generic_format 2 (FLT_exp emin prec) c ∧
        (a * c ≠ 0 → (2 : ℝ) ^ (emin + 3 * prec) ≤ |a * c|)⌝⦄
    (pure (format_dq_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode
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
    Here `round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode`. -/
theorem format_d_discri1 (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜True⌝⦄
    (pure (format_d_discri1_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode
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
      FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode (b * b) +
        FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode (a * c) ≤
        3 * |FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode (b * b) -
          FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode (a * c)|
  · rw [ite_eq_left hcond]
    simpa [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode] using
      FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := 2) (fexp := FLT_exp emin prec)
      (rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t))))
      (x := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode (b * b) -
        FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode (a * c)) (by decide)
  · rw [ite_eq_right hcond]
    simpa [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode] using
      FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := 2) (fexp := FLT_exp emin prec)
      (rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t))))
      (x :=
        FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode
          (FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode (b * b) -
            FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode (a * c)) +
        FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode
          ((b * b -
              FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode (b * b)) -
            (a * c -
              FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode (a * c)))) (by decide)

/-!
Coq lemma: `format_d_discri2`

A companion to `format_d_discri1` for the executable-test branch.  Here the
comparison itself uses the rounded values `round_flt (p+q)` and
`round_flt (3*|round_flt (p-q)|)`.
-/

noncomputable def format_d_discri2_check (emin prec : Int)
    (a b c : ℝ) : Unit :=
  ()

/-- Coq: `format_d_discri2` — with local definitions
    `p := round_flt (b*b)`, `q := round_flt (a*c)`, `dp := b*b - p`,
    `dq := a*c - q`, and
    `d := if round_flt (p+q) ≤ round_flt (3*|round_flt (p-q)|)
          then round_flt (p - q)
          else round_flt (round_flt (p - q) + round_flt (dp - dq))`,
    the value `d` is representable in `generic_format 2 (FLT_exp emin prec)`.
    Here `round_flt := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec)
    FloatSpec.Calc.Round.nearestEvenMode`. -/
theorem format_d_discri2 (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜True⌝⦄
    (pure (format_d_discri2_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode
            let p := round_flt (b * b)
            let q := round_flt (a * c)
            let dp := b * b - p
            let dq := a * c - q
            let d := if (round_flt (p + q) ≤
                         round_flt (3 * |round_flt (p - q)|))
                     then round_flt (p - q)
                     else round_flt (round_flt (p - q) + round_flt (dp - dq))
            generic_format 2 (FLT_exp emin prec) d⌝⦄ := by
  apply Std.Do.Triple.pure
  intro _
  dsimp
  by_cases hcond :
      FloatSpec.Calc.Round.round 2 (FLT_exp emin prec)
          FloatSpec.Calc.Round.nearestEvenMode
          (FloatSpec.Calc.Round.round 2 (FLT_exp emin prec)
              FloatSpec.Calc.Round.nearestEvenMode (b * b) +
            FloatSpec.Calc.Round.round 2 (FLT_exp emin prec)
              FloatSpec.Calc.Round.nearestEvenMode (a * c)) ≤
        FloatSpec.Calc.Round.round 2 (FLT_exp emin prec)
          FloatSpec.Calc.Round.nearestEvenMode
          (3 * |FloatSpec.Calc.Round.round 2 (FLT_exp emin prec)
              FloatSpec.Calc.Round.nearestEvenMode
              (FloatSpec.Calc.Round.round 2 (FLT_exp emin prec)
                  FloatSpec.Calc.Round.nearestEvenMode (b * b) -
                FloatSpec.Calc.Round.round 2 (FLT_exp emin prec)
                  FloatSpec.Calc.Round.nearestEvenMode (a * c))|)
  · rw [ite_eq_left hcond]
    simpa [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode] using
      FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := 2) (fexp := FLT_exp emin prec)
      (rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t))))
      (x := FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode (b * b) -
        FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode (a * c)) (by decide)
  · rw [ite_eq_right hcond]
    simpa [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode] using
      FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := 2) (fexp := FLT_exp emin prec)
      (rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t))))
      (x :=
        FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode
          (FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode (b * b) -
            FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode (a * c)) +
        FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode
          ((b * b -
              FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode (b * b)) -
            (a * c -
              FloatSpec.Calc.Round.round 2 (FLT_exp emin prec) FloatSpec.Calc.Round.nearestEvenMode (a * c)))) (by decide)

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

/-- Final `Fulp`-to-`ulp` conversion used by Coq `discri_correct_test` and
`discri_fp_test`.

The lower Pff discriminant payload proves the error bound against Pff `Fulp`.
Once the final Pff witness `fd` represents the public result `d`, this bridge
rewrites that bound to the public Flocq `ulp` at `d`. -/
theorem discri_bound_from_pff_delta (emin prec : Int) [Prec_gt_0 prec]
    (d target : ℝ) (fd : PffFloat 2)
    (hprec : 1 < prec)
    (hemin : emin ≤ 0)
    (hfd_val : pff_to_R_aux 2 fd = d)
    (hfd_bound : PFbounded (make_bound 2 prec emin) fd)
    (hdelta :
      |pff_to_R_aux 2 fd - target| ≤
        2 * PFulp 2 (make_bound 2 prec emin) prec fd) :
    |d - target| ≤
      2 * ulp 2 (FLT_exp emin prec) d := by
  have hprec_pos : 0 < prec := Prec_gt_0.pos
  have hbnd_dExp : -(make_bound 2 prec emin).dExp = emin := by
    have h := make_bound_Emin 2 prec emin (hp := by exact hprec)
    have hd : (make_bound 2 prec emin).dExp = -emin := by
      simpa [wp, PostCond.noThrow, make_bound_Emin_check, pure] using
        h hemin
    omega
  have hFulpUlp :
      PFulp 2 (make_bound 2 prec emin) prec fd =
        ulp 2 (FLT_exp emin prec) d := by
    have h := Fulp_ulp 2 (make_bound 2 prec emin) prec fd
    have hpBound : pGivesBound 2 (make_bound 2 prec emin) prec := by
      have hp := make_bound_p 2 prec emin (hp := hprec)
      simpa only [wp, PostCond.noThrow, make_bound_p_check, pure,
        pGivesBound, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hp True.intro
    have h' :
        PFulp 2 (make_bound 2 prec emin) prec fd =
          ulp 2 (FLT_exp (-(make_bound 2 prec emin).dExp) prec)
            (pff_to_R_aux 2 fd) := by
      simpa [wp, PostCond.noThrow, Fulp_ulp_check, pure] using
        h ⟨hfd_bound, hpBound, hprec, (by decide : (1 : Int) < 2)⟩
    simpa [hbnd_dExp, hfd_val] using h'
  simpa [hfd_val, hFulpUlp] using hdelta

/-- The elementary public-side estimate used in the exceptional branches of
the two discriminant tests.  Nearest-even is substantially stronger than the
factor-two estimate, but this form is exactly what the final specifications
need. -/
private theorem nearest_round_error_le_two_ulp
    (emin prec : Int) [Prec_gt_0 prec] (x : ℝ) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest
      (fun t : Int => !(decide (2 ∣ t)))
    let r := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd x
    |r - x| ≤ 2 * ulp 2 (FLT_exp emin prec) r := by
  dsimp
  have hbeta : (1 : Int) < 2 := by decide
  have h := FloatSpec.Core.Ulp.error_le_half_ulp_round
    (beta := 2) (fexp := FLT_exp emin prec)
    (fun t : Int => !(decide (2 ∣ t))) x
  have hhalf :
      |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
          (FloatSpec.Core.Generic_fmt.Znearest
            (fun t : Int => !(decide (2 ∣ t)))) x - x| ≤
        (1 / 2 : ℝ) *
          ulp 2 (FLT_exp emin prec)
            (FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
              (FloatSpec.Core.Generic_fmt.Znearest
                (fun t : Int => !(decide (2 ∣ t)))) x) := by
    simpa only [wp, PostCond.noThrow, pure, Id.run, Prod.fst, Prod.snd]
      using h
  have huNonneg :
      0 ≤ ulp 2 (FLT_exp emin prec)
        (FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
          (FloatSpec.Core.Generic_fmt.Znearest
            (fun t : Int => !(decide (2 ∣ t)))) x) := by
    classical
    unfold ulp
    by_cases hz :
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
          (FloatSpec.Core.Generic_fmt.Znearest
            (fun t : Int => !(decide (2 ∣ t)))) x = 0
    · simp only [FloatSpec.Core.Ulp.ulp, hz, ite_eq_left]
      cases FloatSpec.Core.Ulp.negligible_exp (FLT_exp emin prec) with
      | none => exact le_rfl
      | some n => exact le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) _)
    · simp only [FloatSpec.Core.Ulp.ulp, hz, ite_eq_right]
      exact le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) _)
  nlinarith

/-- Pff witness construction for the only genuinely compensated branch of
Coq `discri_correct_test`.  The three exceptional cases (a zero product, a
zero rounded product difference, or an exactly representable compensation)
are intentionally left to the public wrapper, just as in the source proof. -/
private theorem discri_correct_test_nonexceptional
    (emin prec : Int) [Prec_gt_0 prec] (a b c : ℝ)
    (hprec : 1 < prec) (hemin : emin ≤ 0)
    (ha : generic_format 2 (FLT_exp emin prec) a)
    (hb : generic_format 2 (FLT_exp emin prec) b)
    (hc : generic_format 2 (FLT_exp emin prec) c)
    (U1 : b * b ≠ 0 →
      FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) ≤ |b * b|)
    (U2 : a * c ≠ 0 →
      FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) ≤ |a * c|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest
      (fun z : Int => !(decide (2 ∣ z)))
    let R := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
    let p := R (b * b)
    let q := R (a * c)
    let dp := b * b - p
    let dq := a * c - q
    let t := R (p - q)
    let s := R (dp - dq)
    let d := if p + q ≤ 3 * |p - q| then R (p - q) else R (t + s)
    d ≠ 0 → b * b ≠ 0 → a * c ≠ 0 → p - q ≠ 0 →
      (3 * |p - q| < p + q → s ≠ dp - dq) →
      |d - (b * b - a * c)| ≤ 2 * ulp 2 (FLT_exp emin prec) d := by
  classical
  dsimp
  intro hdNe hbbNe hacNe hpqNe hsNonexact
  let choice : Int → Bool := fun z => !(decide (2 ∣ z))
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let R : ℝ → ℝ :=
    FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
  let p := R (b * b)
  let q := R (a * c)
  let dp := b * b - p
  let dq := a * c - q
  let t := R (p - q)
  let s := R (dp - dq)
  let d := if p + q ≤ 3 * |p - q| then R (p - q) else R (t + s)
  have hbeta : (1 : Int) < 2 := by decide
  have hprecNZ : precisionNotZero prec := hprec
  have hprecPos : 0 ≤ prec := by omega
  have hprecNat : (prec.toNat : Int) = prec :=
    Int.toNat_of_nonneg hprecPos
  have hprecNatGt : 1 < prec.toNat := by omega
  have habsPrec : prec.natAbs = prec.toNat := by omega
  let bnd : Fbound := make_bound 2 prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  have hpBound : pGivesBound 2 bnd prec := by
    have h := make_bound_p 2 prec emin (hp := hprec)
    have hv : bnd.vNum = Zpower_nat 2 prec.natAbs := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_p_check, pure, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using
        h True.intro
    simpa [pGivesBound]
  have hbndExp : -bnd.dExp = emin := by
    have h := make_bound_Emin 2 prec emin (hp := hprec)
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using
        h hemin
    omega
  have hboExp : -bo.dExp = emin := by simpa [bo] using hbndExp
  have hvNum : bo.vNum = Zpower_nat 2 prec.toNat := by
    simpa [bo, pGivesBound, habsPrec] using hpBound
  have hformat (z : ℝ) (hz : generic_format 2 (FLT_exp emin prec) z) :
      ∃ f : FloatSpec.Core.Defs.FlocqFloat 2,
        _root_.F2R (beta:=2) f = z ∧ Fbounded (beta:=2) bo f := by
    have hz' : generic_format 2 (FLT_exp (-bnd.dExp) prec) z := by
      simpa [hbndExp] using hz
    rcases (by
        have h := format_is_flocq_bounded 2 bnd prec z
        simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
          using h ⟨hz', hpBound, hprecNZ, hbeta⟩) with
      ⟨f, hfVal, hfBound⟩
    exact ⟨f, hfVal, by simpa [bo, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hfBound⟩
  rcases hformat a ha with ⟨fa, hfaVal, hfaBound⟩
  rcases hformat b hb with ⟨fb, hfbVal, hfbBound⟩
  rcases hformat c hc with ⟨fc, hfcVal, hfcBound⟩
  rcases round_NE_is_pff_round 2 bnd prec (b * b) hpBound hprecNZ hbeta with
    ⟨fp, hfpCan, hfpRound, hfpVal⟩
  rcases round_NE_is_pff_round 2 bnd prec (a * c) hpBound hprecNZ hbeta with
    ⟨fq, hfqCan, hfqRound, hfqVal⟩
  rcases round_NE_is_pff_round 2 bnd prec (p - q) hpBound hprecNZ hbeta with
    ⟨ft, hftCan, hftRound, hftVal⟩
  rcases round_NE_is_pff_round 2 bnd prec (dp - dq) hpBound hprecNZ hbeta with
    ⟨fs, hfsCan, hfsRound, hfsVal⟩
  have hfpAlg : _root_.F2R (beta:=2) fp = p := by
    simpa [p, R, rnd, choice, hbndExp] using hfpVal
  have hfqAlg : _root_.F2R (beta:=2) fq = q := by
    simpa [q, R, rnd, choice, hbndExp] using hfqVal
  have hftAlg : _root_.F2R (beta:=2) ft = t := by
    simpa [t, R, rnd, choice, hbndExp] using hftVal
  have hfsAlg : _root_.F2R (beta:=2) fs = s := by
    simpa [s, R, rnd, choice, hbndExp] using hfsVal
  have hdpFmt : generic_format 2 (FLT_exp emin prec) dp := by
    have h := format_dp (emin := emin) (prec := prec) a b c
    simpa [wp, PostCond.noThrow, pure, format_dp_check, Id.run,
      FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode,
      dp, p, R, rnd, choice] using h ⟨ha, hb, hc, U1⟩
  have hdqFmt : generic_format 2 (FLT_exp emin prec) dq := by
    have h := format_dq (emin := emin) (prec := prec) a b c
    simpa [wp, PostCond.noThrow, pure, format_dq_check, Id.run,
      FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode,
      dq, q, R, rnd, choice] using h ⟨ha, hb, hc, U2⟩
  rcases hformat dp hdpFmt with ⟨fdp, hfdpVal, hfdpBound⟩
  rcases hformat dq hdqFmt with ⟨fdq, hfdqVal, hfdqBound⟩
  let din : ℝ := if p + q ≤ 3 * |p - q| then p - q else t + s
  rcases round_NE_is_pff_round 2 bnd prec din hpBound hprecNZ hbeta with
    ⟨fd, hfdCan, hfdRound, hfdValRaw⟩
  have hfdVal : _root_.F2R (beta:=2) fd = d := by
    by_cases hcond : p + q ≤ 3 * |p - q|
    · simpa [din, d, hcond, R, rnd, choice, hbndExp] using hfdValRaw
    · simpa [din, d, hcond, R, rnd, choice, hbndExp] using hfdValRaw
  have hfpBound : Fbounded (beta:=2) bo fp := hfpRound.1.1
  have hfqBound : Fbounded (beta:=2) bo fq := hfqRound.1.1
  have hftBound : Fbounded (beta:=2) bo ft := hftRound.1.1
  have hfsBound : Fbounded (beta:=2) bo fs := hfsRound.1.1
  have hfdBound : Fbounded (beta:=2) bo fd := hfdRound.1.1
  have hpowFmt (e : Int) (he : emin ≤ e) :
      generic_format 2 (FLT_exp emin prec)
        (FloatSpec.Core.Raux.bpow 2 e) := by
    have h := FloatSpec.Core.FLT.generic_format_FLT_bpow
      (prec := prec) (emin := emin) (beta := 2) (e := e)
    simpa [FloatSpec.Core.Raux.bpow] using h ⟨hbeta, he⟩
  have hpMagStrong :
      FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) ≤ |p| := by
    have h := FloatSpec.Core.Generic_fmt.abs_round_ge_generic
      2 (FLT_exp emin prec) rnd
      (hpowFmt (emin + 3 * prec) (by omega)) (U1 hbbNe)
    simpa [p, R, rnd, choice, FloatSpec.Core.Generic_fmt.round_to_generic,
      FloatSpec.Core.Generic_fmt.roundR] using h
  have hqMagStrong :
      FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) ≤ |q| := by
    have h := FloatSpec.Core.Generic_fmt.abs_round_ge_generic
      2 (FLT_exp emin prec) rnd
      (hpowFmt (emin + 3 * prec) (by omega)) (U2 hacNe)
    simpa [q, R, rnd, choice, FloatSpec.Core.Generic_fmt.round_to_generic,
      FloatSpec.Core.Generic_fmt.roundR] using h
  have hpMagNormal :
      (2 : ℝ) ^ (-bnd.dExp + prec - 1) ≤
        |pff_to_R_aux 2 fp| := by
    have hpow := FloatSpec.Core.Raux.bpow_le 2
      (emin + prec - 1) (emin + 3 * prec) hbeta (by omega)
    have hle : FloatSpec.Core.Raux.bpow 2 (emin + prec - 1) ≤ |p| :=
      le_trans (hpow True.intro) hpMagStrong
    simpa [hbndExp, hfpAlg, FloatSpec.Core.Raux.bpow] using hle
  have hqMagNormal :
      (2 : ℝ) ^ (-bnd.dExp + prec - 1) ≤
        |pff_to_R_aux 2 fq| := by
    have hpow := FloatSpec.Core.Raux.bpow_le 2
      (emin + prec - 1) (emin + 3 * prec) hbeta (by omega)
    have hle : FloatSpec.Core.Raux.bpow 2 (emin + prec - 1) ≤ |q| :=
      le_trans (hpow True.intro) hqMagStrong
    simpa [hbndExp, hfqAlg, FloatSpec.Core.Raux.bpow] using hle
  have hfpNormal : Fnormal (beta:=2) 2 bo fp := by
    have h := CanonicGeNormal 2 bnd prec fp
    simpa only [wp, PostCond.noThrow, CanonicGeNormal_check, pure, PredTrans.pure,
      PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat, PFnormal,
      toFboundSkel, bo] using h
      ⟨by simpa [bo] using hfpCan, hpBound, hprecNZ, hpMagNormal, hbeta⟩
  have hfqNormal : Fnormal (beta:=2) 2 bo fq := by
    have h := CanonicGeNormal 2 bnd prec fq
    simpa only [wp, PostCond.noThrow, CanonicGeNormal_check, pure, PredTrans.pure,
      PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat, PFnormal,
      toFboundSkel, bo] using h
      ⟨by simpa [bo] using hfqCan, hpBound, hprecNZ, hqMagNormal, hbeta⟩
  have htMag := U3_discri1 (emin := emin) (prec := prec) a b c ha hb hc U1 U2
  have htMag' : FloatSpec.Core.Raux.bpow 2 (emin + 2 * prec) ≤ |t| := by
    simpa [p, q, t, R, rnd, choice] using htMag hbbNe hacNe hpqNe
  have hdMag := U4_discri1 (emin := emin) (prec := prec) a b c ha hb hc U1 U2 hdNe
  have hdMag' : FloatSpec.Core.Raux.bpow 2 (emin + prec) ≤ |d| := by
    simpa [p, q, dp, dq, t, s, d, R, rnd, choice] using
      hdMag hbbNe hacNe hpqNe
  have hftExpGt : emin < ft.Fexp := by
    have hmag : (2 : ℝ) ^ (emin + prec) ≤ |pff_to_R_aux 2 ft| := by
      have := le_trans
        (bpow_le_plain 2 (emin + prec) (emin + 2 * prec) hbeta (by omega)) htMag'
      simpa [hftAlg, FloatSpec.Core.Raux.bpow] using this
    have h := FloatFexp_gt 2 bnd prec emin ft
    simpa only [wp, PostCond.noThrow, FloatFexp_gt_check, pure, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h
      ⟨hpBound, by simpa [bo] using hftBound, hmag, hbeta, by omega⟩
  have hfdExpGt : emin < fd.Fexp := by
    have hmag : (2 : ℝ) ^ (emin + prec) ≤ |pff_to_R_aux 2 fd| := by
      simpa [hfdVal, FloatSpec.Core.Raux.bpow] using hdMag'
    have h := FloatFexp_gt 2 bnd prec emin fd
    simpa only [wp, PostCond.noThrow, FloatFexp_gt_check, pure, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h
      ⟨hpBound, by simpa [bo] using hfdBound, hmag, hbeta, by omega⟩
  have hfdNormal : Fnormal (beta:=2) 2 bo fd := by
    have hmag : (2 : ℝ) ^ (-bnd.dExp + prec - 1) ≤
        |pff_to_R_aux 2 fd| := by
      have := le_trans
        (bpow_le_plain 2 (emin + prec - 1) (emin + prec) hbeta (by omega)) hdMag'
      simpa [hbndExp, hfdVal, FloatSpec.Core.Raux.bpow] using this
    have h := CanonicGeNormal 2 bnd prec fd
    simpa only [wp, PostCond.noThrow, CanonicGeNormal_check, pure, PredTrans.pure,
      PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat, PFnormal,
      toFboundSkel, bo] using h
      ⟨by simpa [bo] using hfdCan, hpBound, hprecNZ, hmag, hbeta⟩
  have hfsNormalIf : 3 * |p - q| < p + q →
      _root_.F2R (beta:=2) fs = 0 ∨ Fnormal (beta:=2) 2 bo fs := by
    intro hsecond
    have hsMag := U5_discri1 (emin := emin) (prec := prec) a b c ha hb hc U1 U2
    have hsMag' : FloatSpec.Core.Raux.bpow 2 (emin + prec - 1) ≤ |s| := by
      simpa [p, q, dp, dq, s, R, rnd, choice] using
        hsMag hbbNe hacNe (hsNonexact hsecond)
    right
    have hmag : (2 : ℝ) ^ (-bnd.dExp + prec - 1) ≤
        |pff_to_R_aux 2 fs| := by
      simpa [hbndExp, hfsAlg, FloatSpec.Core.Raux.bpow] using hsMag'
    have h := CanonicGeNormal 2 bnd prec fs
    simpa only [wp, PostCond.noThrow, CanonicGeNormal_check, pure, PredTrans.pure,
      PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat, PFnormal,
      toFboundSkel, bo] using h
      ⟨by simpa [bo] using hfsCan, hpBound, hprecNZ, hmag, hbeta⟩
  have hprod1 : (2 : ℝ) ^ (-bo.dExp + 2 * (prec.toNat : Int) - 1) ≤
      |_root_.F2R (beta:=2) fb * _root_.F2R (beta:=2) fb| := by
    have := le_trans
      (bpow_le_plain 2 (emin + 2 * prec - 1) (emin + 3 * prec) hbeta (by omega))
      (U1 hbbNe)
    simpa [hboExp, hprecNat, hfbVal, FloatSpec.Core.Raux.bpow] using this
  have hprod2 : (2 : ℝ) ^ (-bo.dExp + 2 * (prec.toNat : Int) - 1) ≤
      |_root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fc| := by
    have := le_trans
      (bpow_le_plain 2 (emin + 2 * prec - 1) (emin + 3 * prec) hbeta (by omega))
      (U2 hacNe)
    simpa [hboExp, hprecNat, hfaVal, hfcVal, FloatSpec.Core.Raux.bpow] using this
  have hRoundp : EvenClosest (beta:=2) bo (2 : ℝ) prec.toNat
      (_root_.F2R (beta:=2) fb * _root_.F2R (beta:=2) fb) fp := by
    simpa [bo, hfbVal] using hfpRound
  have hRoundq : EvenClosest (beta:=2) bo (2 : ℝ) prec.toNat
      (_root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fc) fq := by
    simpa [bo, hfaVal, hfcVal] using hfqRound
  have hFirstRound : _root_.F2R (beta:=2) fp + _root_.F2R (beta:=2) fq ≤
        3 * |_root_.F2R (beta:=2) fp - _root_.F2R (beta:=2) fq| →
      EvenClosest (beta:=2) bo (2 : ℝ) prec.toNat
        (_root_.F2R (beta:=2) fp - _root_.F2R (beta:=2) fq) fd := by
    intro hcond
    have hcond' : p + q ≤ 3 * |p - q| := by simpa [hfpAlg, hfqAlg] using hcond
    simpa [bo, din, hcond', hfpAlg, hfqAlg] using hfdRound
  have hRoundtIf : 3 * |_root_.F2R (beta:=2) fp - _root_.F2R (beta:=2) fq| <
        _root_.F2R (beta:=2) fp + _root_.F2R (beta:=2) fq →
      EvenClosest (beta:=2) bo (2 : ℝ) prec.toNat
        (_root_.F2R (beta:=2) fp - _root_.F2R (beta:=2) fq) ft := by
    intro _
    simpa [bo, hfpAlg, hfqAlg] using hftRound
  have hRoundsIf : 3 * |_root_.F2R (beta:=2) fp - _root_.F2R (beta:=2) fq| <
        _root_.F2R (beta:=2) fp + _root_.F2R (beta:=2) fq →
      EvenClosest (beta:=2) bo (2 : ℝ) prec.toNat
        (_root_.F2R (beta:=2) fdp - _root_.F2R (beta:=2) fdq) fs := by
    intro _
    simpa [bo, hfdpVal, hfdqVal] using hfsRound
  have hRounddIf : 3 * |_root_.F2R (beta:=2) fp - _root_.F2R (beta:=2) fq| <
        _root_.F2R (beta:=2) fp + _root_.F2R (beta:=2) fq →
      EvenClosest (beta:=2) bo (2 : ℝ) prec.toNat
        (_root_.F2R (beta:=2) ft + _root_.F2R (beta:=2) fs) fd := by
    intro hsecond
    have hcond : ¬ p + q ≤ 3 * |p - q| := by
      simpa [hfpAlg, hfqAlg] using (not_le_of_gt hsecond)
    simpa [bo, din, hcond, hftAlg, hfsAlg] using hfdRound
  have hdelta :
      |_root_.F2R (beta:=2) fd -
          (_root_.F2R (beta:=2) fb * _root_.F2R (beta:=2) fb -
            _root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fc)| ≤
        2 * Fulp (beta:=2) bo 2 prec.toNat fd := by
    have h := discri (beta:=2) bo 2 prec.toNat
      fa fb fc fp fq ft fdp fdq fs fd
    simpa only [wp, PostCond.noThrow, pure, discri_source_check, Id.run,
      ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h
      ⟨rfl, rfl, hprecNatGt, hvNum, hfaBound, hfbBound, hfcBound,
        hfpBound, hfqBound, hfdBound, hftBound, hfsBound, hfdpBound,
        hfdqBound, by omega, by omega, hprod1, hprod2,
        Or.inr hfpNormal, Or.inr hfqNormal,
        by simpa [hfpAlg, hfqAlg, hfsAlg] using hfsNormalIf,
        hfdNormal, hRoundp, hRoundq, hFirstRound, hRoundtIf,
        by intro _; simpa [hfdpVal, hfbVal, hfpAlg, dp],
        by intro _; simpa [hfdqVal, hfaVal, hfcVal, hfqAlg, dq],
        hRoundsIf, hRounddIf⟩
  exact discri_bound_from_pff_delta (emin := emin) (prec := prec)
    (d := d) (target := b * b - a * c) (fd := fd) hprec hemin hfdVal
    (by simpa [bo] using hfdBound)
    (by simpa [PFulp, hfbVal, hfaVal, hfcVal, bo, bnd, habsPrec] using hdelta)

noncomputable def discri_correct_test_check (_emin _prec : Int)
    (_a _b _c _d : ℝ) : Unit :=
  ()

/-- Coq theorem: `discri_correct_test`.

This public wrapper is the final Pff-to-Flocq step of the discriminant proof:
once the lower Pff payload has produced the final Pff result `fd`, its
boundedness, and the Pff `Fulp` error estimate, the result is the corresponding
Flocq `ulp` estimate for `d`. -/
theorem discri_correct_test_from_pff_delta (emin prec : Int) [Prec_gt_0 prec]
    (a b c d : ℝ) (fd : PffFloat 2)
    (hprec : 1 < prec)
    (hemin : emin ≤ 0)
    (hfd_val : pff_to_R_aux 2 fd = d)
    (hfd_bound : PFbounded (make_bound 2 prec emin) fd)
    (hdelta :
      |pff_to_R_aux 2 fd - (b * b - a * c)| ≤
        2 * PFulp 2 (make_bound 2 prec emin) prec fd) :
    ⦃⌜True⌝⦄
    (pure (discri_correct_test_check emin prec a b c d) : Id Unit)
    ⦃⇓_ => ⌜|d - (b * b - a * c)| ≤
      2 * ulp 2 (FLT_exp emin prec) d⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure, discri_correct_test_check, Id.run]
  exact discri_bound_from_pff_delta (emin := emin) (prec := prec)
    (d := d) (target := b * b - a * c) (fd := fd)
    hprec hemin hfd_val hfd_bound hdelta

noncomputable def discri_correct_test_source_check
    (_emin _prec : Int) (_a _b _c : ℝ) : Unit :=
  ()

/-- Exact translation of Coq discri_correct_test.

The algorithmic p, q, compensation terms, and branch result are kept as
the same local definitions as in the source section.  In particular, callers
do not supply a Pff witness or a pre-proved error bound: both are reconstructed
inside this theorem. -/
theorem discri_correct_test (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜1 < prec ∧ emin ≤ 0 ∧
        generic_format 2 (FLT_exp emin prec) a ∧
        generic_format 2 (FLT_exp emin prec) b ∧
        generic_format 2 (FLT_exp emin prec) c ∧
        (b * b ≠ 0 →
          FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) ≤ |b * b|) ∧
        (a * c ≠ 0 →
          FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) ≤ |a * c|) ∧
        (let rnd := FloatSpec.Core.Generic_fmt.Znearest
            (fun z : Int => !(decide (2 ∣ z)))
          let R := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
          let p := R (b * b)
          let q := R (a * c)
          let dp := b * b - p
          let dq := a * c - q
          let d := if p + q ≤ 3 * |p - q| then R (p - q)
            else R (R (p - q) + R (dp - dq))
          d ≠ 0)⌝⦄
    (pure (discri_correct_test_source_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜
      let rnd := FloatSpec.Core.Generic_fmt.Znearest
        (fun z : Int => !(decide (2 ∣ z)))
      let R := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
      let p := R (b * b)
      let q := R (a * c)
      let dp := b * b - p
      let dq := a * c - q
      let d := if p + q ≤ 3 * |p - q| then R (p - q)
        else R (R (p - q) + R (dp - dq))
      |d - (b * b - a * c)| ≤ 2 * ulp 2 (FLT_exp emin prec) d⌝⦄ := by
  classical
  intro hpre
  rcases hpre with
    ⟨hprec, hemin, ha, hb, hc, U1, U2, hdNeRaw⟩
  simp only [wp, PostCond.noThrow, pure, discri_correct_test_source_check,
    Id.run, ULift.up_down]
  let choice : Int → Bool := fun z => !(decide (2 ∣ z))
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let R : ℝ → ℝ :=
    FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
  let p := R (b * b)
  let q := R (a * c)
  let dp := b * b - p
  let dq := a * c - q
  let t := R (p - q)
  let s := R (dp - dq)
  let d := if p + q ≤ 3 * |p - q| then R (p - q) else R (t + s)
  change |d - (b * b - a * c)| ≤ 2 * ulp 2 (FLT_exp emin prec) d
  have hdNe : d ≠ 0 := by
    simpa [d, t, s, p, q, dp, dq, R, rnd, choice] using hdNeRaw
  have hbeta : (1 : Int) < 2 := by decide
  have hRzero : R 0 = 0 := by
    simpa [R, rnd] using roundR_Znearest_zero emin prec choice
  have hRfmt (x : ℝ) : generic_format 2 (FLT_exp emin prec) (R x) := by
    simpa [R, rnd] using
      FloatSpec.Core.Generic_fmt.generic_format_roundR
        2 (FLT_exp emin prec) rnd x hbeta
  have hRid (x : ℝ) (hx : generic_format 2 (FLT_exp emin prec) x) :
      R x = x := by
    simpa [R, rnd] using
      FloatSpec.Core.Generic_fmt.roundR_generic
        2 (FLT_exp emin prec) rnd x hbeta hx
  have hRopp (x : ℝ) : R (-x) = -R x := by
    have h := round_N_opp_sym emin prec choice x
    have hsymm : ∀ z : Int, choice z = !choice (-(z + 1)) := by
      intro z
      simpa [choice] using (congrFun nearestEven_choice_opp z).symm
    simpa only [wp, PostCond.noThrow, pure, round_N_opp_sym_check,
      Id.run, ULift.up_down, R, rnd, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h hsymm
  have hulpOpp (x : ℝ) :
      ulp 2 (FLT_exp emin prec) (-x) = ulp 2 (FLT_exp emin prec) x := by
    have h := FloatSpec.Core.Ulp.ulp_opp
      (beta := 2) (fexp := FLT_exp emin prec) x
    simpa only [wp, PostCond.noThrow, pure, Id.run, Prod.fst, Prod.snd,
      PredTrans.pure, PredTrans.apply, SPred.down_pure_nil]
      using h True.intro
  have hroundBound (x : ℝ) :
      |R x - x| ≤ 2 * ulp 2 (FLT_exp emin prec) (R x) := by
    simpa [R, rnd, choice, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using
      nearest_round_error_le_two_ulp (emin := emin) (prec := prec) x
  by_cases hbbZero : b * b = 0
  · have hpZero : p = 0 := by simp [p, hbbZero, hRzero]
    have hcond : p + q ≤ 3 * |p - q| := by
      rw [hpZero, zero_add, zero_sub, abs_neg]
      nlinarith [le_abs_self q, abs_nonneg q]
    have hdEq : d = -q := by
      dsimp [d]
      rw [ite_eq_left hcond, hpZero, zero_sub, hRopp]
      exact congrArg Neg.neg (hRid q (hRfmt (a * c)))
    have hqDef : q = R (a * c) := rfl
    rw [hdEq, hbbZero, zero_sub, hulpOpp]
    have h := hroundBound (a * c)
    rw [← hqDef] at h
    have habs : |-q + a * c| = |q - a * c| := by
      rw [← abs_neg]
      congr 1
      ring
    simpa [habs] using h
  by_cases hacZero : a * c = 0
  · have hqZero : q = 0 := by simp [q, hacZero, hRzero]
    have hcond : p + q ≤ 3 * |p - q| := by
      rw [hqZero, add_zero, sub_zero]
      nlinarith [le_abs_self p, abs_nonneg p]
    have hdEq : d = p := by
      dsimp [d]
      rw [ite_eq_left hcond, hqZero, sub_zero]
      exact hRid p (hRfmt (b * b))
    have hpDef : p = R (b * b) := rfl
    rw [hdEq, hacZero, sub_zero]
    have h := hroundBound (b * b)
    rw [← hpDef] at h
    exact h
  by_cases hpqZero : p - q = 0
  · by_cases hcond : p + q ≤ 3 * |p - q|
    · have hdZero : d = 0 := by
        dsimp [d]
        rw [ite_eq_left hcond, hpqZero, hRzero]
      exact False.elim (hdNe hdZero)
    · have htZero : t = 0 := by simp [t, hpqZero, hRzero]
      have hsId : R s = s := hRid s (hRfmt (dp - dq))
      have hdEq : d = R (b * b - a * c) := by
        dsimp [d]
        rw [ite_eq_right hcond, htZero, zero_add, hsId]
        apply congrArg R
        dsimp [s, dp, dq]
        linarith
      rw [hdEq]
      exact hroundBound (b * b - a * c)
  by_cases hsecond : 3 * |p - q| < p + q
  · by_cases hsExact : s = dp - dq
    · have hpNonneg : 0 ≤ p := by
        simpa [p, R, rnd] using
          FloatSpec.Core.Generic_fmt.roundR_nonneg_of_nonneg
            2 (FLT_exp emin prec) rnd (b * b) hbeta (mul_self_nonneg b)
      have hqPos : 0 < q := Q_positive p q hpNonneg hsecond
      have hqLeTwoP : q ≤ 2 * p := Q_le_two_P p q hqPos hsecond
      have hpLeTwoQ : p ≤ 2 * q := P_le_two_Q p q hpNonneg hsecond
      have hpFmt : generic_format 2 (FLT_exp emin prec) p := hRfmt (b * b)
      have hqFmt : generic_format 2 (FLT_exp emin prec) q := hRfmt (a * c)
      have hdiffFmt : generic_format 2 (FLT_exp emin prec) (p - q) :=
        sterbenz (beta := 2)
          (fexp := FLT_exp emin prec) p q hpFmt hqFmt hbeta
          ⟨by nlinarith, hpLeTwoQ⟩
      have htExact : t = p - q := hRid (p - q) hdiffFmt
      have hcond : ¬ p + q ≤ 3 * |p - q| := not_le_of_gt hsecond
      have hdEq : d = R (b * b - a * c) := by
        dsimp [d]
        rw [ite_eq_right hcond, htExact, hsExact]
        apply congrArg R
        dsimp [dp, dq]
        ring
      rw [hdEq]
      exact hroundBound (b * b - a * c)
    · exact discri_correct_test_nonexceptional
        (emin := emin) (prec := prec) a b c hprec hemin ha hb hc U1 U2
        hdNe hbbZero hacZero hpqZero (fun _ => hsExact)
  · exact discri_correct_test_nonexceptional
      (emin := emin) (prec := prec) a b c hprec hemin ha hb hc U1 U2
      hdNe hbbZero hacZero hpqZero (fun h => (hsecond h).elim)

noncomputable def discri_fp_test_check (_emin _prec : Int)
    (_a _b _c _d : ℝ) : Unit :=
  ()

/-- Coq theorem: `discri_fp_test`.

The full upstream proof builds the Pff witnesses for the rounded products and
final discriminant result, then invokes the lower Pff `discri` theorem.  This
wrapper records the final checked handoff from that Pff payload to the public
Flocq `ulp` error statement. -/
theorem discri_fp_test_from_pff_delta (emin prec : Int) [Prec_gt_0 prec]
    (a b c d : ℝ) (fd : PffFloat 2)
    (hprec : 1 < prec)
    (hemin : emin ≤ 0)
    (hfd_val : pff_to_R_aux 2 fd = d)
    (hfd_bound : PFbounded (make_bound 2 prec emin) fd)
    (hdelta :
      |pff_to_R_aux 2 fd - (b * b - a * c)| ≤
        2 * PFulp 2 (make_bound 2 prec emin) prec fd) :
    ⦃⌜True⌝⦄
    (pure (discri_fp_test_check emin prec a b c d) : Id Unit)
    ⦃⇓_ => ⌜|d - (b * b - a * c)| ≤
      2 * ulp 2 (FLT_exp emin prec) d⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure, discri_fp_test_check, Id.run]
  exact discri_bound_from_pff_delta (emin := emin) (prec := prec)
    (d := d) (target := b * b - a * c) (fd := fd)
    hprec hemin hfd_val hfd_bound hdelta

noncomputable def discri_fp_test_source_check
    (_emin _prec : Int) (_a _b _c : ℝ) : Unit :=
  ()

/- Exact translation of Coq `discri_fp_test`.

All Pff witnesses used by the Coq proof are reconstructed from the three
source-format inputs and the actual nearest-even algorithm.  In particular,
the public statement does not expose a Pff witness or a pre-proved error
payload. -/
set_option maxHeartbeats 2000000 in
theorem discri_fp_test (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜4 ≤ prec ∧ emin ≤ 0 ∧
        generic_format 2 (FLT_exp emin prec) a ∧
        generic_format 2 (FLT_exp emin prec) b ∧
        generic_format 2 (FLT_exp emin prec) c ∧
        (b * b ≠ 0 →
          FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) ≤ |b * b|) ∧
        (a * c ≠ 0 →
          FloatSpec.Core.Raux.bpow 2 (emin + 3 * prec) ≤ |a * c|) ∧
        (let rnd := FloatSpec.Core.Generic_fmt.Znearest
            (fun z : Int => !(decide (2 ∣ z)))
          let R := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
          let p := R (b * b)
          let q := R (a * c)
          let dp := b * b - p
          let dq := a * c - q
          let t := R (p - q)
          let u := R (3 * |t|)
          let v := R (p + q)
          let s := R (dp - dq)
          let d := if v ≤ u then R (p - q) else R (t + s)
          d ≠ 0)⌝⦄
    (pure (discri_fp_test_source_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜
      let rnd := FloatSpec.Core.Generic_fmt.Znearest
        (fun z : Int => !(decide (2 ∣ z)))
      let R := FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
      let p := R (b * b)
      let q := R (a * c)
      let dp := b * b - p
      let dq := a * c - q
      let t := R (p - q)
      let u := R (3 * |t|)
      let v := R (p + q)
      let s := R (dp - dq)
      let d := if v ≤ u then R (p - q) else R (t + s)
      |d - (b * b - a * c)| ≤ 2 * ulp 2 (FLT_exp emin prec) d⌝⦄ := by
  classical
  intro hpre
  rcases hpre with ⟨hprec, hemin, ha, hb, hc, U1, U2, hdNeRaw⟩
  simp only [wp, PostCond.noThrow, pure, discri_fp_test_source_check,
    Id.run, ULift.up_down]
  let choice : Int → Bool := fun z => !(decide (2 ∣ z))
  let rnd := FloatSpec.Core.Generic_fmt.Znearest choice
  let R : ℝ → ℝ :=
    FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec) rnd
  let p := R (b * b)
  let q := R (a * c)
  let dp := b * b - p
  let dq := a * c - q
  let t := R (p - q)
  let u := R (3 * |t|)
  let v := R (p + q)
  let s := R (dp - dq)
  let d := if v ≤ u then R (p - q) else R (t + s)
  change |d - (b * b - a * c)| ≤ 2 * ulp 2 (FLT_exp emin prec) d
  have hdNe : d ≠ 0 := by
    simpa [d, u, v, t, s, p, q, dp, dq, R, rnd, choice] using hdNeRaw
  have hbeta : (1 : Int) < 2 := by decide
  have hprec1 : 1 < prec := by omega
  have hprecNZ : precisionNotZero prec := hprec1
  have hprecPos : 0 ≤ prec := by omega
  have hprecNat : (prec.toNat : Int) = prec := Int.toNat_of_nonneg hprecPos
  have hprecNatGt : 1 < prec.toNat := by omega
  have hprecNat4 : 4 ≤ prec.toNat := by omega
  have habsPrec : prec.natAbs = prec.toNat := by omega
  let bnd : Fbound := make_bound 2 prec emin
  let bo : Fbound_skel := toFboundSkel bnd
  have hpBound : pGivesBound 2 bnd prec := by
    have h := make_bound_p 2 prec emin (hp := hprec1)
    have hv : bnd.vNum = Zpower_nat 2 prec.natAbs := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_p_check, pure] using
        h True.intro
    simpa [pGivesBound]
  have hbndExp : -bnd.dExp = emin := by
    have h := make_bound_Emin 2 prec emin (hp := hprec1)
    have hd : bnd.dExp = -emin := by
      simpa [bnd, wp, PostCond.noThrow, make_bound_Emin_check, pure] using
        h hemin
    omega
  have hboExp : -bo.dExp = emin := by simpa [bo] using hbndExp
  have hvNum : bo.vNum = Zpower_nat 2 prec.toNat := by
    simpa [bo, pGivesBound, habsPrec] using hpBound
  have hformat (z : ℝ) (hz : generic_format 2 (FLT_exp emin prec) z) :
      ∃ f : FloatSpec.Core.Defs.FlocqFloat 2,
        _root_.F2R (beta:=2) f = z ∧ Fbounded (beta:=2) bo f := by
    have hz' : generic_format 2 (FLT_exp (-bnd.dExp) prec) z := by
      simpa [hbndExp] using hz
    rcases (by
        have h := format_is_flocq_bounded 2 bnd prec z
        simpa only [wp, PostCond.noThrow, format_is_pff_format'_check, pure]
          using h ⟨hz', hpBound, hprecNZ, hbeta⟩) with
      ⟨f, hfVal, hfBound⟩
    exact ⟨f, hfVal, by simpa [bo, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using hfBound⟩
  rcases hformat a ha with ⟨fa, hfaVal, hfaBound⟩
  rcases hformat b hb with ⟨fb, hfbVal, hfbBound⟩
  rcases hformat c hc with ⟨fc, hfcVal, hfcBound⟩
  rcases round_NE_is_pff_round 2 bnd prec (b * b) hpBound hprecNZ hbeta with
    ⟨fp, hfpCan, hfpRound, hfpVal⟩
  rcases round_NE_is_pff_round 2 bnd prec (a * c) hpBound hprecNZ hbeta with
    ⟨fq, hfqCan, hfqRound, hfqVal⟩
  rcases round_NE_is_pff_round 2 bnd prec (p - q) hpBound hprecNZ hbeta with
    ⟨ft, hftCan, hftRound, hftVal⟩
  rcases round_NE_is_pff_round 2 bnd prec (3 * |t|) hpBound hprecNZ hbeta with
    ⟨fu, hfuCan, hfuRound, hfuVal⟩
  rcases round_NE_is_pff_round 2 bnd prec (p + q) hpBound hprecNZ hbeta with
    ⟨fv, hfvCan, hfvRound, hfvVal⟩
  rcases round_NE_is_pff_round 2 bnd prec (dp - dq) hpBound hprecNZ hbeta with
    ⟨fs, hfsCan, hfsRound, hfsVal⟩
  have hfpAlg : _root_.F2R (beta:=2) fp = p := by
    simpa [p, R, rnd, choice, hbndExp] using hfpVal
  have hfqAlg : _root_.F2R (beta:=2) fq = q := by
    simpa [q, R, rnd, choice, hbndExp] using hfqVal
  have hftAlg : _root_.F2R (beta:=2) ft = t := by
    simpa [t, R, rnd, choice, hbndExp] using hftVal
  have hfuAlg : _root_.F2R (beta:=2) fu = u := by
    simpa [u, R, rnd, choice, hbndExp] using hfuVal
  have hfvAlg : _root_.F2R (beta:=2) fv = v := by
    simpa [v, R, rnd, choice, hbndExp] using hfvVal
  have hfsAlg : _root_.F2R (beta:=2) fs = s := by
    simpa [s, R, rnd, choice, hbndExp] using hfsVal
  have hdpFmt : generic_format 2 (FLT_exp emin prec) dp := by
    have h := format_dp (emin := emin) (prec := prec) a b c
    simpa [wp, PostCond.noThrow, pure, format_dp_check, Id.run,
      FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode,
      dp, p, R, rnd, choice] using h ⟨ha, hb, hc, U1⟩
  have hdqFmt : generic_format 2 (FLT_exp emin prec) dq := by
    have h := format_dq (emin := emin) (prec := prec) a b c
    simpa [wp, PostCond.noThrow, pure, format_dq_check, Id.run,
      FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.nearestEvenMode,
      dq, q, R, rnd, choice] using h ⟨ha, hb, hc, U2⟩
  rcases hformat dp hdpFmt with ⟨fdp, hfdpVal, hfdpBound⟩
  rcases hformat dq hdqFmt with ⟨fdq, hfdqVal, hfdqBound⟩
  let din : ℝ := if v ≤ u then p - q else t + s
  rcases round_NE_is_pff_round 2 bnd prec din hpBound hprecNZ hbeta with
    ⟨fd, hfdCan, hfdRound, hfdValRaw⟩
  have hfdVal : _root_.F2R (beta:=2) fd = d := by
    by_cases hcond : v ≤ u
    · simpa [din, d, hcond, R, rnd, choice, hbndExp] using hfdValRaw
    · simpa [din, d, hcond, R, rnd, choice, hbndExp] using hfdValRaw
  have hfpBound : Fbounded (beta:=2) bo fp := hfpRound.1.1
  have hfqBound : Fbounded (beta:=2) bo fq := hfqRound.1.1
  have hftBound : Fbounded (beta:=2) bo ft := hftRound.1.1
  have hfuBound : Fbounded (beta:=2) bo fu := hfuRound.1.1
  have hfvBound : Fbounded (beta:=2) bo fv := hfvRound.1.1
  have hfsBound : Fbounded (beta:=2) bo fs := hfsRound.1.1
  have hfdBound : Fbounded (beta:=2) bo fd := hfdRound.1.1
  have hU1 : _root_.F2R (beta:=2) fb = 0 ∨
      (2 : ℝ) ^ (-bo.dExp + 3 * (prec.toNat : Int) - 1) ≤
        |_root_.F2R (beta:=2) fb * _root_.F2R (beta:=2) fb| := by
    by_cases hbbZero : b * b = 0
    · left
      have hbZero : b = 0 := by nlinarith
      simpa [hfbVal, hbZero]
    · right
      have hle := le_trans
        (bpow_le_plain 2 (emin + 3 * prec - 1) (emin + 3 * prec) hbeta (by omega))
        (U1 hbbZero)
      simpa [hboExp, hprecNat, hfbVal, FloatSpec.Core.Raux.bpow] using hle
  have hU2 : _root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fc = 0 ∨
      (2 : ℝ) ^ (-bo.dExp + 3 * (prec.toNat : Int) - 1) ≤
        |_root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fc| := by
    by_cases hacZero : a * c = 0
    · left
      simpa [hfaVal, hfcVal] using hacZero
    · right
      have hle := le_trans
        (bpow_le_plain 2 (emin + 3 * prec - 1) (emin + 3 * prec) hbeta (by omega))
        (U2 hacZero)
      simpa [hboExp, hprecNat, hfaVal, hfcVal,
        FloatSpec.Core.Raux.bpow] using hle
  have hRoundp : EvenClosest (beta:=2) bo (2 : ℝ) prec.toNat
      (_root_.F2R (beta:=2) fb * _root_.F2R (beta:=2) fb) fp := by
    simpa [bo, hfbVal] using hfpRound
  have hRoundq : EvenClosest (beta:=2) bo (2 : ℝ) prec.toNat
      (_root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fc) fq := by
    simpa [bo, hfaVal, hfcVal] using hfqRound
  have hRoundt : EvenClosest (beta:=2) bo (2 : ℝ) prec.toNat
      (_root_.F2R (beta:=2) fp - _root_.F2R (beta:=2) fq) ft := by
    simpa [bo, hfpAlg, hfqAlg] using hftRound
  have hRoundu : EvenClosest (beta:=2) bo (2 : ℝ) prec.toNat
      (3 * |_root_.F2R (beta:=2) ft|) fu := by
    simpa [bo, hftAlg] using hfuRound
  have hRoundv : EvenClosest (beta:=2) bo (2 : ℝ) prec.toNat
      (_root_.F2R (beta:=2) fp + _root_.F2R (beta:=2) fq) fv := by
    simpa [bo, hfpAlg, hfqAlg] using hfvRound
  have hFRoundd : _root_.F2R (beta:=2) fv ≤ _root_.F2R (beta:=2) fu →
      EvenClosest (beta:=2) bo (2 : ℝ) prec.toNat
        (_root_.F2R (beta:=2) fp - _root_.F2R (beta:=2) fq) fd := by
    intro hcond
    have hcond' : v ≤ u := by simpa [hfvAlg, hfuAlg] using hcond
    simpa [bo, din, hcond', hfpAlg, hfqAlg] using hfdRound
  have hSRounds : _root_.F2R (beta:=2) fu < _root_.F2R (beta:=2) fv →
      EvenClosest (beta:=2) bo (2 : ℝ) prec.toNat
        (_root_.F2R (beta:=2) fdp - _root_.F2R (beta:=2) fdq) fs := by
    intro _
    simpa [bo, hfdpVal, hfdqVal] using hfsRound
  have hSRoundd : _root_.F2R (beta:=2) fu < _root_.F2R (beta:=2) fv →
      EvenClosest (beta:=2) bo (2 : ℝ) prec.toNat
        (_root_.F2R (beta:=2) ft + _root_.F2R (beta:=2) fs) fd := by
    intro hcond
    have hcond' : ¬ v ≤ u := by
      exact not_le_of_gt (by simpa [hfuAlg, hfvAlg] using hcond)
    simpa [bo, din, hcond', hftAlg, hfsAlg] using hfdRound
  have hsplit : _root_.F2R (beta:=2) fd = 0 ∨
      |_root_.F2R (beta:=2) fd -
          (_root_.F2R (beta:=2) fb * _root_.F2R (beta:=2) fb -
            _root_.F2R (beta:=2) fa * _root_.F2R (beta:=2) fc)| ≤
        2 * Fulp (beta:=2) bo 2 prec.toNat fd := by
    have h := discri16 (beta:=2) bo 2 prec.toNat
      fa fb fc fp fq ft fdp fdq fs fd fu fv
    simpa only [wp, PostCond.noThrow, pure, discri16_check, Id.run,
      ULift.up_down, PredTrans.pure, PredTrans.apply, SPred.down_pure_nil, Int.cast_ofNat] using h
      ⟨rfl, rfl, hprecNatGt, hprecNat4, hvNum, hfaBound, hfbBound,
        hfcBound, fun _ => hfdpBound, fun _ => hfdqBound, hU1, hU2,
        hRoundp, hRoundq, hRoundt, hRoundu, hRoundv, hFRoundd,
        by simpa [hfdpVal, hfbVal, hfpAlg, dp],
        by simpa [hfdqVal, hfaVal, hfcVal, hfqAlg, dq],
        hSRounds, hSRoundd⟩
  have hdelta := hsplit.resolve_left (by
    intro hfdZero
    apply hdNe
    rw [← hfdVal]
    exact hfdZero)
  exact discri_bound_from_pff_delta (emin := emin) (prec := prec)
    (d := d) (target := b * b - a * c) (fd := fd) hprec1 hemin hfdVal
    (by simpa [bo] using hfdBound)
    (by simpa [PFulp, hfbVal, hfaVal, hfcVal, bo, bnd, habsPrec] using hdelta)
