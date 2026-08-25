import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import FloatSpec.src.Prop.Relative
import Mathlib.Data.Real.Basic

-- Error of the rounded-to-nearest addition is representable
-- Translated from Coq file: flocq/src/Prop/Plus_error.v

open Real
open FloatSpec.Core.Defs

variable (beta : Int) [ValidRadix beta]
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp fexp]

-- Section: Plus error representability

/-- Round representation with same exponent.

Upstream Flocq states this under `beta : radix`; in this Lean port that
radix invariant is the explicit hypothesis `hβ`. -/
theorem round_repr_same_exp (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (hβ : 1 < beta) (m e : Int) :
  ∃ m', FloatSpec.Core.Generic_fmt.roundR beta fexp rnd (_root_.F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e : FloatSpec.Core.Defs.FlocqFloat beta)) =
        _root_.F2R (FloatSpec.Core.Defs.FlocqFloat.mk m' e : FloatSpec.Core.Defs.FlocqFloat beta) := by
  classical
  let x : ℝ :=
    _root_.F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e : FloatSpec.Core.Defs.FlocqFloat beta)
  set c : Int := cexp beta fexp x with hc
  by_cases hce : c ≤ e
  · refine ⟨m, ?_⟩
    have hfmt : generic_format beta fexp x := by
      have htrip :=
        FloatSpec.Core.Generic_fmt.generic_format_F2R (beta := beta) (fexp := fexp)
          (m := m) (e := e)
      exact htrip ⟨hβ, by
        intro _hm
        simpa [x, c, hc] using hce⟩
    have hround :
        FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x = x :=
      FloatSpec.Core.Generic_fmt.roundR_generic (beta := beta) (fexp := fexp)
        (rnd := rnd) (x := x) hβ hfmt
    simpa [x] using hround
  · have hec : e ≤ c := le_of_lt (lt_of_not_ge hce)
    let n : Int := rnd (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x)
    refine ⟨n * beta ^ Int.toNat (c - e), ?_⟩
    have hroundF :
        FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x =
          _root_.F2R (FloatSpec.Core.Defs.FlocqFloat.mk n c : FloatSpec.Core.Defs.FlocqFloat beta) := by
      change FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x =
        FloatSpec.Core.Defs.F2R
          (FloatSpec.Core.Defs.FlocqFloat.mk n c : FloatSpec.Core.Defs.FlocqFloat beta)
      change
        (((rnd (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x) : Int) : ℝ) *
            (beta : ℝ) ^ (cexp beta fexp x)) =
          (((n : Int) : ℝ) * (beta : ℝ) ^ c)
      rw [show n = rnd (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x) from rfl]
    have hchange :=
      FloatSpec.Core.Float_prop.F2R_change_exp
        (beta := beta)
        (f := FloatSpec.Core.Defs.FlocqFloat.mk n c)
        (e' := e) hβ hec
    have hnat : (c - e).natAbs = Int.toNat (c - e) := by
      grind
    have hchange' :
        FloatSpec.Core.Defs.F2R
            (FloatSpec.Core.Defs.FlocqFloat.mk n c : FloatSpec.Core.Defs.FlocqFloat beta) =
          FloatSpec.Core.Defs.F2R
            (FloatSpec.Core.Defs.FlocqFloat.mk (n * beta ^ Int.toNat (c - e)) e :
              FloatSpec.Core.Defs.FlocqFloat beta) := by
      simpa [hnat] using hchange
    calc
      FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x
          = _root_.F2R (FloatSpec.Core.Defs.FlocqFloat.mk n c : FloatSpec.Core.Defs.FlocqFloat beta) := hroundF
      _ = _root_.F2R
            (FloatSpec.Core.Defs.FlocqFloat.mk (n * beta ^ Int.toNat (c - e)) e :
              FloatSpec.Core.Defs.FlocqFloat beta) := by
              simpa [_root_.F2R] using hchange'

variable [FloatSpec.Core.Generic_fmt.Monotone_exp fexp]
variable (hβ : 1 < beta)
variable (choice : Int → Bool)

private lemma znearest_eq_floor_of_lt_half (choice : Int → Bool) (x : ℝ)
    (h : x - ((Int.floor x : Int) : ℝ) < (1 / 2 : ℝ)) :
    FloatSpec.Core.Generic_fmt.Znearest choice x = Int.floor x := by
  unfold FloatSpec.Core.Generic_fmt.Znearest
  simp only [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil,
    FloatSpec.Core.Raux.Rcompare]
  simp only [h, ite_true]

private lemma znearest_eq_ceil_of_half_lt (choice : Int → Bool) (x : ℝ)
    (h : (1 / 2 : ℝ) < x - ((Int.floor x : Int) : ℝ)) :
    FloatSpec.Core.Generic_fmt.Znearest choice x = Int.ceil x := by
  unfold FloatSpec.Core.Generic_fmt.Znearest
  have hnotlt : ¬ x - ((Int.floor x : Int) : ℝ) < (1 / 2 : ℝ) :=
    not_lt.mpr (le_of_lt h)
  have hne : ¬ x - ((Int.floor x : Int) : ℝ) = (1 / 2 : ℝ) := by
    intro heq
    linarith
  simp only [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil,
    FloatSpec.Core.Raux.Rcompare]
  simp only [hnotlt, hne, ite_false]

private lemma znearest_eq_ceil_of_eq_half_choice (choice : Int → Bool) (x : ℝ)
    (h : x - ((Int.floor x : Int) : ℝ) = (1 / 2 : ℝ))
    (hc : choice (Int.floor x) = true) :
    FloatSpec.Core.Generic_fmt.Znearest choice x = Int.ceil x := by
  have hz := FloatSpec.Core.Generic_fmt.Znearest_eq_choice_of_eq_half choice x
    (by simpa [FloatSpec.Core.Raux.Zfloor] using h)
  simpa [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil, hc] using hz

private lemma znearest_eq_floor_of_eq_half_choice (choice : Int → Bool) (x : ℝ)
    (h : x - ((Int.floor x : Int) : ℝ) = (1 / 2 : ℝ))
    (hc : choice (Int.floor x) = false) :
    FloatSpec.Core.Generic_fmt.Znearest choice x = Int.floor x := by
  have hz := FloatSpec.Core.Generic_fmt.Znearest_eq_choice_of_eq_half choice x
    (by simpa [FloatSpec.Core.Raux.Zfloor] using h)
  simpa [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil, hc] using hz

private lemma znearest_abs_sub_le_floor_gap (choice : Int → Bool) (s : ℝ) :
    |(((FloatSpec.Core.Generic_fmt.Znearest choice s : Int) : ℝ) - s)| ≤
      s - ((Int.floor s : Int) : ℝ) := by
  classical
  have hfloor_le : ((Int.floor s : Int) : ℝ) ≤ s := Int.floor_le s
  have hceil_ge : s ≤ ((Int.ceil s : Int) : ℝ) := Int.le_ceil s
  have hgap_nonneg : 0 ≤ s - ((Int.floor s : Int) : ℝ) :=
    sub_nonneg.mpr hfloor_le
  by_cases hlt : s - ((Int.floor s : Int) : ℝ) < (1 / 2 : ℝ)
  · have hz := znearest_eq_floor_of_lt_half choice s hlt
    have hnonpos : ((Int.floor s : Int) : ℝ) - s ≤ 0 :=
      sub_nonpos.mpr hfloor_le
    have habs :
        |((Int.floor s : Int) : ℝ) - s| = s - ((Int.floor s : Int) : ℝ) := by
      rw [abs_of_nonpos hnonpos]
      ring
    rw [hz, habs]
  · by_cases heq : s - ((Int.floor s : Int) : ℝ) = (1 / 2 : ℝ)
    · have hs_not_int : s ≠ ((Int.floor s : Int) : ℝ) := by
        intro hs
        linarith
      have hceil_int := FloatSpec.Core.Generic_fmt.ceil_eq_floor_add_one
        (x := s) hs_not_int
      have hceil_real :
          ((Int.ceil s : Int) : ℝ) = ((Int.floor s : Int) : ℝ) + 1 := by
        exact_mod_cast hceil_int
      by_cases hchoice : choice (Int.floor s) = true
      · have hz := znearest_eq_ceil_of_eq_half_choice choice s heq hchoice
        have hceil_gap :
            ((Int.ceil s : Int) : ℝ) - s = s - ((Int.floor s : Int) : ℝ) := by
          linarith
        have hnonneg : 0 ≤ ((Int.ceil s : Int) : ℝ) - s :=
          sub_nonneg.mpr hceil_ge
        have habs :
            |((Int.ceil s : Int) : ℝ) - s| = ((Int.ceil s : Int) : ℝ) - s :=
          abs_of_nonneg hnonneg
        rw [hz, habs, hceil_gap]
      · have hchoice_false : choice (Int.floor s) = false := by
          cases hc : choice (Int.floor s) <;> simp [hc] at hchoice ⊢
        have hz := znearest_eq_floor_of_eq_half_choice choice s heq hchoice_false
        have hnonpos : ((Int.floor s : Int) : ℝ) - s ≤ 0 :=
          sub_nonpos.mpr hfloor_le
        have habs :
            |((Int.floor s : Int) : ℝ) - s| = s - ((Int.floor s : Int) : ℝ) := by
          rw [abs_of_nonpos hnonpos]
          ring
        rw [hz, habs]
    · have hgt : (1 / 2 : ℝ) < s - ((Int.floor s : Int) : ℝ) :=
        lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      have hs_not_int : s ≠ ((Int.floor s : Int) : ℝ) := by
        intro hs
        linarith
      have hceil_int := FloatSpec.Core.Generic_fmt.ceil_eq_floor_add_one
        (x := s) hs_not_int
      have hceil_real :
          ((Int.ceil s : Int) : ℝ) = ((Int.floor s : Int) : ℝ) + 1 := by
        exact_mod_cast hceil_int
      have hz := znearest_eq_ceil_of_half_lt choice s hgt
      have hnonneg : 0 ≤ ((Int.ceil s : Int) : ℝ) - s :=
        sub_nonneg.mpr hceil_ge
      have hle : ((Int.ceil s : Int) : ℝ) - s ≤
          s - ((Int.floor s : Int) : ℝ) := by
        linarith
      simpa [hz, abs_of_nonneg hnonneg] using hle

private lemma znearest_abs_sub_le_ceil_gap (choice : Int → Bool) (s : ℝ) :
    |(((FloatSpec.Core.Generic_fmt.Znearest choice s : Int) : ℝ) - s)| ≤
      ((Int.ceil s : Int) : ℝ) - s := by
  classical
  have hfloor_le : ((Int.floor s : Int) : ℝ) ≤ s := Int.floor_le s
  have hceil_ge : s ≤ ((Int.ceil s : Int) : ℝ) := Int.le_ceil s
  by_cases hlt : s - ((Int.floor s : Int) : ℝ) < (1 / 2 : ℝ)
  · have hz := znearest_eq_floor_of_lt_half choice s hlt
    by_cases hs_int : s = ((Int.floor s : Int) : ℝ)
    · have habs :
          |((Int.floor s : Int) : ℝ) - s| = 0 := by
        rw [hs_int]
        simp [Int.floor_intCast]
      rw [hz, habs]
      exact sub_nonneg.mpr hceil_ge
    · have hceil_int := FloatSpec.Core.Generic_fmt.ceil_eq_floor_add_one
        (x := s) hs_int
      have hceil_real :
          ((Int.ceil s : Int) : ℝ) = ((Int.floor s : Int) : ℝ) + 1 := by
        exact_mod_cast hceil_int
      have hnonpos : ((Int.floor s : Int) : ℝ) - s ≤ 0 :=
        sub_nonpos.mpr hfloor_le
      have hle : s - ((Int.floor s : Int) : ℝ) ≤
          ((Int.ceil s : Int) : ℝ) - s := by
        linarith
      simpa [hz, abs_of_nonpos hnonpos] using hle
  · by_cases heq : s - ((Int.floor s : Int) : ℝ) = (1 / 2 : ℝ)
    · have hs_not_int : s ≠ ((Int.floor s : Int) : ℝ) := by
        intro hs
        linarith
      have hceil_int := FloatSpec.Core.Generic_fmt.ceil_eq_floor_add_one
        (x := s) hs_not_int
      have hceil_real :
          ((Int.ceil s : Int) : ℝ) = ((Int.floor s : Int) : ℝ) + 1 := by
        exact_mod_cast hceil_int
      by_cases hchoice : choice (Int.floor s) = true
      · have hz := znearest_eq_ceil_of_eq_half_choice choice s heq hchoice
        have hnonneg : 0 ≤ ((Int.ceil s : Int) : ℝ) - s :=
          sub_nonneg.mpr hceil_ge
        have habs :
            |((Int.ceil s : Int) : ℝ) - s| = ((Int.ceil s : Int) : ℝ) - s :=
          abs_of_nonneg hnonneg
        rw [hz, habs]
      · have hchoice_false : choice (Int.floor s) = false := by
          cases hc : choice (Int.floor s) <;> simp [hc] at hchoice ⊢
        have hz := znearest_eq_floor_of_eq_half_choice choice s heq hchoice_false
        have hnonpos : ((Int.floor s : Int) : ℝ) - s ≤ 0 :=
          sub_nonpos.mpr hfloor_le
        have hgap :
            s - ((Int.floor s : Int) : ℝ) =
              ((Int.ceil s : Int) : ℝ) - s := by
          linarith
        have habs :
            |((Int.floor s : Int) : ℝ) - s| = s - ((Int.floor s : Int) : ℝ) := by
          rw [abs_of_nonpos hnonpos]
          ring
        rw [hz, habs, hgap]
    · have hgt : (1 / 2 : ℝ) < s - ((Int.floor s : Int) : ℝ) :=
        lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      have hz := znearest_eq_ceil_of_half_lt choice s hgt
      have hnonneg : 0 ≤ ((Int.ceil s : Int) : ℝ) - s :=
        sub_nonneg.mpr hceil_ge
      simpa [hz, abs_of_nonneg hnonneg]

theorem roundR_Znearest_N_pt (x : ℝ) (hβ : 1 < beta) :
    FloatSpec.Core.Defs.Rnd_N_pt
      (fun y => generic_format beta fexp y) x
      (FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest choice) x) := by
  classical
  let F : ℝ → Prop := fun y => generic_format beta fexp y
  set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x with hsm
  set e : Int := cexp beta fexp x with he
  let p : ℝ := (beta : ℝ) ^ e
  let d : ℝ := ((FloatSpec.Core.Raux.Zfloor sm : Int) : ℝ) * p
  let u : ℝ := ((FloatSpec.Core.Raux.Zceil sm : Int) : ℝ) * p
  let f : ℝ := (((FloatSpec.Core.Generic_fmt.Znearest choice sm : Int) : ℝ) * p)
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hβ
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hp_pos : 0 < p := by
    simpa [p] using zpow_pos hbpos_real e
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hscaled : sm * p = x := by
    have htrip := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
      (beta := beta) (fexp := fexp) (x := x)
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, sm, hsm, e, he, p]
      using htrip hβ
  have hround_near :
      FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest choice) x = f := by
    change
      (((FloatSpec.Core.Generic_fmt.Znearest choice
          (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x) : Int) : ℝ) *
        (beta : ℝ) ^ (cexp beta fexp x)) = f
    rw [← hsm, ← he]
  have hround_floor :
      FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_floor x = d := by
    change
      (((FloatSpec.Core.Generic_fmt.rnd_floor
          (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x) : Int) : ℝ) *
        (beta : ℝ) ^ (cexp beta fexp x)) = d
    rw [← hsm, ← he]
    simp [FloatSpec.Core.Generic_fmt.rnd_floor, FloatSpec.Core.Raux.Zfloor, d, p]
  have hround_ceil :
      FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_ceil x = u := by
    change
      (((FloatSpec.Core.Generic_fmt.rnd_ceil
          (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x) : Int) : ℝ) *
        (beta : ℝ) ^ (cexp beta fexp x)) = u
    rw [← hsm, ← he]
    simp [FloatSpec.Core.Generic_fmt.rnd_ceil, FloatSpec.Core.Raux.Zceil, u, p]
  have hFf : F f := by
    have hfmt :=
      FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := beta) (fexp := fexp)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice) (x := x) hβ
    simpa [F, hround_near] using hfmt
  have hDN : FloatSpec.Core.Defs.Rnd_DN_pt F x d := by
    refine ⟨?_, ?_, ?_⟩
    · have hfmt :=
        FloatSpec.Core.Generic_fmt.generic_format_roundR
          (beta := beta) (fexp := fexp)
          (rnd := FloatSpec.Core.Generic_fmt.rnd_floor) (x := x) hβ
      simpa [F, hround_floor] using hfmt
    · have hfloor_le : ((FloatSpec.Core.Raux.Zfloor sm : Int) : ℝ) ≤ sm := by
        simpa [FloatSpec.Core.Raux.Zfloor] using Int.floor_le sm
      have hmul := mul_le_mul_of_nonneg_right hfloor_le hp_nonneg
      simpa [d, hscaled] using hmul
    · intro g hgF hg_le
      have h :=
        FloatSpec.Core.Generic_fmt.roundR_ge_generic
          (beta := beta) (fexp := fexp)
          (rnd := FloatSpec.Core.Generic_fmt.rnd_floor)
          (x := g) (y := x) hβ (by simpa [F] using hgF) hg_le
      simpa [hround_floor] using h
  have hUP : FloatSpec.Core.Defs.Rnd_UP_pt F x u := by
    refine ⟨?_, ?_, ?_⟩
    · have hfmt :=
        FloatSpec.Core.Generic_fmt.generic_format_roundR
          (beta := beta) (fexp := fexp)
          (rnd := FloatSpec.Core.Generic_fmt.rnd_ceil) (x := x) hβ
      simpa [F, hround_ceil] using hfmt
    · have hceil_ge : sm ≤ ((FloatSpec.Core.Raux.Zceil sm : Int) : ℝ) := by
        simpa [FloatSpec.Core.Raux.Zceil] using Int.le_ceil sm
      have hmul := mul_le_mul_of_nonneg_right hceil_ge hp_nonneg
      simpa [u, hscaled] using hmul
    · intro g hgF hx_le_g
      have h :=
        FloatSpec.Core.Generic_fmt.roundR_le_generic
          (beta := beta) (fexp := fexp)
          (rnd := FloatSpec.Core.Generic_fmt.rnd_ceil)
          (x := x) (y := g) hβ (by simpa [F] using hgF) hx_le_g
      simpa [hround_ceil] using h
  have hbdL : |f - x| ≤ x - d := by
    have hdist :
        |(((FloatSpec.Core.Generic_fmt.Znearest choice sm : Int) : ℝ) - sm)| * p ≤
          (sm - ((FloatSpec.Core.Raux.Zfloor sm : Int) : ℝ)) * p := by
      have hmant := znearest_abs_sub_le_floor_gap choice sm
      have hmant' :
          |(((FloatSpec.Core.Generic_fmt.Znearest choice sm : Int) : ℝ) - sm)| ≤
            sm - ((FloatSpec.Core.Raux.Zfloor sm : Int) : ℝ) := by
        simpa [FloatSpec.Core.Raux.Zfloor] using hmant
      exact mul_le_mul_of_nonneg_right hmant' hp_nonneg
    have hf_x :
        |f - x| =
          |(((FloatSpec.Core.Generic_fmt.Znearest choice sm : Int) : ℝ) - sm)| * p := by
      calc
        |f - x| = |(((FloatSpec.Core.Generic_fmt.Znearest choice sm : Int) : ℝ) * p - sm * p)| := by
          rw [hscaled]
        _ = |(((FloatSpec.Core.Generic_fmt.Znearest choice sm : Int) : ℝ) - sm) * p| := by
          ring_nf
        _ = |(((FloatSpec.Core.Generic_fmt.Znearest choice sm : Int) : ℝ) - sm)| * p := by
          simp [abs_mul, abs_of_nonneg hp_nonneg]
    have hx_d :
        x - d = (sm - ((FloatSpec.Core.Raux.Zfloor sm : Int) : ℝ)) * p := by
      rw [← hscaled]
      simp [d]
      ring
    simpa [hf_x, hx_d] using hdist
  have hbdR : |f - x| ≤ u - x := by
    have hdist :
        |(((FloatSpec.Core.Generic_fmt.Znearest choice sm : Int) : ℝ) - sm)| * p ≤
          (((FloatSpec.Core.Raux.Zceil sm : Int) : ℝ) - sm) * p := by
      have hmant := znearest_abs_sub_le_ceil_gap choice sm
      have hmant' :
          |(((FloatSpec.Core.Generic_fmt.Znearest choice sm : Int) : ℝ) - sm)| ≤
            ((FloatSpec.Core.Raux.Zceil sm : Int) : ℝ) - sm := by
        simpa [FloatSpec.Core.Raux.Zceil] using hmant
      exact mul_le_mul_of_nonneg_right hmant' hp_nonneg
    have hf_x :
        |f - x| =
          |(((FloatSpec.Core.Generic_fmt.Znearest choice sm : Int) : ℝ) - sm)| * p := by
      calc
        |f - x| = |(((FloatSpec.Core.Generic_fmt.Znearest choice sm : Int) : ℝ) * p - sm * p)| := by
          rw [hscaled]
        _ = |(((FloatSpec.Core.Generic_fmt.Znearest choice sm : Int) : ℝ) - sm) * p| := by
          ring_nf
        _ = |(((FloatSpec.Core.Generic_fmt.Znearest choice sm : Int) : ℝ) - sm)| * p := by
          simp [abs_mul, abs_of_nonneg hp_nonneg]
    have hu_x :
        u - x = (((FloatSpec.Core.Raux.Zceil sm : Int) : ℝ) - sm) * p := by
      rw [← hscaled]
      simp [u]
      ring
    simpa [hf_x, hu_x] using hdist
  have hspec := FloatSpec.Core.Round_pred.Rnd_N_pt_DN_UP_spec
    (F := F) (x := x) (d := d) (u := u) (f := f)
  have hN : FloatSpec.Core.Defs.Rnd_N_pt F x f := by
    simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_DN_UP_check, pure,
      decide_eq_true_iff] using hspec ⟨hFf, hDN, hUP, hbdL, hbdR⟩
  simpa [F, hround_near] using hN

omit [FloatSpec.Core.Generic_fmt.Valid_exp fexp] [FloatSpec.Core.Generic_fmt.Monotone_exp fexp] in
theorem generic_format_shift (x : ℝ) (e : Int)
  (hβ : 1 < beta)
  (hx : generic_format beta fexp x) (h_exp : e ≤ cexp beta fexp x) :
  ∃ m : Int, x = (m : ℝ) * (beta : ℝ) ^ e := by
  let c : Int := cexp beta fexp x
  let m0 : Int :=
    FloatSpec.Core.Raux.Ztrunc
      (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x)
  let f : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk m0 c
  let m : Int := m0 * beta ^ (c - e).natAbs
  refine ⟨m, ?_⟩
  have hx_repr : x = _root_.F2R f := by
    simpa [f, m0, c, generic_format, FloatSpec.Core.Generic_fmt.generic_format,
      _root_.generic_format] using hx
  have hchange :
      _root_.F2R f =
        _root_.F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
          FloatSpec.Core.Defs.FlocqFloat beta) := by
    have h :=
      FloatSpec.Core.Float_prop.F2R_change_exp (beta := beta) (f := f)
        (e' := e) hβ (by simpa [f, c] using h_exp)
    simpa only [f, m, m0, c] using h
  calc
    x = _root_.F2R f := hx_repr
    _ = _root_.F2R
          (FloatSpec.Core.Defs.FlocqFloat.mk m e : FloatSpec.Core.Defs.FlocqFloat beta) :=
          hchange
    _ = (m : ℝ) * (beta : ℝ) ^ e := by
          simp [_root_.F2R, FloatSpec.Core.Defs.F2R]

/-- Plus error auxiliary lemma -/
lemma plus_error_aux (x y : ℝ)
  (hβ : 1 < beta)
  (h_exp : cexp beta fexp x ≤ cexp beta fexp y)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) :
  generic_format beta fexp (FloatSpec.Calc.Round.round beta fexp (Znearest choice) (x + y) - (x + y)) := by
  classical
  let e : Int := cexp beta fexp x
  rcases generic_format_shift (beta := beta) (fexp := fexp) (x := x) (e := e)
      hβ hx (by simp [e]) with ⟨mx, hx_repr⟩
  rcases generic_format_shift (beta := beta) (fexp := fexp) (x := y) (e := e)
      hβ hy (by simpa [e] using h_exp) with ⟨my, hy_repr⟩
  let msum : Int := mx + my
  let s : ℝ := x + y
  let rnd : ℝ → Int := FloatSpec.Core.Generic_fmt.Znearest choice
  let r : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp rnd s
  have hs_f2r :
      s = _root_.F2R
        (FloatSpec.Core.Defs.FlocqFloat.mk msum e : FloatSpec.Core.Defs.FlocqFloat beta) := by
    simp [s, msum, hx_repr, hy_repr, _root_.F2R, FloatSpec.Core.Defs.F2R,
      Int.cast_add]
    ring
  rcases round_repr_same_exp (beta := beta) (fexp := fexp)
      (rnd := rnd) hβ (m := msum) (e := e) with ⟨mround, hround_same⟩
  let merr : Int := mround - msum
  let ferr : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk merr e
  have hround_eval :
      r = _root_.F2R
        (FloatSpec.Core.Defs.FlocqFloat.mk mround e : FloatSpec.Core.Defs.FlocqFloat beta) := by
    simpa [r, rnd, hs_f2r] using hround_same
  have herr_f2r :
      _root_.F2R ferr = r - s := by
    rw [hround_eval, hs_f2r]
    change
      ((merr : ℝ) * (beta : ℝ) ^ e) =
        ((mround : ℝ) * (beta : ℝ) ^ e) - ((msum : ℝ) * (beta : ℝ) ^ e)
    simp [merr, Int.cast_sub]
    ring
  have hcexp_err_le : r - s ≠ 0 → cexp beta fexp (r - s) ≤ e := by
    intro herr_ne
    have hN := roundR_Znearest_N_pt (beta := beta) (fexp := fexp)
      (choice := choice) (x := s) hβ
    have hdist0 := hN.2 y (by simpa [s] using hy)
    have hdist : |r - s| ≤ |x| := by
      have hy_dist : |y - s| = |x| := by
        have hsub : y - s = -x := by
          dsimp [s]
          ring
        rw [hsub, abs_neg]
      simpa [r, rnd, hy_dist] using hdist0
    have hx_ne : x ≠ 0 := by
      intro hx0
      have herr_abs_nonpos : |r - s| ≤ 0 := by simpa [hx0] using hdist
      have herr_abs_zero : |r - s| = 0 :=
        le_antisymm herr_abs_nonpos (abs_nonneg _)
      exact herr_ne (abs_eq_zero.mp herr_abs_zero)
    have hx_upper : |x| < (beta : ℝ) ^ (mag beta x) := by
      have htrip := FloatSpec.Core.Raux.mag_upper_bound
        (beta := beta) (x := x) hβ hx_ne
      simpa [FloatSpec.Core.Raux.abs_val, Std.Do.wp, Std.Do.PostCond.noThrow,
        Id.run, pure] using htrip True.intro
    have herr_upper : |r - s| < (beta : ℝ) ^ (mag beta x) :=
      lt_of_le_of_lt hdist hx_upper
    have hmag_le : mag beta (r - s) ≤ mag beta x := by
      have htrip := FloatSpec.Core.Raux.mag_le_abs
        (beta := beta) (x := r - s) (e := mag beta x) hβ herr_ne herr_upper
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure]
        using htrip True.intro
    have hmono :
        fexp (mag beta (r - s)) ≤ fexp (mag beta x) :=
      FloatSpec.Core.Generic_fmt.Monotone_exp.mono (fexp := fexp) hmag_le
    simpa [e, FloatSpec.Core.Generic_fmt.cexp] using hmono
  have hfmt :=
    (FloatSpec.Core.Generic_fmt.generic_format_F2R'
      (beta := beta) (fexp := fexp) (x := r - s) (f := ferr))
      ⟨hβ, herr_f2r, hcexp_err_le⟩
  simpa [FloatSpec.Calc.Round.round, FloatSpec.Compat.Scaffold.ZnearestMode,
    Znearest, rnd, r, s] using hfmt

/-- Error of the addition -/
theorem plus_error (x y : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) :
  generic_format beta fexp (FloatSpec.Calc.Round.round beta fexp (Znearest choice) (x + y) - (x + y)) := by
  by_cases hxy : cexp beta fexp x ≤ cexp beta fexp y
  · exact plus_error_aux (beta := beta) (fexp := fexp) (choice := choice)
      x y hβ hxy hx hy
  · have hyx : cexp beta fexp y ≤ cexp beta fexp x := le_of_lt (lt_of_not_ge hxy)
    have h := plus_error_aux (beta := beta) (fexp := fexp) (choice := choice)
      y x hβ hyx hy hx
    simpa [add_comm] using h

-- Section: Plus zero properties

variable [FloatSpec.Core.Ulp.Exp_not_FTZ fexp]

/-- Round plus not equal to zero auxiliary -/
lemma round_plus_neq_0_aux (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x y : ℝ)
  (hβ : 1 < beta)
  (h_exp : cexp beta fexp x ≤ cexp beta fexp y)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (h_pos : 0 < x + y) :
  FloatSpec.Core.Generic_fmt.roundR beta fexp rnd (x + y) ≠ 0 := by
  classical
  set e : Int := cexp beta fexp x with he
  rcases generic_format_shift (beta := beta) (fexp := fexp) (x := x) (e := e)
      hβ hx (by simpa [e, he]) with ⟨mx, hx_repr⟩
  rcases generic_format_shift (beta := beta) (fexp := fexp) (x := y) (e := e)
      hβ hy (by simpa [e, he] using h_exp) with ⟨my, hy_repr⟩
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbpos e
  have hsum_repr : x + y = ((mx + my : Int) : ℝ) * (beta : ℝ) ^ e := by
    rw [hx_repr, hy_repr]
    rw [Int.cast_add]
    ring
  have hmant_pos : 0 < mx + my := by
    have hprod_pos : 0 < ((mx + my : Int) : ℝ) * (beta : ℝ) ^ e := by
      simpa [hsum_repr] using h_pos
    have hmant_real_pos : 0 < ((mx + my : Int) : ℝ) :=
      (mul_pos_iff_of_pos_right hpow_pos).mp hprod_pos
    exact_mod_cast hmant_real_pos
  have hone_le_mant : (1 : Int) ≤ mx + my := Int.add_one_le_iff.mpr hmant_pos
  have hbpow_le_sum : (beta : ℝ) ^ e ≤ x + y := by
    have hmant_real_one : (1 : ℝ) ≤ ((mx + my : Int) : ℝ) := by
      exact_mod_cast hone_le_mant
    have hmul := mul_le_mul_of_nonneg_right hmant_real_one (le_of_lt hpow_pos)
    simpa [hsum_repr] using hmul
  have hfmt_bpow : generic_format beta fexp ((beta : ℝ) ^ e) := by
    have hnotftz :
        fexp (e + 1) ≤ e := by
      have h := FloatSpec.Core.Ulp.Exp_not_FTZ.exp_not_FTZ
        (fexp := fexp) (mag beta x)
      simpa [e, he, FloatSpec.Core.Generic_fmt.cexp] using h
    have htrip :=
      FloatSpec.Core.Generic_fmt.generic_format_bpow
        (beta := beta) (fexp := fexp) (e := e)
        ⟨hβ, hnotftz⟩
    simpa using htrip
  have hround_ge :
      (beta : ℝ) ^ e ≤
        FloatSpec.Core.Generic_fmt.roundR beta fexp rnd (x + y) :=
    FloatSpec.Core.Generic_fmt.roundR_ge_generic
      (beta := beta) (fexp := fexp) (rnd := rnd)
      (x := (beta : ℝ) ^ e) (y := x + y) hβ hfmt_bpow hbpow_le_sum
  intro hzero
  have : (beta : ℝ) ^ e ≤ 0 := by simpa [hzero] using hround_ge
  exact (not_lt_of_ge this) hpow_pos

/-- rnd(x+y)=0 → x+y ≠ 0 (provided this is not a FTZ format) -/
theorem round_plus_neq_0 (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x y : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (h_nonzero : x + y ≠ 0) :
  FloatSpec.Core.Generic_fmt.roundR beta fexp rnd (x + y) ≠ 0 := by
  by_cases hpos0 : 0 ≤ x + y
  · have hpos : 0 < x + y := lt_of_le_of_ne hpos0 (Ne.symm h_nonzero)
    by_cases hxy : cexp beta fexp x ≤ cexp beta fexp y
    · exact round_plus_neq_0_aux (beta := beta) (fexp := fexp)
        (rnd := rnd) x y hβ hxy hx hy hpos
    · have hyx : cexp beta fexp y ≤ cexp beta fexp x := le_of_lt (lt_of_not_ge hxy)
      have h := round_plus_neq_0_aux (beta := beta) (fexp := fexp)
        (rnd := rnd) y x hβ hyx hy hx (by simpa [add_comm] using hpos)
      simpa [add_comm] using h
  · have hneg : 0 < -(x + y) := by linarith
    have hx_neg : generic_format beta fexp (-x) := by
      have h := FloatSpec.Core.Generic_fmt.generic_format_opp
        (beta := beta) (fexp := fexp) (x := x)
      exact h hx
    have hy_neg : generic_format beta fexp (-y) := by
      have h := FloatSpec.Core.Generic_fmt.generic_format_opp
        (beta := beta) (fexp := fexp) (x := y)
      exact h hy
    have hcexp_neg_x : cexp beta fexp (-x) = cexp beta fexp x := by
      have h := FloatSpec.Core.Generic_fmt.cexp_opp
        (beta := beta) (fexp := fexp) (x := x) hβ
      exact h
    have hcexp_neg_y : cexp beta fexp (-y) = cexp beta fexp y := by
      have h := FloatSpec.Core.Generic_fmt.cexp_opp
        (beta := beta) (fexp := fexp) (x := y) hβ
      exact h
    have hneg_xy : 0 < -x + -y := by nlinarith
    have hneg_yx : 0 < -y + -x := by nlinarith
    have hnonzero_neg :
        FloatSpec.Core.Generic_fmt.roundR beta fexp
            (FloatSpec.Core.Generic_fmt.Zrnd_opp rnd) (-(x + y)) ≠ 0 := by
      by_cases hxy : cexp beta fexp (-x) ≤ cexp beta fexp (-y)
      · have haux := round_plus_neq_0_aux (beta := beta) (fexp := fexp)
          (rnd := FloatSpec.Core.Generic_fmt.Zrnd_opp rnd)
          (-x) (-y) hβ hxy hx_neg hy_neg hneg_xy
        have hsum : -x + -y = -(x + y) := by ring
        rw [hsum] at haux
        exact haux
      · have hyx : cexp beta fexp (-y) ≤ cexp beta fexp (-x) :=
          le_of_lt (lt_of_not_ge hxy)
        have haux := round_plus_neq_0_aux (beta := beta) (fexp := fexp)
          (rnd := FloatSpec.Core.Generic_fmt.Zrnd_opp rnd)
          (-y) (-x) hβ hyx hy_neg hx_neg hneg_yx
        have hsum : -y + -x = -(x + y) := by ring
        rw [hsum] at haux
        exact haux
    intro hzero
    apply hnonzero_neg
    have hopp := FloatSpec.Core.Generic_fmt.roundR_opp
      (beta := beta) (fexp := fexp) (rnd := rnd) (x := x + y) hβ
    have hrewrite :
        FloatSpec.Core.Generic_fmt.roundR beta fexp
            (FloatSpec.Core.Generic_fmt.Zrnd_opp rnd) (-(x + y)) =
          - FloatSpec.Core.Generic_fmt.roundR beta fexp rnd (x + y) := by
      have h2 := FloatSpec.Core.Generic_fmt.roundR_opp
        (beta := beta) (fexp := fexp)
        (rnd := FloatSpec.Core.Generic_fmt.Zrnd_opp rnd) (x := x + y) hβ
      have hopp_opp :
          FloatSpec.Core.Generic_fmt.Zrnd_opp (FloatSpec.Core.Generic_fmt.Zrnd_opp rnd) = rnd := by
        funext t
        simp [FloatSpec.Core.Generic_fmt.Zrnd_opp]
      simpa [hopp_opp] using h2
    rw [hrewrite, hzero]
    simp

/-- rnd(x+y)=0 → x+y = 0 -/
theorem round_plus_eq_0 (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x y : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (h_zero : FloatSpec.Core.Generic_fmt.roundR beta fexp rnd (x + y) = 0) :
  x + y = 0 := by
  by_contra h_nonzero
  exact (round_plus_neq_0 (beta := beta) (fexp := fexp)
    (rnd := rnd) x y hβ hx hy h_nonzero) h_zero

-- Section: FLT format plus properties

variable (emin prec : Int)
variable [Prec_gt_0 prec]

/-- FLT format plus small -/
theorem FLT_format_plus_small (x y : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (hy : generic_format beta (FLT_exp emin prec) y)
  (h_bound : |x + y| ≤ FloatSpec.Core.Raux.bpow beta (prec + emin)) :
  generic_format beta (FLT_exp emin prec) (x + y) := by
  classical
  let fixExp : Int → Int := FloatSpec.Core.FIX.FIX_exp (emin := emin)
  have hx_fix : generic_format beta fixExp x := by
    have htrip :=
      FloatSpec.Core.FLT.generic_format_FIX_FLT
        (prec := prec) (emin := emin) (beta := beta) (x := x)
    simpa [fixExp] using htrip ⟨hβ, hx⟩
  have hy_fix : generic_format beta fixExp y := by
    have htrip :=
      FloatSpec.Core.FLT.generic_format_FIX_FLT
        (prec := prec) (emin := emin) (beta := beta) (x := y)
    simpa [fixExp] using htrip ⟨hβ, hy⟩
  rcases generic_format_shift (beta := beta) (fexp := fixExp)
      (x := x) (e := emin) hβ hx_fix
      (by
        change emin ≤ fixExp (mag beta x)
        simp [fixExp, FloatSpec.Core.FIX.FIX_exp]) with ⟨mx, hx_repr⟩
  rcases generic_format_shift (beta := beta) (fexp := fixExp)
      (x := y) (e := emin) hβ hy_fix
      (by
        change emin ≤ fixExp (mag beta y)
        simp [fixExp, FloatSpec.Core.FIX.FIX_exp]) with ⟨my, hy_repr⟩
  let fsum : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk (mx + my) emin
  have hsum_f2r : _root_.F2R fsum = x + y := by
    rw [hx_repr, hy_repr]
    simp [fsum, _root_.F2R, FloatSpec.Core.Defs.F2R, Int.cast_add]
    ring
  have hfix_sum : generic_format beta fixExp (x + y) := by
    have htrip :=
      FloatSpec.Core.Generic_fmt.generic_format_F2R'
        (beta := beta) (fexp := fixExp) (x := x + y) (f := fsum)
    exact htrip ⟨hβ, hsum_f2r, by
      intro _hne
      simp [fixExp, fsum, FloatSpec.Core.Generic_fmt.cexp,
        FloatSpec.Core.FIX.FIX_exp]⟩
  have hflt :=
    FloatSpec.Core.FLT.generic_format_FLT_FIX
      (prec := prec) (emin := emin) (beta := beta) (x := x + y)
  have h_bound' : |x + y| ≤ (beta : ℝ) ^ (emin + prec) := by
    simpa [FloatSpec.Core.Raux.bpow, add_comm] using h_bound
  simpa [fixExp] using hflt ⟨hβ, h_bound', hfix_sum⟩

/-- FLT plus error with nearest rounding existence -/
lemma FLT_plus_error_N_ex (x y : ℝ)
  (hbeta : 1 < beta)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (hy : generic_format beta (FLT_exp emin prec) y) :
  ∃ eps, |eps| ≤ u_ro beta prec / (1 + u_ro beta prec) ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (x + y) = (x + y) * (1 + eps) := by
  classical
  have hpos : 0 ≤ u_ro beta prec / (1 + u_ro beta prec) :=
    u_rod1pu_ro_pos (beta := beta) (prec := prec) hbeta
  by_cases hlarge :
      FloatSpec.Core.Raux.bpow beta (emin + prec) ≤ |x + y|
  · rcases relative_error_N_FLX'_ex (beta := beta) (choice := choice)
      (prec := prec) hbeta (x := x + y) with ⟨eps, heps, hround_flx⟩
    refine ⟨eps, heps, ?_⟩
    have hcexp :
        FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp emin prec) (x + y) =
          FloatSpec.Core.Generic_fmt.cexp beta (FLX_exp prec) (x + y) := by
      have htrip := FloatSpec.Core.FLT.cexp_FLT_FLX
        (prec := prec) (emin := emin) (beta := beta) (x := x + y)
      have hrun := htrip ⟨hbeta, by
        simpa [FloatSpec.Core.Raux.bpow] using hlarge⟩
      simpa [FLT_exp, FLX_exp] using hrun
    have hround_eq :
        FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (x + y) =
          FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) (x + y) := by
      unfold FloatSpec.Calc.Round.round FloatSpec.Core.Generic_fmt.roundR
      simp [FloatSpec.Core.Generic_fmt.scaled_mantissa, hcexp]
    simpa [hround_eq] using hround_flx
  · refine ⟨0, ?_, ?_⟩
    · simpa using hpos
    · have hsmall :
          |x + y| ≤ FloatSpec.Core.Raux.bpow beta (prec + emin) := by
        have hlt : |x + y| < FloatSpec.Core.Raux.bpow beta (emin + prec) :=
          lt_of_not_ge hlarge
        have hle : |x + y| ≤ FloatSpec.Core.Raux.bpow beta (emin + prec) :=
          le_of_lt hlt
        simpa [add_comm] using hle
      have hfmt :
          generic_format beta (FLT_exp emin prec) (x + y) :=
        FLT_format_plus_small (beta := beta) (emin := emin) (prec := prec)
          x y hbeta hx hy hsmall
      have hround :
          FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (x + y) =
            x + y := by
        have h :=
          FloatSpec.Core.Generic_fmt.roundR_generic
            (beta := beta) (fexp := FLT_exp emin prec)
            (rnd := FloatSpec.Core.Generic_fmt.Znearest choice)
            (x := x + y) hbeta hfmt
        simpa [FloatSpec.Calc.Round.round, Znearest,
          FloatSpec.Compat.Scaffold.ZnearestMode] using h
      simpa [hround]

/-- FLT plus error with round existence -/
lemma FLT_plus_error_N_round_ex (x y : ℝ)
  (hbeta : 1 < beta)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (hy : generic_format beta (FLT_exp emin prec) y) :
  ∃ eps, |eps| ≤ u_ro beta prec ∧
    x + y = FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (x + y) * (1 + eps) := by
  exact relative_error_N_round_ex_derive
    (beta := beta) (prec := prec)
    (x := x + y)
    (rx := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (x + y))
    hbeta
    (FLT_plus_error_N_ex (beta := beta) (choice := choice)
      (emin := emin) (prec := prec) x y hbeta hx hy)

-- Section: Plus mult ulp properties

variable (rnd : ℝ → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_rnd rnd]

/-- Existence of shift representation -/
lemma ex_shift (x : ℝ) (e : Int)
  (hβ : 1 < beta)
  (hx : generic_format beta fexp x) (h_exp : e ≤ cexp beta fexp x) :
  ∃ m : Int, x = (m : ℝ) * (beta : ℝ) ^ e := by
  let c : Int := cexp beta fexp x
  let m0 : Int :=
    FloatSpec.Core.Raux.Ztrunc
      (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x)
  let f : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk m0 c
  let m : Int := m0 * beta ^ (c - e).natAbs
  refine ⟨m, ?_⟩
  have hx_repr : x = _root_.F2R f := by
    simpa [f, m0, c, generic_format, FloatSpec.Core.Generic_fmt.generic_format,
      _root_.generic_format] using hx
  have hchange :
      _root_.F2R f =
        _root_.F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
          FloatSpec.Core.Defs.FlocqFloat beta) := by
    have h :=
      FloatSpec.Core.Float_prop.F2R_change_exp (beta := beta) (f := f)
        (e' := e) hβ (by simpa [f, c] using h_exp)
    simpa only [f, m, m0, c] using h
  calc
    x = _root_.F2R f := hx_repr
    _ = _root_.F2R
          (FloatSpec.Core.Defs.FlocqFloat.mk m e : FloatSpec.Core.Defs.FlocqFloat beta) :=
          hchange
    _ = (m : ℝ) * (beta : ℝ) ^ e := by
          simp [_root_.F2R, FloatSpec.Core.Defs.F2R]

/-- Magnitude minus one relation -/
lemma mag_minus1 (z : ℝ) (hβ : 1 < beta) (h_nonzero : z ≠ 0) :
  mag beta z - 1 = mag beta (z / (beta : ℝ)) := by
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  have hdiv_ne : z / (beta : ℝ) ≠ 0 := div_ne_zero h_nonzero hbne
  have hz_abs_pos : 0 < |z| := abs_pos.mpr h_nonzero
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := Real.log_pos hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
  set L : ℝ := Real.log |z| / Real.log (beta : ℝ)
  have hlog_div :
      Real.log |z / (beta : ℝ)| = Real.log |z| - Real.log (beta : ℝ) := by
    rw [abs_div, abs_of_pos hbpos]
    exact Real.log_div (x := |z|) (y := (beta : ℝ)) (ne_of_gt hz_abs_pos) hbne
  have hscaled :
      Real.log |z / (beta : ℝ)| / Real.log (beta : ℝ) = L - 1 := by
    calc
      Real.log |z / (beta : ℝ)| / Real.log (beta : ℝ)
          = (Real.log |z| - Real.log (beta : ℝ)) / Real.log (beta : ℝ) := by
              rw [hlog_div]
      _ = L - 1 := by
              change (Real.log |z| - Real.log (beta : ℝ)) / Real.log (beta : ℝ) =
                Real.log |z| / Real.log (beta : ℝ) - 1
              field_simp [hlogβ_ne]
  have hfloor_sub :
      Int.floor (L - 1) = Int.floor L - 1 := by
    simpa [sub_eq_add_neg] using (Int.floor_add_intCast L (-1))
  have hfloor_L :
      Int.floor L = Int.floor (Real.log |z| / Real.log (beta : ℝ)) := by
    simp [L]
  unfold _root_.mag FloatSpec.Core.Raux.mag
  simp only [h_nonzero, hdiv_ne, if_false]
  rw [hscaled, hfloor_sub, hfloor_L]
  omega

/-- Round plus F2R representation -/
theorem round_plus_F2R (x y : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) (h_nonzero : x ≠ 0) :
  ∃ m : Int, FloatSpec.Core.Generic_fmt.roundR beta fexp rnd (x + y) =
    _root_.F2R (FloatSpec.Core.Defs.FlocqFloat.mk m (cexp beta fexp (x / (beta : ℝ))) : FloatSpec.Core.Defs.FlocqFloat beta) := by
  classical
  set e : Int := cexp beta fexp (x / (beta : ℝ)) with he
  by_cases hmag : mag beta (x / (beta : ℝ)) ≤ mag beta y
  · have he_x : e ≤ cexp beta fexp x := by
      have hx_mag : mag beta (x / (beta : ℝ)) ≤ mag beta x := by
        have h := mag_minus1 (beta := beta) (z := x) hβ h_nonzero
        omega
      simpa [e, he, FloatSpec.Core.Generic_fmt.cexp] using
        (FloatSpec.Core.Generic_fmt.Monotone_exp.mono (fexp := fexp) hx_mag)
    have he_y : e ≤ cexp beta fexp y := by
      simpa [e, he, FloatSpec.Core.Generic_fmt.cexp] using
        (FloatSpec.Core.Generic_fmt.Monotone_exp.mono (fexp := fexp) hmag)
    rcases generic_format_shift (beta := beta) (fexp := fexp)
        (x := x) (e := e) hβ hx he_x with ⟨mx, hx_repr⟩
    rcases generic_format_shift (beta := beta) (fexp := fexp)
        (x := y) (e := e) hβ hy he_y with ⟨my, hy_repr⟩
    have hsum :
        x + y =
          _root_.F2R
            (FloatSpec.Core.Defs.FlocqFloat.mk (mx + my) e :
              FloatSpec.Core.Defs.FlocqFloat beta) := by
      rw [hx_repr, hy_repr]
      simp [_root_.F2R, FloatSpec.Core.Defs.F2R, Int.cast_add]
      ring
    rcases round_repr_same_exp (beta := beta) (fexp := fexp)
        (rnd := rnd) hβ (mx + my) e with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    simpa [e, he, hsum] using hm
  · have hmy_le : mag beta y ≤ mag beta x - 2 := by
      have hx_mag : mag beta (x / (beta : ℝ)) = mag beta x - 1 := by
        exact (mag_minus1 (beta := beta) (z := x) hβ h_nonzero).symm
      have hlt : mag beta y < mag beta (x / (beta : ℝ)) := lt_of_not_ge hmag
      omega
    have hmag_sum :
        mag beta x - 1 ≤ mag beta (x + y) := by
      have htrip := FloatSpec.Core.Raux.mag_plus_ge
        (beta := beta) (x := x) (y := y) hβ h_nonzero hmy_le
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip True.intro
    have he_sum : e ≤ cexp beta fexp (x + y) := by
      have hx_mag : mag beta (x / (beta : ℝ)) = mag beta x - 1 := by
        exact (mag_minus1 (beta := beta) (z := x) hβ h_nonzero).symm
      have hle : mag beta (x / (beta : ℝ)) ≤ mag beta (x + y) := by
        omega
      simpa [e, he, FloatSpec.Core.Generic_fmt.cexp] using
        (FloatSpec.Core.Generic_fmt.Monotone_exp.mono (fexp := fexp) hle)
    set c : Int := cexp beta fexp (x + y) with hc
    set n : Int := rnd (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp (x + y)) with hn
    refine ⟨n * beta ^ (c - e).natAbs, ?_⟩
    have hround_c :
        FloatSpec.Core.Generic_fmt.roundR beta fexp rnd (x + y) =
          _root_.F2R
            (FloatSpec.Core.Defs.FlocqFloat.mk n c :
              FloatSpec.Core.Defs.FlocqFloat beta) := by
      change
        (((rnd (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp (x + y)) : Int) : ℝ) *
            (beta : ℝ) ^ (cexp beta fexp (x + y))) =
          (((n : Int) : ℝ) * (beta : ℝ) ^ c)
      rw [← hn, ← hc]
    have hchange :
        _root_.F2R
            (FloatSpec.Core.Defs.FlocqFloat.mk n c :
              FloatSpec.Core.Defs.FlocqFloat beta) =
          _root_.F2R
            (FloatSpec.Core.Defs.FlocqFloat.mk (n * beta ^ (c - e).natAbs) e :
              FloatSpec.Core.Defs.FlocqFloat beta) := by
      have h :=
        FloatSpec.Core.Float_prop.F2R_change_exp
          (beta := beta)
          (f := FloatSpec.Core.Defs.FlocqFloat.mk n c)
              (e' := e) hβ (by simpa [c, hc] using he_sum)
      change
        ((n : ℝ) * (beta : ℝ) ^ c) =
          (((n * beta ^ (c - e).natAbs : Int) : ℝ) * (beta : ℝ) ^ e)
      simpa [_root_.F2R, FloatSpec.Core.Defs.F2R] using h
    exact hround_c.trans hchange

variable [FloatSpec.Core.Ulp.Exp_not_FTZ fexp]

/-- Round plus greater equal ulp -/
theorem round_plus_ge_ulp (x y : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (h_nonzero : FloatSpec.Core.Generic_fmt.roundR beta fexp rnd (x + y) ≠ 0) :
  ulp beta fexp (x / (beta : ℝ)) ≤ |FloatSpec.Core.Generic_fmt.roundR beta fexp rnd (x + y)| := by
  classical
  by_cases hx0 : x = 0
  · have hround :
        FloatSpec.Core.Generic_fmt.roundR beta fexp rnd (x + y) = y := by
      have hfix := FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp) (rnd := rnd) (x := y) hβ hy
      simpa [hx0] using hfix
    have hy0 : y ≠ 0 := by
      intro hy_zero
      have hzero :
          FloatSpec.Core.Generic_fmt.roundR beta fexp rnd (x + y) = 0 := by
        rw [hround, hy_zero]
      exact h_nonzero hzero
    have hulps :
        ulp beta fexp 0 ≤ ulp beta fexp y := by
      have htrip := FloatSpec.Core.Ulp.ulp_ge_ulp_0
        (beta := beta) (fexp := fexp) (x := y) hβ
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip True.intro
    have hulp_y :
        ulp beta fexp y ≤ |y| := by
      have htrip := FloatSpec.Core.Ulp.ulp_le_abs
        (beta := beta) (fexp := fexp) (x := y) hy0 hy
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip True.intro
    have hzero_div : x / (beta : ℝ) = 0 := by simp [hx0]
    simpa [hzero_div, hround] using le_trans hulps hulp_y
  · rcases round_plus_F2R (beta := beta) (fexp := fexp) (rnd := rnd)
      (x := x) (y := y) hβ hx hy hx0 with ⟨m, hm⟩
    by_cases hm0 : m = 0
    · exfalso
      apply h_nonzero
      simpa [hm, hm0, _root_.F2R, FloatSpec.Core.Defs.F2R]
    · have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hβ
      have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
      have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos_real
      have hx_div_ne : x / (beta : ℝ) ≠ 0 := div_ne_zero hx0 hbne
      set e : Int := cexp beta fexp (x / (beta : ℝ)) with he
      have hulp :
          ulp beta fexp (x / (beta : ℝ)) = (beta : ℝ) ^ e := by
        have htrip := FloatSpec.Core.Ulp.ulp_neq_0
          (beta := beta) (fexp := fexp) (x := x / (beta : ℝ)) hx_div_ne
        simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, e, he]
          using htrip True.intro
      have hpow_nonneg : 0 ≤ (beta : ℝ) ^ e := le_of_lt (zpow_pos hbpos_real e)
      have hm_abs_ge_one : (1 : ℝ) ≤ |(m : ℝ)| := by
        have hm_abs_pos : 0 < Int.natAbs m := Int.natAbs_pos.mpr hm0
        have : (1 : Nat) ≤ Int.natAbs m := Nat.succ_le_of_lt hm_abs_pos
        have hcast : (1 : ℝ) ≤ (Int.natAbs m : ℝ) := by exact_mod_cast this
        simpa [Nat.cast_natAbs, Int.cast_abs] using hcast
      have hmul :
          (beta : ℝ) ^ e ≤ |(m : ℝ)| * (beta : ℝ) ^ e := by
        have h := mul_le_mul_of_nonneg_right hm_abs_ge_one hpow_nonneg
        simpa using h
      calc
        ulp beta fexp (x / (beta : ℝ)) = (beta : ℝ) ^ e := hulp
        _ ≤ |(m : ℝ)| * (beta : ℝ) ^ e := hmul
        _ = |FloatSpec.Core.Generic_fmt.roundR beta fexp rnd (x + y)| := by
          rw [hm]
          simp [_root_.F2R, FloatSpec.Core.Defs.F2R, abs_mul,
            abs_of_nonneg hpow_nonneg, e, he]

-- Section: FLT plus bounds

/-- Round FLT plus greater equal bound -/
theorem round_FLT_plus_ge (x y : ℝ) (e : Int)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (hy : generic_format beta (FLT_exp emin prec) y)
  (h_bound : FloatSpec.Core.Raux.bpow beta (e + prec) ≤ |x|)
  (h_nonzero : FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x + y) ≠ 0) :
  FloatSpec.Core.Raux.bpow beta e ≤
    |FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x + y)| := by
  classical
  haveI : FloatSpec.Core.Ulp.Exp_not_FTZ (FLT_exp emin prec) := by
    refine ⟨?_⟩
    intro k
    have hprec : 0 < prec := (Prec_gt_0.pos : 0 < prec)
    let a : Int := max (k - prec) emin
    change max (a + 1 - prec) emin ≤ a
    exact max_le (by omega) (by simp [a])
  have hx0 : x ≠ 0 := by
    intro hx0
    have hpow_pos : 0 < FloatSpec.Core.Raux.bpow beta (e + prec) := by
      have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hβ
      have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
      simpa [FloatSpec.Core.Raux.bpow] using zpow_pos hbpos_real (e + prec)
    have : FloatSpec.Core.Raux.bpow beta (e + prec) ≤ 0 := by
      simpa [hx0] using h_bound
    exact (not_lt_of_ge this) hpow_pos
  have hx_div0 : x / (beta : ℝ) ≠ 0 := by
    have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hβ
    have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
    exact div_ne_zero hx0 (ne_of_gt hbpos_real)
  have hx_upper : |x| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) := by
    have h := FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := x) hβ hx0
    simpa [FloatSpec.Core.Raux.abs_val] using h True.intro
  have hmag_lt : e + prec < FloatSpec.Core.Raux.mag beta x := by
    have hpow_lt :
        (beta : ℝ) ^ (e + prec) <
          (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) :=
      lt_of_le_of_lt (by simpa [FloatSpec.Core.Raux.bpow] using h_bound) hx_upper
    have h := FloatSpec.Core.Raux.lt_bpow beta (e + prec)
      (FloatSpec.Core.Raux.mag beta x) hβ hpow_lt
    simpa using h True.intro
  have hmag_div := mag_minus1 (beta := beta) (z := x) hβ hx0
  have he_cexp : e ≤ cexp beta (FLT_exp emin prec) (x / (beta : ℝ)) := by
    have : e ≤ FloatSpec.Core.Raux.mag beta (x / (beta : ℝ)) - prec := by
      have hmag_div' :
          FloatSpec.Core.Raux.mag beta (x / (beta : ℝ)) =
            FloatSpec.Core.Raux.mag beta x - 1 := hmag_div.symm
      omega
    simp [cexp, FLT_exp, FloatSpec.Core.Generic_fmt.cexp,
      FloatSpec.Core.FLT.FLT_exp]
    exact Or.inl this
  have hulp :
      ulp beta (FLT_exp emin prec) (x / (beta : ℝ)) =
        (beta : ℝ) ^ (cexp beta (FLT_exp emin prec) (x / (beta : ℝ))) := by
    have h := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := FLT_exp emin prec)
      (x := x / (beta : ℝ)) (hx := hx_div0)
    simpa [cexp] using h True.intro
  have hbpow_le_ulp :
      FloatSpec.Core.Raux.bpow beta e ≤
        ulp beta (FLT_exp emin prec) (x / (beta : ℝ)) := by
    have h := FloatSpec.Core.Raux.bpow_le beta e
      (cexp beta (FLT_exp emin prec) (x / (beta : ℝ))) hβ he_cexp
    simpa [FloatSpec.Core.Raux.bpow, hulp] using h True.intro
  haveI : FloatSpec.Core.Generic_fmt.Monotone_exp (FLT_exp emin prec) := by
    simpa [FLT_exp] using
      (inferInstance : FloatSpec.Core.Generic_fmt.Monotone_exp (FloatSpec.Core.FLT.FLT_exp prec emin))
  exact le_trans hbpow_le_ulp
    (round_plus_ge_ulp (beta := beta) (fexp := FLT_exp emin prec)
      (rnd := rnd) (x := x) (y := y) hβ hx hy h_nonzero)

/-- Round FLT plus greater equal bound (alternative) -/
lemma round_FLT_plus_ge' (x y : ℝ) (e : Int)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (hy : generic_format beta (FLT_exp emin prec) y)
  (h1 : x ≠ 0 → FloatSpec.Core.Raux.bpow beta (e + prec) ≤ |x|)
  (h2 : x = 0 → y ≠ 0 → FloatSpec.Core.Raux.bpow beta e ≤ |y|)
  (h_nonzero : FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x + y) ≠ 0) :
  FloatSpec.Core.Raux.bpow beta e ≤
    |FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x + y)| := by
  by_cases hx0 : x = 0
  · have hy0 : y ≠ 0 := by
      intro hy0
      apply h_nonzero
      have hfix := FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd) (x := y) hβ hy
      simpa [hx0, hy0] using hfix
    have hround :
        FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x + y) = y := by
      have hfix := FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd) (x := y) hβ hy
      simpa [hx0] using hfix
    simpa [hround] using h2 hx0 hy0
  · exact round_FLT_plus_ge (beta := beta) (rnd := rnd)
      (emin := emin) (prec := prec) (x := x) (y := y) (e := e)
      hβ hx hy (h1 hx0) h_nonzero

/-- Round FLX plus greater equal bound -/
theorem round_FLX_plus_ge (x y : ℝ) (e : Int)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLX_exp prec) x)
  (hy : generic_format beta (FLX_exp prec) y)
  (h_bound : FloatSpec.Core.Raux.bpow beta (e + prec) ≤ |x|)
  (h_nonzero : FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec) rnd (x + y) ≠ 0) :
  FloatSpec.Core.Raux.bpow beta e ≤
    |FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec) rnd (x + y)| := by
  classical
  haveI : FloatSpec.Core.Ulp.Exp_not_FTZ (FLX_exp prec) := by
    refine ⟨?_⟩
    intro k
    have hprec : 0 < prec := (Prec_gt_0.pos : 0 < prec)
    simp [FLX_exp, FloatSpec.Core.FLX.FLX_exp]
    omega
  have hx0 : x ≠ 0 := by
    intro hx0
    have hpow_pos : 0 < FloatSpec.Core.Raux.bpow beta (e + prec) := by
      have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hβ
      have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
      simpa [FloatSpec.Core.Raux.bpow] using zpow_pos hbpos_real (e + prec)
    have : FloatSpec.Core.Raux.bpow beta (e + prec) ≤ 0 := by
      simpa [hx0] using h_bound
    exact (not_lt_of_ge this) hpow_pos
  have hx_div0 : x / (beta : ℝ) ≠ 0 := by
    have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hβ
    have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
    exact div_ne_zero hx0 (ne_of_gt hbpos_real)
  have hx_upper : |x| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) := by
    have h := FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := x) hβ hx0
    simpa [FloatSpec.Core.Raux.abs_val] using h True.intro
  have hmag_lt : e + prec < FloatSpec.Core.Raux.mag beta x := by
    have hpow_lt :
        (beta : ℝ) ^ (e + prec) <
          (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) :=
      lt_of_le_of_lt (by simpa [FloatSpec.Core.Raux.bpow] using h_bound) hx_upper
    have h := FloatSpec.Core.Raux.lt_bpow beta (e + prec)
      (FloatSpec.Core.Raux.mag beta x) hβ hpow_lt
    simpa using h True.intro
  have hmag_div := mag_minus1 (beta := beta) (z := x) hβ hx0
  have he_cexp : e ≤ cexp beta (FLX_exp prec) (x / (beta : ℝ)) := by
    have hmag_div' :
        FloatSpec.Core.Raux.mag beta (x / (beta : ℝ)) =
          FloatSpec.Core.Raux.mag beta x - 1 := hmag_div.symm
    simp [cexp, FLX_exp, FloatSpec.Core.Generic_fmt.cexp,
      FloatSpec.Core.FLX.FLX_exp]
    omega
  have hulp :
      ulp beta (FLX_exp prec) (x / (beta : ℝ)) =
        (beta : ℝ) ^ (cexp beta (FLX_exp prec) (x / (beta : ℝ))) := by
    have h := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := FLX_exp prec)
      (x := x / (beta : ℝ)) (hx := hx_div0)
    simpa [cexp] using h True.intro
  have hbpow_le_ulp :
      FloatSpec.Core.Raux.bpow beta e ≤
        ulp beta (FLX_exp prec) (x / (beta : ℝ)) := by
    have h := FloatSpec.Core.Raux.bpow_le beta e
      (cexp beta (FLX_exp prec) (x / (beta : ℝ))) hβ he_cexp
    simpa [FloatSpec.Core.Raux.bpow, hulp] using h True.intro
  haveI : FloatSpec.Core.Generic_fmt.Monotone_exp (FLX_exp prec) := by
    simpa [FLX_exp] using
      (inferInstance : FloatSpec.Core.Generic_fmt.Monotone_exp (FloatSpec.Core.FLX.FLX_exp prec))
  exact le_trans hbpow_le_ulp
    (round_plus_ge_ulp (beta := beta) (fexp := FLX_exp prec)
      (rnd := rnd) (x := x) (y := y) hβ hx hy h_nonzero)

-- Section: Plus error bounds

/-- Plus error bounded by left operand -/
lemma plus_error_le_l (x y : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) :
  |FloatSpec.Calc.Round.round beta fexp (Znearest choice) (x + y) - (x + y)| ≤ |x| := by
  classical
  let s : ℝ := x + y
  let r : ℝ :=
    FloatSpec.Core.Generic_fmt.roundR beta fexp
      (FloatSpec.Core.Generic_fmt.Znearest choice) s
  have hN := roundR_Znearest_N_pt (beta := beta) (fexp := fexp)
    (choice := choice) (x := s) hβ
  have hdist0 := hN.2 y (by simpa [s] using hy)
  have hy_dist : |y - s| = |x| := by
    have hsub : y - s = -x := by
      dsimp [s]
      ring
    rw [hsub, abs_neg]
  simpa [FloatSpec.Calc.Round.round, FloatSpec.Compat.Scaffold.ZnearestMode,
    Znearest, s, r, hy_dist] using hdist0

/-- Plus error bounded by right operand -/
lemma plus_error_le_r (x y : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) :
  |FloatSpec.Calc.Round.round beta fexp (Znearest choice) (x + y) - (x + y)| ≤ |y| := by
  have h := plus_error_le_l (beta := beta) (fexp := fexp) (choice := choice)
    y x hβ hy hx
  simpa [add_comm] using h
