import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import Mathlib.Data.Real.Basic

-- Round to odd properties
-- Translated from Coq file: flocq/src/Prop/Round_odd.v

open Real
open FloatSpec.Calc.Round

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

/-- Rnd_odd_pt: pointwise specification of round-to-odd witness

    Mirrors Coq's `Rnd_odd_pt` predicate: `f` is in format and either
    equals `x`, or it is a DN/UP witness and corresponds to a canonical
    float with an odd mantissa. -/
def Rnd_odd_pt (x f : ℝ) : Prop :=
  generic_format beta fexp f ∧
  (f = x ∨
    ((FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x f ∨
      FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x f) ∧
     ∃ g : FloatSpec.Core.Defs.FlocqFloat beta,
       f = (FloatSpec.Core.Defs.F2R g) ∧
       FloatSpec.Core.Generic_fmt.canonical beta fexp g ∧
       g.Fnum % 2 ≠ 0))

/-- Round to odd rounding mode -/
noncomputable def Zodd : ℝ → Int := fun x =>
  let n := FloatSpec.Core.Raux.Zfloor x
  if x = (n : ℝ) then n
  else if n % 2 = 0 then FloatSpec.Core.Raux.Zceil x
  else n

/-- `Calc.Round` wrapper for Flocq's round-to-odd integer mode. -/
noncomputable def oddMode : FloatSpec.Calc.Round.Mode where
  rnd := Zodd
  rnd_zero := by
    simp [Zodd, FloatSpec.Core.Raux.Zfloor]

private lemma Zodd_of_int_floor (x : ℝ)
    (h : x = ((FloatSpec.Core.Raux.Zfloor x : Int) : ℝ)) :
    Zodd x = FloatSpec.Core.Raux.Zfloor x := by
  unfold Zodd
  rw [if_pos h]

private lemma Zodd_of_floor_even (x : ℝ)
    (h : ¬ x = ((FloatSpec.Core.Raux.Zfloor x : Int) : ℝ))
    (he : (FloatSpec.Core.Raux.Zfloor x : Int) % 2 = 0) :
    Zodd x = FloatSpec.Core.Raux.Zceil x := by
  unfold Zodd
  rw [if_neg h, if_pos he]

private lemma Zodd_of_floor_odd (x : ℝ)
    (h : ¬ x = ((FloatSpec.Core.Raux.Zfloor x : Int) : ℝ))
    (he : ¬ (FloatSpec.Core.Raux.Zfloor x : Int) % 2 = 0) :
    Zodd x = FloatSpec.Core.Raux.Zfloor x := by
  unfold Zodd
  rw [if_neg h, if_neg he]

private lemma Zfloor_le_Zodd (x : ℝ) :
    FloatSpec.Core.Raux.Zfloor x ≤ Zodd x := by
  classical
  by_cases h : x = ((FloatSpec.Core.Raux.Zfloor x : Int) : ℝ)
  · rw [Zodd_of_int_floor x h]
  · by_cases he : (FloatSpec.Core.Raux.Zfloor x : Int) % 2 = 0
    · rw [Zodd_of_floor_even x h he]
      have hleR :
          ((FloatSpec.Core.Raux.Zfloor x : Int) : ℝ) ≤
            ((FloatSpec.Core.Raux.Zceil x : Int) : ℝ) :=
        (Int.floor_le x).trans (Int.le_ceil x)
      exact_mod_cast hleR
    · rw [Zodd_of_floor_odd x h he]

private lemma Zodd_le_Zceil (x : ℝ) :
    Zodd x ≤ FloatSpec.Core.Raux.Zceil x := by
  classical
  by_cases h : x = ((FloatSpec.Core.Raux.Zfloor x : Int) : ℝ)
  · rw [Zodd_of_int_floor x h]
    have hleR :
        ((FloatSpec.Core.Raux.Zfloor x : Int) : ℝ) ≤
          ((FloatSpec.Core.Raux.Zceil x : Int) : ℝ) :=
      (Int.floor_le x).trans (Int.le_ceil x)
    exact_mod_cast hleR
  · by_cases he : (FloatSpec.Core.Raux.Zfloor x : Int) % 2 = 0
    · rw [Zodd_of_floor_even x h he]
    · rw [Zodd_of_floor_odd x h he]
      have hleR :
          ((FloatSpec.Core.Raux.Zfloor x : Int) : ℝ) ≤
            ((FloatSpec.Core.Raux.Zceil x : Int) : ℝ) :=
        (Int.floor_le x).trans (Int.le_ceil x)
      exact_mod_cast hleR

private lemma Zodd_monotone (x y : ℝ) (hxy : x ≤ y) : Zodd x ≤ Zodd y := by
  classical
  set fx := FloatSpec.Core.Raux.Zfloor x
  set fy := FloatSpec.Core.Raux.Zfloor y
  have hfx_le_fy : fx ≤ fy := by
    have hreal : (fx : ℝ) ≤ y := by
      have hfl : (fx : ℝ) ≤ x := by
        simpa [fx, FloatSpec.Core.Raux.Zfloor] using Int.floor_le x
      exact hfl.trans hxy
    exact (Int.le_floor).mpr (by simpa [fy, FloatSpec.Core.Raux.Zfloor] using hreal)
  by_cases hxint : x = (fx : ℝ)
  · have hxz : Zodd x = fx := by
      simpa [fx] using Zodd_of_int_floor x (by simpa [fx] using hxint)
    rw [hxz]
    exact le_trans hfx_le_fy (by simpa [fy] using Zfloor_le_Zodd y)
  · by_cases hxe : fx % 2 = 0
    · have hxz : Zodd x = FloatSpec.Core.Raux.Zceil x := by
        simpa [fx] using
          Zodd_of_floor_even x (by simpa [fx] using hxint) (by simpa [fx] using hxe)
      have hceilx_eq : FloatSpec.Core.Raux.Zceil x = fx + 1 := by
        have hne : ((FloatSpec.Core.Raux.Zfloor x : Int) : ℝ) ≠ x := by
          intro h
          exact hxint (by simpa [fx] using h.symm)
        have h := (FloatSpec.Core.Raux.Zceil_floor_neq x hne) True.intro
        simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, fx] using h
      rw [hxz, hceilx_eq]
      by_cases hnext_le_y : ((fx + 1 : Int) : ℝ) ≤ y
      · have hnext_le_fy : fx + 1 ≤ fy :=
          (Int.le_floor).mpr
            (by simpa [fy, FloatSpec.Core.Raux.Zfloor] using hnext_le_y)
        exact le_trans hnext_le_fy (by simpa [fy] using Zfloor_le_Zodd y)
      · have hy_lt_next : y < ((fx + 1 : Int) : ℝ) := lt_of_not_ge hnext_le_y
        have hfy_eq : fy = fx := by
          apply le_antisymm
          · have hfy_lt_next : fy < fx + 1 := by
              have hfyR_lt : (fy : ℝ) < ((fx + 1 : Int) : ℝ) := by
                have hfy_le_y : (fy : ℝ) ≤ y := by
                  simpa [fy, FloatSpec.Core.Raux.Zfloor] using Int.floor_le y
                exact lt_of_le_of_lt hfy_le_y hy_lt_next
              exact_mod_cast hfyR_lt
            omega
          · exact hfx_le_fy
        have hy_nonint : ¬ y = (fy : ℝ) := by
          intro hyi
          have hfx_lt_x : (fx : ℝ) < x := by
            have hfl : (fx : ℝ) ≤ x := by
              simpa [fx, FloatSpec.Core.Raux.Zfloor] using Int.floor_le x
            exact lt_of_le_of_ne hfl (Ne.symm hxint)
          have : y = (fx : ℝ) := by
            simpa [hfy_eq] using hyi
          linarith
        have hyz : Zodd y = FloatSpec.Core.Raux.Zceil y := by
          simpa [fy, hfy_eq, hxe] using
            Zodd_of_floor_even y (by simpa [fy] using hy_nonint)
              (by simpa [fy, hfy_eq] using hxe)
        have hceily_eq : FloatSpec.Core.Raux.Zceil y = fx + 1 := by
          have hne : ((FloatSpec.Core.Raux.Zfloor y : Int) : ℝ) ≠ y := by
            intro h
            exact hy_nonint (by simpa [fy] using h.symm)
          have h := (FloatSpec.Core.Raux.Zceil_floor_neq y hne) True.intro
          simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, fy, hfy_eq] using h
        rw [hyz, hceily_eq]
    · have hxz : Zodd x = fx := by
        simpa [fx] using
          Zodd_of_floor_odd x (by simpa [fx] using hxint) (by simpa [fx] using hxe)
      rw [hxz]
      exact le_trans hfx_le_fy (by simpa [fy] using Zfloor_le_Zodd y)

private lemma emod_two_ne_zero_neg {m : Int} (h : m % 2 ≠ 0) : (-m) % 2 ≠ 0 := by
  intro hn
  have hdiv_neg : (2 : Int) ∣ -m :=
    (Int.dvd_iff_emod_eq_zero (a := (2 : Int)) (b := -m)).mpr hn
  have hdiv : (2 : Int) ∣ m := by
    simpa using (Int.dvd_neg.mp hdiv_neg)
  exact h ((Int.dvd_iff_emod_eq_zero (a := (2 : Int)) (b := m)).mp hdiv)

private lemma Zodd_opp (x : ℝ) : Zodd (-x) = -Zodd x := by
  classical
  set fx := FloatSpec.Core.Raux.Zfloor x
  have hfloor_neg : FloatSpec.Core.Raux.Zfloor (-x) = -FloatSpec.Core.Raux.Zceil x := by
    simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil, Int.floor_neg]
  have hceil_neg : FloatSpec.Core.Raux.Zceil (-x) = -FloatSpec.Core.Raux.Zfloor x := by
    simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil, Int.ceil_neg]
  by_cases hxint : x = (fx : ℝ)
  · have hxz : Zodd x = fx := by
      simpa [fx] using Zodd_of_int_floor x (by simpa [fx] using hxint)
    have hneg_int : -x = ((FloatSpec.Core.Raux.Zfloor (-x) : Int) : ℝ) := by
      rw [hxint]
      have hfloor : Int.floor (-(fx : ℝ)) = -fx := by
        simpa [Int.cast_neg] using Int.floor_intCast (z := -fx)
      simpa [FloatSpec.Core.Raux.Zfloor, hfloor]
    rw [Zodd_of_int_floor (-x) hneg_int, hxz, hfloor_neg]
    have hceil_eq : FloatSpec.Core.Raux.Zceil x = fx := by
      simpa [fx, FloatSpec.Core.Raux.Zceil] using
        congrArg Int.ceil hxint
    rw [hceil_eq]
  · have hx_nonint_floor : ¬ x = ((FloatSpec.Core.Raux.Zfloor x : Int) : ℝ) := by
      simpa [fx] using hxint
    have hceil_x : FloatSpec.Core.Raux.Zceil x = fx + 1 := by
      have hne : ((FloatSpec.Core.Raux.Zfloor x : Int) : ℝ) ≠ x := by
        intro h
        exact hx_nonint_floor h.symm
      have h := (FloatSpec.Core.Raux.Zceil_floor_neq x hne) True.intro
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, fx] using h
    have hneg_nonint :
        ¬ -x = ((FloatSpec.Core.Raux.Zfloor (-x) : Int) : ℝ) := by
      intro hneg_int
      apply hx_nonint_floor
      have hxceil : x = ((FloatSpec.Core.Raux.Zceil x : Int) : ℝ) := by
        have htmp : -x = (-(FloatSpec.Core.Raux.Zceil x) : Int) := by
          simpa [hfloor_neg] using hneg_int
        exact neg_inj.mp (by simpa using htmp)
      have hfloor_eq_ceil : FloatSpec.Core.Raux.Zfloor x = FloatSpec.Core.Raux.Zceil x := by
        simpa [FloatSpec.Core.Raux.Zfloor] using congrArg Int.floor hxceil
      rw [hfloor_eq_ceil]
      exact hxceil
    by_cases hxeven : fx % 2 = 0
    · have hxz : Zodd x = FloatSpec.Core.Raux.Zceil x := by
        simpa [fx] using
          Zodd_of_floor_even x hx_nonint_floor (by simpa [fx] using hxeven)
      have hneg_odd : ¬ (FloatSpec.Core.Raux.Zfloor (-x) : Int) % 2 = 0 := by
        rw [hfloor_neg, hceil_x]
        omega
      have hnegz : Zodd (-x) = FloatSpec.Core.Raux.Zfloor (-x) :=
        Zodd_of_floor_odd (-x) hneg_nonint hneg_odd
      rw [hnegz, hxz, hfloor_neg]
    · have hxz : Zodd x = fx := by
        simpa [fx] using Zodd_of_floor_odd x hx_nonint_floor (by simpa [fx] using hxeven)
      have hneg_even : (FloatSpec.Core.Raux.Zfloor (-x) : Int) % 2 = 0 := by
        rw [hfloor_neg, hceil_x]
        omega
      have hnegz : Zodd (-x) = FloatSpec.Core.Raux.Zceil (-x) :=
        Zodd_of_floor_even (-x) hneg_nonint hneg_even
      rw [hnegz, hxz, hceil_neg]

/-- Round to odd is a valid rounding -/
instance : FloatSpec.Core.Generic_fmt.Valid_rnd (Zodd) := by
  refine { Zrnd_le := ?mono, Zrnd_IZR := ?onInt }
  · intro x y hxy
    exact Zodd_monotone x y hxy
  · intro n
    have hf : FloatSpec.Core.Raux.Zfloor (n : ℝ) = n := by
      simpa [FloatSpec.Core.Raux.Zfloor] using Int.floor_intCast (n := n)
    have h : (n : ℝ) = ((FloatSpec.Core.Raux.Zfloor (n : ℝ) : Int) : ℝ) := by
      rw [hf]
    rw [Zodd_of_int_floor (n : ℝ) h, hf]

/-- If `x` is not exactly an integer (`Zfloor x`), then the result of
    rounding-to-odd (`Zodd x`) is odd. This mirrors Coq's `Zrnd_odd_Zodd`. -/
lemma Zrnd_odd_Zodd (x : ℝ)
  (hx : x ≠ (((FloatSpec.Core.Raux.Zfloor x) : Int) : ℝ)) :
  (Zodd x) % 2 = 1 := by
  classical
  set n := FloatSpec.Core.Raux.Zfloor x
  have hx' : ¬ x = (n : ℝ) := by
    intro h
    exact hx (by simpa [n] using h)
  unfold Zodd
  simp only [n, hx', ↓reduceIte]
  by_cases heven : n % 2 = 0
  · have hne : ((FloatSpec.Core.Raux.Zfloor x : Int) : ℝ) ≠ x := by
      intro h
      exact hx h.symm
    have hceil :
        FloatSpec.Core.Raux.Zceil x = FloatSpec.Core.Raux.Zfloor x + 1 := by
      have h := (FloatSpec.Core.Raux.Zceil_floor_neq x hne) True.intro
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using h
    have hceil_n : FloatSpec.Core.Raux.Zceil x = n + 1 := by
      simpa [n] using hceil
    rw [hceil_n]
    omega
  · have hcases := Int.emod_two_eq_zero_or_one n
    omega

/-- Integer floor of a translated real: `Zfloor (n + y) = n + Zfloor y`. -/
lemma Zfloor_plus (n : Int) (y : ℝ) :
  (FloatSpec.Core.Raux.Zfloor ((n : ℝ) + y)) =
    n + (FloatSpec.Core.Raux.Zfloor y) := by
  simpa [FloatSpec.Core.Raux.Zfloor] using
    (Int.floor_intCast_add (R := ℝ) n y)

/-- Integer ceil of a translated real: `Zceil (n + y) = n + Zceil y`. -/
lemma Zceil_plus (n : Int) (y : ℝ) :
  (FloatSpec.Core.Raux.Zceil ((n : ℝ) + y)) =
    n + (FloatSpec.Core.Raux.Zceil y) := by
  calc
    FloatSpec.Core.Raux.Zceil ((n : ℝ) + y)
        = Int.ceil (y + (n : ℝ)) := by
          simp [FloatSpec.Core.Raux.Zceil, add_comm]
    _ = FloatSpec.Core.Raux.Zceil y + n := by
          simpa [FloatSpec.Core.Raux.Zceil] using
            (Int.ceil_add_intCast (R := ℝ) y n)
    _ = n + FloatSpec.Core.Raux.Zceil y := by omega

/-- Parity is invariant by absolute value: `(abs z)` is even iff `z` is even.
    Coq counterpart: `Zeven_abs`. -/
lemma Zeven_abs (z : Int) :
  ((Int.ofNat (Int.natAbs z)) % 2 = 0) ↔ (z % 2 = 0) := by
  calc
    ((Int.ofNat (Int.natAbs z)) % 2 = 0) ↔
        (2 : Int) ∣ Int.ofNat (Int.natAbs z) := by
      exact (Int.dvd_iff_emod_eq_zero
        (a := (2 : Int)) (b := Int.ofNat (Int.natAbs z))).symm
    _ ↔ (2 : Int) ∣ z := by
      exact Int.dvd_natAbs (a := (2 : Int)) (b := z)
    _ ↔ z % 2 = 0 := by
      exact Int.dvd_iff_emod_eq_zero (a := (2 : Int)) (b := z)

/-- Sum with round-to-odd at an even integer point.
    Coq counterpart: `Zrnd_odd_plus`. -/
lemma Zrnd_odd_plus (x y : ℝ)
  (hx : x = (((FloatSpec.Core.Raux.Zfloor x) : Int) : ℝ))
  (heven : ((FloatSpec.Core.Raux.Zfloor x) : Int) % 2 = 0) :
  ((Zodd (x + y) : Int) : ℝ) = x + ((Zodd y : Int) : ℝ) := by
  classical
  set n := FloatSpec.Core.Raux.Zfloor x
  set m := FloatSpec.Core.Raux.Zfloor y
  have hx' : x = (n : ℝ) := by simpa [n] using hx
  have hn_even : n % 2 = 0 := by simpa [n] using heven
  have hfloor_xy : FloatSpec.Core.Raux.Zfloor (x + y) = n + m := by
    calc
      FloatSpec.Core.Raux.Zfloor (x + y)
          = FloatSpec.Core.Raux.Zfloor ((n : ℝ) + y) := by rw [hx']
      _ = n + FloatSpec.Core.Raux.Zfloor y := Zfloor_plus n y
      _ = n + m := by simp [m]
  have hceil_xy : FloatSpec.Core.Raux.Zceil (x + y) =
      n + FloatSpec.Core.Raux.Zceil y := by
    calc
      FloatSpec.Core.Raux.Zceil (x + y)
          = FloatSpec.Core.Raux.Zceil ((n : ℝ) + y) := by rw [hx']
      _ = n + FloatSpec.Core.Raux.Zceil y := Zceil_plus n y
  by_cases hyint : y = (m : ℝ)
  · have hxyint : x + y =
        ((FloatSpec.Core.Raux.Zfloor (x + y) : Int) : ℝ) := by
      rw [hfloor_xy, hx', hyint]
      norm_num [Int.cast_add]
    have hzxy : Zodd (x + y) = FloatSpec.Core.Raux.Zfloor (x + y) :=
      Zodd_of_int_floor (x + y) hxyint
    have hzy : Zodd y = FloatSpec.Core.Raux.Zfloor y :=
      Zodd_of_int_floor y (by simpa [m] using hyint)
    rw [hzxy, hzy, hfloor_xy, hx']
    simp [m, Int.cast_add]
  · have hy_nonint_floor : ¬ y = ((FloatSpec.Core.Raux.Zfloor y : Int) : ℝ) := by
      simpa [m] using hyint
    have hxy_nonint : ¬ x + y =
        ((FloatSpec.Core.Raux.Zfloor (x + y) : Int) : ℝ) := by
      intro hxyi
      apply hyint
      have hcast : x + y = ((n + m : Int) : ℝ) := by
        simpa [hfloor_xy] using hxyi
      rw [hx'] at hcast
      have hcast' : (n : ℝ) + y = (n : ℝ) + (m : ℝ) := by
        simpa [Int.cast_add] using hcast
      exact add_left_cancel hcast'
    by_cases hm_even : m % 2 = 0
    · have hsum_even : (FloatSpec.Core.Raux.Zfloor (x + y) : Int) % 2 = 0 := by
        rw [hfloor_xy]
        omega
      have hzy : Zodd y = FloatSpec.Core.Raux.Zceil y :=
        Zodd_of_floor_even y hy_nonint_floor (by simpa [m] using hm_even)
      have hzxy : Zodd (x + y) = FloatSpec.Core.Raux.Zceil (x + y) :=
        Zodd_of_floor_even (x + y) hxy_nonint hsum_even
      rw [hzxy, hzy, hceil_xy, hx']
      simp [Int.cast_add]
    · have hsum_odd : ¬ (FloatSpec.Core.Raux.Zfloor (x + y) : Int) % 2 = 0 := by
        rw [hfloor_xy]
        omega
      have hzy : Zodd y = FloatSpec.Core.Raux.Zfloor y :=
        Zodd_of_floor_odd y hy_nonint_floor (by simpa [m] using hm_even)
      have hzxy : Zodd (x + y) = FloatSpec.Core.Raux.Zfloor (x + y) :=
        Zodd_of_floor_odd (x + y) hxy_nonint hsum_odd
      rw [hzxy, hzy, hfloor_xy, hx']
      simp [m, Int.cast_add]

/-- Negation invariance for the `Rnd_odd_pt` predicate.
    Coq counterpart: `Rnd_odd_pt_opp_inv`. -/
theorem Rnd_odd_pt_opp_inv (x f : ℝ) :
  Rnd_odd_pt (beta := beta) (fexp := fexp) (-x) (-f) →
  Rnd_odd_pt (beta := beta) (fexp := fexp) x f := by
  intro h
  rcases h with ⟨hf_fmt_neg, hcases⟩
  have hFopp :
      ∀ y, generic_format beta fexp y → generic_format beta fexp (-y) := by
    intro y hy
    exact FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := fexp) (x := y) hy
  have hf_fmt : generic_format beta fexp f := by
    have h := hFopp (-f) hf_fmt_neg
    simpa using h
  refine ⟨hf_fmt, ?_⟩
  rcases hcases with hexact | hround
  · left
    linarith
  · right
    rcases hround with ⟨hdu, hg⟩
    constructor
    · rcases hdu with hdn | hup
      · right
        have hUP := FloatSpec.Core.Round_pred.Rnd_UP_pt_opp_pure
          (generic_format beta fexp) (-x) (-f) hFopp hdn
        simpa using hUP
      · left
        rcases hup with ⟨Hf, hxle_f, hmin⟩
        refine ⟨hf_fmt, ?_, ?_⟩
        · linarith
        · intro g HgF Hgx
          have hneg_g_fmt : generic_format beta fexp (-g) := hFopp g HgF
          have hnegx_le_negg : -x ≤ -g := by linarith
          have hnegf_le_negg : -f ≤ -g := hmin (-g) hneg_g_fmt hnegx_le_negg
          linarith
    · rcases hg with ⟨g, hfg, hcan, hodd⟩
      refine ⟨FloatSpec.Core.Defs.FlocqFloat.mk (-g.Fnum) g.Fexp, ?_, ?_, ?_⟩
      · have hf2r_neg :
            FloatSpec.Core.Defs.F2R
                (FloatSpec.Core.Defs.FlocqFloat.mk (-g.Fnum) g.Fexp :
                  FloatSpec.Core.Defs.FlocqFloat beta)
              = -FloatSpec.Core.Defs.F2R g := by
          simp [FloatSpec.Core.Defs.F2R, neg_mul]
        calc
          f = -(-f) := by ring
          _ = -(FloatSpec.Core.Defs.F2R g) := by rw [hfg]
          _ = FloatSpec.Core.Defs.F2R
                (FloatSpec.Core.Defs.FlocqFloat.mk (-g.Fnum) g.Fexp :
                  FloatSpec.Core.Defs.FlocqFloat beta) := hf2r_neg.symm
      · exact FloatSpec.Core.Generic_fmt.canonical_opp
          beta fexp g.Fnum g.Fexp hcan
      · exact emod_two_ne_zero_neg hodd

/-- Negation commutes with round-to-odd.
    Coq counterpart: `round_odd_opp`. -/
theorem round_odd_opp (x : ℝ) (hβ : 1 < beta) :
  FloatSpec.Calc.Round.round beta fexp oddMode (-x)
  = - FloatSpec.Calc.Round.round beta fexp oddMode x := by
  have hopp := FloatSpec.Core.Generic_fmt.roundR_opp
    (beta := beta) (fexp := fexp) (rnd := Zodd) (x := x) hβ
  have hmode :
      FloatSpec.Calc.Round.round beta fexp oddMode (-x)
        = -FloatSpec.Core.Generic_fmt.roundR beta fexp (FloatSpec.Core.Generic_fmt.Zrnd_opp Zodd) x := by
    simpa [FloatSpec.Calc.Round.round, oddMode] using hopp
  have hrnd_ext :
      FloatSpec.Core.Generic_fmt.Zrnd_opp Zodd = Zodd := by
    funext y
    simp [FloatSpec.Core.Generic_fmt.Zrnd_opp, Zodd_opp]
  rw [hmode, hrnd_ext]
  rfl

/-- Uniqueness of the round-to-odd witness.
    Coq counterpart: `Rnd_odd_pt_unique`. -/
theorem Rnd_odd_pt_unique (x f1 f2 : ℝ) :
  FloatSpec.Core.RoundNE.Exists_NE beta fexp →
  1 < beta →
  Rnd_odd_pt (beta := beta) (fexp := fexp) x f1 →
  Rnd_odd_pt (beta := beta) (fexp := fexp) x f2 →
  f1 = f2 := by
  intro hNE hβ h1 h2
  haveI : FloatSpec.Core.RoundNE.Exists_NE beta fexp := hNE
  let F : ℝ → Prop := generic_format beta fexp
  have DN_unique (x f1 f2 : ℝ)
      (h1 : FloatSpec.Core.Defs.Rnd_DN_pt F x f1)
      (h2 : FloatSpec.Core.Defs.Rnd_DN_pt F x f2) : f1 = f2 := by
    exact le_antisymm (h2.2.2 f1 h1.1 h1.2.1) (h1.2.2 f2 h2.1 h2.2.1)
  have UP_unique (x f1 f2 : ℝ)
      (h1 : FloatSpec.Core.Defs.Rnd_UP_pt F x f1)
      (h2 : FloatSpec.Core.Defs.Rnd_UP_pt F x f2) : f1 = f2 := by
    exact le_antisymm (h1.2.2 f2 h2.1 h2.2.1) (h2.2.2 f1 h1.1 h1.2.1)
  have odd_mod_one (m : Int) (hm : m % 2 ≠ 0) : m % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one m with h0 | h1
    · exact False.elim (hm h0)
    · exact h1
  rcases h1 with ⟨Ff1, H1⟩
  rcases h2 with ⟨Ff2, H2⟩
  classical
  cases FloatSpec.Core.Generic_fmt.generic_format_EM beta fexp x with
  | inl Fx =>
      have hf1x : f1 = x := by
        rcases H1 with H1eq | ⟨H1du, _⟩
        · exact H1eq
        · rcases H1du with H1dn | H1up
          · exact le_antisymm H1dn.2.1 (H1dn.2.2 x Fx le_rfl)
          · exact le_antisymm (H1up.2.2 x Fx le_rfl) H1up.2.1
      have hf2x : f2 = x := by
        rcases H2 with H2eq | ⟨H2du, _⟩
        · exact H2eq
        · rcases H2du with H2dn | H2up
          · exact le_antisymm H2dn.2.1 (H2dn.2.2 x Fx le_rfl)
          · exact le_antisymm (H2up.2.2 x Fx le_rfl) H2up.2.1
      exact hf1x.trans hf2x.symm
  | inr HxNF =>
      rcases H1 with H1eq | ⟨H1du, g1, Hg1, Cg1, Og1⟩
      · exact False.elim (HxNF (by simpa [H1eq] using Ff1))
      rcases H2 with H2eq | ⟨H2du, g2, Hg2, Cg2, Og2⟩
      · exact False.elim (HxNF (by simpa [H2eq] using Ff2))
      rcases H1du with H1dn | H1up
      · rcases H2du with H2dn | H2up
        · exact DN_unique x f1 f2 (by simpa [F] using H1dn) (by simpa [F] using H2dn)
        · have hpar_prop : FloatSpec.Core.RoundNE.DN_UP_parity_prop beta fexp := by
            have htrip := FloatSpec.Core.RoundNE.DN_UP_parity_generic
              (beta := beta) (fexp := fexp)
            simpa [FloatSpec.Core.RoundNE.DN_UP_parity_generic_check, pure,
              decide_eq_true_iff] using (htrip hβ)
          rcases hpar_prop x f1 f2 HxNF H1dn H2up with
            ⟨gd, gu, Hgd, Hgu, Cgd, Cgu, Hpar⟩
          have hgd_eq : gd = g1 := by
            apply FloatSpec.Core.Generic_fmt.canonical_unique
              (beta := beta) (hbeta := hβ) (fexp := fexp)
            · exact Cgd
            · exact Cg1
            · rw [← Hgd, ← Hg1]
          have hgu_eq : gu = g2 := by
            apply FloatSpec.Core.Generic_fmt.canonical_unique
              (beta := beta) (hbeta := hβ) (fexp := fexp)
            · exact Cgu
            · exact Cg2
            · rw [← Hgu, ← Hg2]
          rw [hgd_eq, hgu_eq] at Hpar
          exact False.elim (Hpar (by rw [odd_mod_one g1.Fnum Og1, odd_mod_one g2.Fnum Og2]))
      · rcases H2du with H2dn | H2up
        · have hpar_prop : FloatSpec.Core.RoundNE.DN_UP_parity_prop beta fexp := by
            have htrip := FloatSpec.Core.RoundNE.DN_UP_parity_generic
              (beta := beta) (fexp := fexp)
            simpa [FloatSpec.Core.RoundNE.DN_UP_parity_generic_check, pure,
              decide_eq_true_iff] using (htrip hβ)
          rcases hpar_prop x f2 f1 HxNF H2dn H1up with
            ⟨gd, gu, Hgd, Hgu, Cgd, Cgu, Hpar⟩
          have hgd_eq : gd = g2 := by
            apply FloatSpec.Core.Generic_fmt.canonical_unique
              (beta := beta) (hbeta := hβ) (fexp := fexp)
            · exact Cgd
            · exact Cg2
            · rw [← Hgd, ← Hg2]
          have hgu_eq : gu = g1 := by
            apply FloatSpec.Core.Generic_fmt.canonical_unique
              (beta := beta) (hbeta := hβ) (fexp := fexp)
            · exact Cgu
            · exact Cg1
            · rw [← Hgu, ← Hg1]
          rw [hgd_eq, hgu_eq] at Hpar
          exact False.elim (Hpar (by rw [odd_mod_one g2.Fnum Og2, odd_mod_one g1.Fnum Og1]))
        · exact UP_unique x f1 f2 (by simpa [F] using H1up) (by simpa [F] using H2up)

/-- Round to odd maintains format when appropriate -/
theorem generic_format_round_odd (x : ℝ) (hβ : 1 < beta) :
  generic_format beta fexp (FloatSpec.Calc.Round.round beta fexp oddMode x) := by
  simpa [FloatSpec.Calc.Round.round, oddMode] using
    FloatSpec.Core.Generic_fmt.generic_format_roundR
      (beta := beta) (fexp := fexp) (rnd := Zodd) (x := x) hβ

variable (fexpe : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexpe]

/-- If the auxiliary exponent `fexpe` is pointwise below `fexp - 2`,
    then any `fexp`-generic number is also `fexpe`-generic.
    Coq counterpart: `generic_format_fexpe_fexp`. -/
lemma generic_format_fexpe_fexp
  (hβ : 1 < beta)
  (hrel : ∀ e, fexpe e ≤ fexp e - 2)
  (x : ℝ) :
  generic_format beta fexp x → generic_format beta fexpe x := by
  intro hx
  exact FloatSpec.Core.Generic_fmt.generic_inclusion_mag
    (beta := beta) (fexp1 := fexp) (fexp2 := fexpe) x hβ
    (by
      intro _
      have h := hrel (FloatSpec.Core.Raux.mag beta x)
      omega)
    hx

/-- Zodd summation at even-base aligned points.
    Coq counterpart: `Zrnd_odd_plus'`.

    If `beta` is even and `x` sits exactly on a radix grid point
    `n * beta^e` with `1 ≤ e`, then rounding-to-odd satisfies
    `Zodd (x + y) = x + Zodd y` (as integers mapped to reals).
    We mirror the Coq statement and leave the proof as a placeholder. -/
theorem Zrnd_odd_plus' (Ebeta : ∃ n : Int, beta = 2 * n)
  (hβ : 1 < beta)
  (x y : ℝ)
  (hx : ∃ n e : Int, x = (n : ℝ) * (beta : ℝ) ^ e ∧ 1 ≤ e) :
  ((Zodd (x + y) : Int) : ℝ) = x + ((Zodd y : Int) : ℝ) := by
  rcases hx with ⟨n, e, hx, he⟩
  have he_nonneg : 0 ≤ e := le_trans (by decide : (0 : Int) ≤ 1) he
  have he_nat : (e.toNat : Int) = e := Int.toNat_of_nonneg he_nonneg
  set k : Int := n * beta ^ e.toNat with hk
  have hpow_cast : (beta : ℝ) ^ e = ((beta ^ e.toNat : Int) : ℝ) := by
    have hzpow_toNat : (beta : ℝ) ^ e = (beta : ℝ) ^ e.toNat := by
      rw [← Int.toNat_of_nonneg he_nonneg]
      exact zpow_ofNat _ _
    have hcast_pow : (beta : ℝ) ^ e.toNat = ((beta ^ e.toNat : Int) : ℝ) := by
      rw [← Int.cast_pow]
    exact hzpow_toNat.trans hcast_pow
  have hx_int : x = (k : ℝ) := by
    rw [hx, hpow_cast, hk]
    norm_num [Int.cast_mul]
  have hx_floor : x = ((FloatSpec.Core.Raux.Zfloor x : Int) : ℝ) := by
    rw [hx_int]
    simp [FloatSpec.Core.Raux.Zfloor]
  have hk_even : k % 2 = 0 := by
    rcases Ebeta with ⟨b, hb⟩
    have hpow_even : (beta ^ e.toNat) % 2 = 0 := by
      obtain ⟨q, hq⟩ : ∃ q, e.toNat = q + 1 := by
        refine ⟨e.toNat - 1, ?_⟩
        have hpos : 0 < e.toNat := by
          have hcast_pos : (0 : Int) < (e.toNat : Int) := by omega
          exact Nat.cast_pos.mp hcast_pos
        omega
      rw [hq, pow_succ, hb]
      have hmod : (2 * (b * (2 * b) ^ q)) % 2 = 0 :=
        Int.mul_emod_right 2 (b * (2 * b) ^ q)
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmod
    have hmulmod : (n * beta ^ e.toNat) % 2 =
        ((n % 2) * ((beta ^ e.toNat) % 2)) % 2 := by
      simpa using (Int.mul_emod n (beta ^ e.toNat) 2)
    simpa [hk, hpow_even, hmulmod]
  have hfloor_even : (FloatSpec.Core.Raux.Zfloor x : Int) % 2 = 0 := by
    have hfloor_eq : (FloatSpec.Core.Raux.Zfloor x : Int) = k := by
      rw [hx_int]
      simp [FloatSpec.Core.Raux.Zfloor]
    simpa [hfloor_eq] using hk_even
  exact Zrnd_odd_plus (x := x) (y := y) hx_floor hfloor_even

/-!
  Coq Section Fcore_rnd_odd: auxiliary witnesses d, u, and midpoint m.
  The retained lemmas assume DN/UP witnesses `d` and `u`.
-/

private lemma Rnd_DN_pt_unique_pure
    (F : ℝ → Prop) (x f₁ f₂ : ℝ)
    (h₁ : FloatSpec.Core.Defs.Rnd_DN_pt F x f₁)
    (h₂ : FloatSpec.Core.Defs.Rnd_DN_pt F x f₂) :
    f₁ = f₂ := by
  rcases h₁ with ⟨F₁, h₁le, h₁max⟩
  rcases h₂ with ⟨F₂, h₂le, h₂max⟩
  exact le_antisymm (h₂max f₁ F₁ h₁le) (h₁max f₂ F₂ h₂le)

private lemma roundR_floor_DN_pt_local
    (x : ℝ) (hβ : 1 < beta) :
    FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x
      (FloatSpec.Core.Generic_fmt.roundR (beta := beta) (fexp := fexp)
        (fun y => FloatSpec.Core.Raux.Zfloor y) x) := by
  classical
  refine ⟨?hfmt, ?hle, ?hmax⟩
  · simpa [FloatSpec.Core.Generic_fmt.rnd_floor] using
      FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := beta) (fexp := fexp)
        (rnd := FloatSpec.Core.Generic_fmt.rnd_floor) (x := x) hβ
  · have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    set e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x with he
    set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x with hsm
    have hfloor_le : ((FloatSpec.Core.Raux.Zfloor sm : Int) : ℝ) ≤ sm := by
      simpa [FloatSpec.Core.Raux.Zfloor] using (Int.floor_le sm)
    have hmul := mul_le_mul_of_nonneg_right hfloor_le
      (le_of_lt (zpow_pos hbposR e))
    have hscaled : sm * (beta : ℝ) ^ e = x := by
      have htrip := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
        (beta := beta) (fexp := fexp) (x := x)
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, sm, hsm, e, he]
        using htrip hβ
    have hdn_eval :
        FloatSpec.Core.Generic_fmt.roundR beta fexp
            (fun y => FloatSpec.Core.Raux.Zfloor y) x =
          ((FloatSpec.Core.Raux.Zfloor sm : Int) : ℝ) * (beta : ℝ) ^ e := by
      simpa [FloatSpec.Core.Generic_fmt.roundR, sm, hsm, e, he]
    calc
      FloatSpec.Core.Generic_fmt.roundR beta fexp
          (fun y => FloatSpec.Core.Raux.Zfloor y) x
          = ((FloatSpec.Core.Raux.Zfloor sm : Int) : ℝ) * (beta : ℝ) ^ e := hdn_eval
      _ ≤ sm * (beta : ℝ) ^ e := hmul
      _ = x := hscaled
  · intro g hgF hg_le
    simpa [FloatSpec.Core.Generic_fmt.rnd_floor] using
      FloatSpec.Core.Generic_fmt.roundR_ge_generic
        (beta := beta) (fexp := fexp) (rnd := FloatSpec.Core.Generic_fmt.rnd_floor)
        (x := g) (y := x) hβ hgF hg_le

private lemma roundR_ceil_UP_pt_local
    (x : ℝ) (hβ : 1 < beta) :
    FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x
      (FloatSpec.Core.Generic_fmt.roundR (beta := beta) (fexp := fexp)
        (fun y => FloatSpec.Core.Raux.Zceil y) x) := by
  classical
  refine ⟨?hfmt, ?hle, ?hmin⟩
  · simpa [FloatSpec.Core.Generic_fmt.rnd_ceil] using
      FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := beta) (fexp := fexp)
        (rnd := FloatSpec.Core.Generic_fmt.rnd_ceil) (x := x) hβ
  · have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    set e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x with he
    set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x with hsm
    have hceil_ge : sm ≤ ((FloatSpec.Core.Raux.Zceil sm : Int) : ℝ) := by
      simpa [FloatSpec.Core.Raux.Zceil] using (Int.le_ceil sm)
    have hmul := mul_le_mul_of_nonneg_right hceil_ge
      (le_of_lt (zpow_pos hbposR e))
    have hscaled : sm * (beta : ℝ) ^ e = x := by
      have htrip := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
        (beta := beta) (fexp := fexp) (x := x)
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, sm, hsm, e, he]
        using htrip hβ
    have hup_eval :
        FloatSpec.Core.Generic_fmt.roundR beta fexp
            (fun y => FloatSpec.Core.Raux.Zceil y) x =
          ((FloatSpec.Core.Raux.Zceil sm : Int) : ℝ) * (beta : ℝ) ^ e := by
      simpa [FloatSpec.Core.Generic_fmt.roundR, sm, hsm, e, he]
    calc
      x = sm * (beta : ℝ) ^ e := hscaled.symm
      _ ≤ ((FloatSpec.Core.Raux.Zceil sm : Int) : ℝ) * (beta : ℝ) ^ e := hmul
      _ = FloatSpec.Core.Generic_fmt.roundR beta fexp
          (fun y => FloatSpec.Core.Raux.Zceil y) x := hup_eval.symm
  · intro g hgF hx_le_g
    simpa [FloatSpec.Core.Generic_fmt.rnd_ceil] using
      FloatSpec.Core.Generic_fmt.roundR_le_generic
        (beta := beta) (fexp := fexp) (rnd := FloatSpec.Core.Generic_fmt.rnd_ceil)
        (x := x) (y := g) hβ hgF hx_le_g

/-- Coq: `d_eq`
    Equality between the DN-witness value and rounding with `Zfloor`.
    Mirrors: `F2R d = round beta fexp Zfloor x`.

    We state it over Core’s `roundR` with the concrete rounding function `Zfloor`.
-/
lemma d_eq (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) (hβ : 1 < beta) :
  F2R d =
    (FloatSpec.Core.Generic_fmt.roundR (beta := beta) (fexp := fexp)
        (fun y => (FloatSpec.Core.Raux.Zfloor y)) x) := by
  exact Rnd_DN_pt_unique_pure (generic_format beta fexp) x (F2R d)
    (FloatSpec.Core.Generic_fmt.roundR (beta := beta) (fexp := fexp)
      (fun y => FloatSpec.Core.Raux.Zfloor y) x)
    Hd (roundR_floor_DN_pt_local (beta := beta) (fexp := fexp) x hβ)

/-- Coq: `u_eq`
    Equality between the UP-witness value and rounding with `Zceil`.

    Mirrors: `F2R u = round beta fexp Zceil x`. We use the Core `roundR`
    helper with the integer rounding function `Zceil` (as `Int` via `.run`). -/
lemma u_eq (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) (hβ : 1 < beta) :
  F2R u =
    (FloatSpec.Core.Generic_fmt.roundR (beta := beta) (fexp := fexp)
        (fun y => (FloatSpec.Core.Raux.Zceil y)) x) := by
  exact FloatSpec.Core.Round_pred.Rnd_UP_pt_unique_pure (generic_format beta fexp) x (F2R u)
    (FloatSpec.Core.Generic_fmt.roundR (beta := beta) (fexp := fexp)
      (fun y => FloatSpec.Core.Raux.Zceil y) x)
    Hu (roundR_ceil_UP_pt_local (beta := beta) (fexp := fexp) x hβ)

/-- Coq: `d_ge_0`
    From the DN-witness hypothesis, the down-rounded value `F2R d` is
    nonnegative when `0 < x`. -/
lemma d_ge_0 (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) :
  0 ≤ F2R d := by
  have hzero_fmt : generic_format beta fexp 0 :=
    FloatSpec.Core.Generic_fmt.generic_format_0_run (beta := beta) (fexp := fexp)
  have hzero_le_x : (0 : ℝ) ≤ x := le_of_lt xPos
  exact Hd.2.2 0 hzero_fmt hzero_le_x

/-- Midpoint between the DN/UP witnesses used in Coq's section `Fcore_rnd_odd`.
    We keep it as a plain real number constructed from `d` and `u`. -/
noncomputable def m (d u : FloatSpec.Core.Defs.FlocqFloat beta) : ℝ :=
  (F2R d + F2R u) / 2

/-- Coq: `d_le_m`. The down-rounded value is below the midpoint `m`. -/
lemma d_le_m (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) :
  F2R d ≤ m (beta := beta) d u := by
  have hdu : F2R d ≤ F2R u := le_trans Hd.2.1 Hu.2.1
  unfold m
  linarith

/-- Coq: `m_le_u`. The midpoint `m` is below the up-rounded value. -/
lemma m_le_u (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) :
  m (beta := beta) d u ≤ F2R u := by
  have hdu : F2R d ≤ F2R u := le_trans Hd.2.1 Hu.2.1
  unfold m
  linarith

/-- Coq: `DN_odd_d_aux`.
    For any `z` between `F2R d` and `F2R u`, the DN rounding predicate
    selects `F2R d`. -/
lemma DN_odd_d_aux (x z : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (Hz : F2R d ≤ z ∧ z < F2R u) :
  FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) z (F2R d) := by
  refine ⟨Hd.1, Hz.1, ?_⟩
  intro g hg hgz
  by_cases hxg : x ≤ g
  · have hug : F2R u ≤ g := Hu.2.2 g hg hxg
    linarith
  · have hgx : g ≤ x := le_of_lt (lt_of_not_ge hxg)
    exact Hd.2.2 g hg hgx

/-- Coq: `UP_odd_d_aux`.
    For any `z` strictly between `F2R d` and `F2R u` (up to `≤` on the right),
    the UP rounding predicate selects `F2R u`. -/
lemma UP_odd_d_aux (x z : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x)
  (Hz : F2R d < z ∧ z ≤ F2R u) :
  FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) z (F2R u) := by
  refine ⟨Hu.1, Hz.2, ?_⟩
  intro g hg hzg
  by_cases hgx : g ≤ x
  · have hgd : g ≤ F2R d := Hd.2.2 g hg hgx
    linarith
  · have hxg : x ≤ g := le_of_lt (lt_of_not_ge hgx)
    exact Hu.2.2 g hg hxg
