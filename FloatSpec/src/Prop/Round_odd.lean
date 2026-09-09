import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import Mathlib.Data.Real.Basic

set_option linter.style.haveILetI false

attribute [local simp] FloatSpec.Core.Generic_fmt.rnd_floor
  FloatSpec.Core.Generic_fmt.rnd_ceil

private theorem rnd_floor_eq :
    FloatSpec.Core.Generic_fmt.rnd_floor = FloatSpec.Core.Raux.Zfloor := rfl

private theorem rnd_ceil_eq :
    FloatSpec.Core.Generic_fmt.rnd_ceil = FloatSpec.Core.Raux.Zceil := rfl

attribute [local simp] rnd_floor_eq rnd_ceil_eq

-- Round to odd properties
-- Translated from Coq file: flocq/src/Prop/Round_odd.v

open Real
open FloatSpec.Calc.Round

variable (beta : Int) [ValidRadix beta]
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp fexp]

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

/-- Coq (`Round_odd.v`): `Definition Rnd_odd`.

A rounding function is round-to-odd when every output satisfies the
pointwise round-to-odd predicate. -/
def Rnd_odd (rnd : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, Rnd_odd_pt (beta := beta) (fexp := fexp) x (rnd x)

/-- Round to odd rounding mode -/
noncomputable def Zodd : ℝ → Int := fun x =>
  let n := FloatSpec.Core.Raux.Zfloor x
  if x = (n : ℝ) then n
  else if n % 2 = 0 then FloatSpec.Core.Raux.Zceil x
  else n

/-- Coq (`Round_odd.v`): `Definition Zrnd_odd`.

Public Flocq-name wrapper for the integer round-to-odd mode. -/
noncomputable abbrev Zrnd_odd : ℝ → Int := Zodd

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

/-- Coq `valid_rnd_odd`: round to odd is a valid integer rounding. -/
noncomputable instance valid_rnd_odd :
    FloatSpec.Core.Generic_fmt.Valid_rnd Zrnd_odd := by
  change FloatSpec.Core.Generic_fmt.Valid_rnd Zodd
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
      refine ⟨FloatSpec.Core.Defs.FlocqFloat.mk (-g.Fnum) g.Fexp,
        ?_, ?_, ?_⟩
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
          (beta := beta) (fexp := fexp)
          g.Fnum g.Fexp hcan
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
        · have hpar_prop : FloatSpec.Core.RoundNE.DN_UP_parity_payload beta fexp := by
            have htrip := FloatSpec.Core.RoundNE.DN_UP_parity_generic_payload
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
        · have hpar_prop : FloatSpec.Core.RoundNE.DN_UP_parity_payload beta fexp := by
            have htrip := FloatSpec.Core.RoundNE.DN_UP_parity_generic_payload
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
variable [FloatSpec.Core.Generic_fmt.Valid_exp fexpe]

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

/-- Coq: `exists_even_fexp_lt`.

    If `x` has a float representative whose exponent is strictly above
    `c (mag beta x)`, and the radix is even, then `x` has a canonical
    representative at exponent `c (mag beta x)` with an even mantissa. -/
lemma exists_even_fexp_lt
  (Ebeta : ∃ n : Int, beta = 2 * n)
  (hβ : 1 < beta)
  (c : Int → Int) (x : ℝ)
  (h : ∃ g : FloatSpec.Core.Defs.FlocqFloat beta,
      F2R g = x ∧ c (FloatSpec.Core.Raux.mag beta x) < g.Fexp) :
  ∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
    F2R f = x ∧
      FloatSpec.Core.Generic_fmt.canonical beta c f ∧ f.Fnum % 2 = 0 := by
  classical
  rcases h with ⟨g, hgx, hlt_exp⟩
  let e0 : Int := c (FloatSpec.Core.Raux.mag beta x)
  let k : Nat := Int.toNat (g.Fexp - e0)
  have hdiff_pos : 0 < g.Fexp - e0 := by omega
  have hdiff_nonneg : 0 ≤ g.Fexp - e0 := le_of_lt hdiff_pos
  have hk_cast : (k : Int) = g.Fexp - e0 := by
    simpa [k] using Int.toNat_of_nonneg hdiff_nonneg
  let f : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk (g.Fnum * beta ^ k) e0
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposℝ : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbneℝ : (beta : ℝ) ≠ 0 := ne_of_gt hbposℝ
  have hf_val : F2R f = x := by
    calc
      F2R f
          = (((g.Fnum * beta ^ k : Int) : ℝ) * (beta : ℝ) ^ e0) := by
              rfl
      _ = ((g.Fnum : ℝ) * (beta : ℝ) ^ (k : Int) *
            (beta : ℝ) ^ e0) := by
              simp [f, Int.cast_mul, Int.cast_pow, zpow_natCast]
      _ = ((g.Fnum : ℝ) * (beta : ℝ) ^ (g.Fexp - e0) *
            (beta : ℝ) ^ e0) := by
              rw [hk_cast]
      _ = (g.Fnum : ℝ) * ((beta : ℝ) ^ (g.Fexp - e0) *
            (beta : ℝ) ^ e0) := by ring
      _ = (g.Fnum : ℝ) * (beta : ℝ) ^ ((g.Fexp - e0) + e0) := by
              rw [zpow_add₀ hbneℝ]
      _ = F2R g := by
              simp [F2R, sub_add_cancel]
      _ = x := hgx
  refine ⟨f, hf_val, ?_, ?_⟩
  · change e0 = c (FloatSpec.Core.Raux.mag beta (F2R f))
    rw [hf_val]
  · rcases Ebeta with ⟨b, hb⟩
    have hk_pos : 0 < k := by
      have hcast_pos : (0 : Int) < (k : Int) := by
        simpa [hk_cast] using hdiff_pos
      exact Nat.cast_pos.mp hcast_pos
    obtain ⟨q, hq⟩ : ∃ q : Nat, k = q + 1 := by
      exact ⟨k - 1, (Nat.succ_pred_eq_of_pos hk_pos).symm⟩
    have hpow_even : beta ^ k % 2 = 0 := by
      rw [hq, pow_succ, hb]
      have hmod : (2 * (b * (2 * b) ^ q)) % 2 = 0 :=
        Int.mul_emod_right 2 (b * (2 * b) ^ q)
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmod
    have hmulmod :
        (g.Fnum * beta ^ k) % 2 =
          ((g.Fnum % 2) * ((beta ^ k) % 2)) % 2 := by
      simpa using (Int.mul_emod g.Fnum (beta ^ k) 2)
    simp [f, hmulmod, hpow_even]

/-- Zodd summation at even-base aligned points.
    Coq counterpart: `Zrnd_odd_plus'`.

    If `beta` is even and `x` sits exactly on a radix grid point
    `n * beta^e` with `1 ≤ e`, then rounding-to-odd satisfies
    `Zodd (x + y) = x + Zodd y` (as integers mapped to reals).
    This mirrors the Coq statement with an explicit integer-grid witness. -/
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

private lemma roundR_nearest_eq_DN_of_lt_mid
  (choice : Int → Bool) (x d u : ℝ)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x u)
  (hβ : 1 < beta)
  (hmid : x < (d + u) / 2) :
  FloatSpec.Core.Generic_fmt.roundR beta fexp
      (FloatSpec.Core.Generic_fmt.Znearest choice) x = d := by
  classical
  let dn := FloatSpec.Core.Generic_fmt.roundR beta fexp
    FloatSpec.Core.Generic_fmt.rnd_floor x
  let up := FloatSpec.Core.Generic_fmt.roundR beta fexp
    FloatSpec.Core.Generic_fmt.rnd_ceil x
  have hDN_round : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x dn := by
    simpa [dn, FloatSpec.Core.Generic_fmt.rnd_floor] using
      roundR_floor_DN_pt_local (beta := beta) (fexp := fexp) x hβ
  have hUP_round : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x up := by
    simpa [up, FloatSpec.Core.Generic_fmt.rnd_ceil] using
      roundR_ceil_UP_pt_local (beta := beta) (fexp := fexp) x hβ
  have hdn_eq : dn = d :=
    Rnd_DN_pt_unique_pure (generic_format beta fexp) x dn d hDN_round Hd
  have hup_eq : up = u :=
    FloatSpec.Core.Round_pred.Rnd_UP_pt_unique_pure
      (generic_format beta fexp) x up u hUP_round Hu
  set e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x with he
  set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x with hsm
  set n : Int := FloatSpec.Core.Raux.Zfloor sm with hn
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbposR e
  have hscaled : sm * (beta : ℝ) ^ e = x := by
    have htrip := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
      (beta := beta) (fexp := fexp) (x := x)
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, sm, hsm, e, he]
      using htrip hβ
  have hdn_eval : dn = (n : ℝ) * (beta : ℝ) ^ e := by
    simpa [dn, FloatSpec.Core.Generic_fmt.roundR, FloatSpec.Core.Generic_fmt.rnd_floor,
      sm, hsm, e, he, n, hn]
  have hup_eval : up = ((FloatSpec.Core.Raux.Zceil sm : Int) : ℝ) * (beta : ℝ) ^ e := by
    simpa [up, FloatSpec.Core.Generic_fmt.roundR, FloatSpec.Core.Generic_fmt.rnd_ceil,
      sm, hsm, e, he]
  have hmid_round : x < (dn + up) / 2 := by
    simpa [hdn_eq, hup_eq] using hmid
  have hfloor_le : (n : ℝ) ≤ sm := by
    simpa [n, hn, FloatSpec.Core.Raux.Zfloor] using Int.floor_le sm
  have hnonneg : 0 ≤ sm - (n : ℝ) := sub_nonneg.mpr hfloor_le
  have hceil_le_floor_add_one :
      FloatSpec.Core.Raux.Zceil sm ≤ n + 1 := by
    have hsm_lt : sm < (n : ℝ) + 1 := by
      simpa [n, hn, FloatSpec.Core.Raux.Zfloor] using Int.lt_floor_add_one sm
    exact Int.ceil_le.mpr (by simpa [Int.cast_add, Int.cast_one] using le_of_lt hsm_lt)
  have hgap_le :
      up - dn ≤ (beta : ℝ) ^ e := by
    have hceil_cast :
        ((FloatSpec.Core.Raux.Zceil sm : Int) : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast hceil_le_floor_add_one
    have hdiff_le :
        ((FloatSpec.Core.Raux.Zceil sm : Int) : ℝ) - (n : ℝ) ≤ 1 := by
      linarith
    have hmul := mul_le_mul_of_nonneg_right hdiff_le (le_of_lt hpow_pos)
    calc
      up - dn =
          (((FloatSpec.Core.Raux.Zceil sm : Int) : ℝ) - (n : ℝ)) *
            (beta : ℝ) ^ e := by
              rw [hup_eval, hdn_eval]
              ring
      _ ≤ 1 * (beta : ℝ) ^ e := hmul
      _ = (beta : ℝ) ^ e := by ring
  have hdist_lt : |sm - (n : ℝ)| < (1 / 2 : ℝ) := by
    have hx_minus_dn_lt : x - dn < (up - dn) / 2 := by
      linarith [hmid_round]
    have hx_minus_dn_scaled :
        x - dn = (sm - (n : ℝ)) * (beta : ℝ) ^ e := by
      rw [← hscaled, hdn_eval]
      ring
    have hlt_scaled :
        (sm - (n : ℝ)) * (beta : ℝ) ^ e < (1 / 2) * (beta : ℝ) ^ e := by
      nlinarith [hpow_pos, hgap_le, hx_minus_dn_lt, hx_minus_dn_scaled]
    have hlt : sm - (n : ℝ) < (1 / 2 : ℝ) := by
      nlinarith [hpow_pos, hlt_scaled]
    simpa [abs_of_nonneg hnonneg] using hlt
  have hZ :
      FloatSpec.Core.Generic_fmt.Znearest choice sm = n := by
    have h := FloatSpec.Core.Generic_fmt.Znearest_imp choice sm n hdist_lt
    simpa [Std.Do.wp,
      Std.Do.PostCond.noThrow, Id.run, pure] using h
  calc
    FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest choice) x
        = ((FloatSpec.Core.Generic_fmt.Znearest choice sm : Int) : ℝ) *
            (beta : ℝ) ^ e := by
              simp [FloatSpec.Core.Generic_fmt.roundR, sm, hsm, e, he]
    _ = (n : ℝ) * (beta : ℝ) ^ e := by rw [hZ]
    _ = dn := hdn_eval.symm
    _ = d := hdn_eq

private lemma roundR_nearest_eq_UP_of_mid_lt
  (choice : Int → Bool) (x d u : ℝ)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x u)
  (hβ : 1 < beta)
  (hmid : (d + u) / 2 < x) :
  FloatSpec.Core.Generic_fmt.roundR beta fexp
      (FloatSpec.Core.Generic_fmt.Znearest choice) x = u := by
  classical
  let dn := FloatSpec.Core.Generic_fmt.roundR beta fexp
    FloatSpec.Core.Generic_fmt.rnd_floor x
  let up := FloatSpec.Core.Generic_fmt.roundR beta fexp
    FloatSpec.Core.Generic_fmt.rnd_ceil x
  have hDN_round : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x dn := by
    simpa [dn, FloatSpec.Core.Generic_fmt.rnd_floor] using
      roundR_floor_DN_pt_local (beta := beta) (fexp := fexp) x hβ
  have hUP_round : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x up := by
    simpa [up, FloatSpec.Core.Generic_fmt.rnd_ceil] using
      roundR_ceil_UP_pt_local (beta := beta) (fexp := fexp) x hβ
  have hdn_eq : dn = d :=
    Rnd_DN_pt_unique_pure (generic_format beta fexp) x dn d hDN_round Hd
  have hup_eq : up = u :=
    FloatSpec.Core.Round_pred.Rnd_UP_pt_unique_pure
      (generic_format beta fexp) x up u hUP_round Hu
  set e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x with he
  set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x with hsm
  set n : Int := FloatSpec.Core.Raux.Zceil sm with hn
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbposR e
  have hscaled : sm * (beta : ℝ) ^ e = x := by
    have htrip := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
      (beta := beta) (fexp := fexp) (x := x)
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, sm, hsm, e, he]
      using htrip hβ
  have hdn_eval :
      dn = ((FloatSpec.Core.Raux.Zfloor sm : Int) : ℝ) * (beta : ℝ) ^ e := by
    simpa [dn, FloatSpec.Core.Generic_fmt.roundR, FloatSpec.Core.Generic_fmt.rnd_floor,
      sm, hsm, e, he]
  have hup_eval : up = (n : ℝ) * (beta : ℝ) ^ e := by
    simpa [up, FloatSpec.Core.Generic_fmt.roundR, FloatSpec.Core.Generic_fmt.rnd_ceil,
      sm, hsm, e, he, n, hn]
  have hmid_round : (dn + up) / 2 < x := by
    simpa [hdn_eq, hup_eq] using hmid
  have hceil_ge : sm ≤ (n : ℝ) := by
    simpa [n, hn, FloatSpec.Core.Raux.Zceil] using Int.le_ceil sm
  have hnonneg : 0 ≤ (n : ℝ) - sm := sub_nonneg.mpr hceil_ge
  have hceil_le_floor_add_one :
      n ≤ FloatSpec.Core.Raux.Zfloor sm + 1 := by
    have hsm_lt : sm < ((FloatSpec.Core.Raux.Zfloor sm : Int) : ℝ) + 1 := by
      simpa [FloatSpec.Core.Raux.Zfloor] using Int.lt_floor_add_one sm
    exact Int.ceil_le.mpr (by simpa [Int.cast_add, Int.cast_one] using le_of_lt hsm_lt)
  have hgap_le :
      up - dn ≤ (beta : ℝ) ^ e := by
    have hceil_cast :
        (n : ℝ) ≤ ((FloatSpec.Core.Raux.Zfloor sm : Int) : ℝ) + 1 := by
      exact_mod_cast hceil_le_floor_add_one
    have hdiff_le :
        (n : ℝ) - ((FloatSpec.Core.Raux.Zfloor sm : Int) : ℝ) ≤ 1 := by
      linarith
    have hmul := mul_le_mul_of_nonneg_right hdiff_le (le_of_lt hpow_pos)
    calc
      up - dn =
          ((n : ℝ) - ((FloatSpec.Core.Raux.Zfloor sm : Int) : ℝ)) *
            (beta : ℝ) ^ e := by
              rw [hup_eval, hdn_eval]
              ring
      _ ≤ 1 * (beta : ℝ) ^ e := hmul
      _ = (beta : ℝ) ^ e := by ring
  have hdist_lt : |sm - (n : ℝ)| < (1 / 2 : ℝ) := by
    have hup_minus_x_lt : up - x < (up - dn) / 2 := by
      linarith [hmid_round]
    have hup_minus_x_scaled :
        up - x = ((n : ℝ) - sm) * (beta : ℝ) ^ e := by
      rw [← hscaled, hup_eval]
      ring
    have hlt_scaled :
        ((n : ℝ) - sm) * (beta : ℝ) ^ e < (1 / 2) * (beta : ℝ) ^ e := by
      nlinarith [hpow_pos, hgap_le, hup_minus_x_lt, hup_minus_x_scaled]
    have hlt : (n : ℝ) - sm < (1 / 2 : ℝ) := by
      nlinarith [hpow_pos, hlt_scaled]
    have hdist : |(n : ℝ) - sm| < (1 / 2 : ℝ) := by
      simpa [abs_of_nonneg hnonneg] using hlt
    simpa [abs_sub_comm] using hdist
  have hZ :
      FloatSpec.Core.Generic_fmt.Znearest choice sm = n := by
    have h := FloatSpec.Core.Generic_fmt.Znearest_imp choice sm n hdist_lt
    simpa [Std.Do.wp,
      Std.Do.PostCond.noThrow, Id.run, pure] using h
  calc
    FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest choice) x
        = ((FloatSpec.Core.Generic_fmt.Znearest choice sm : Int) : ℝ) *
            (beta : ℝ) ^ e := by
              simp [FloatSpec.Core.Generic_fmt.roundR, sm, hsm, e, he]
    _ = (n : ℝ) * (beta : ℝ) ^ e := by rw [hZ]
    _ = up := hup_eval.symm
    _ = u := hup_eq

/-- Positive-input core of Coq's `round_odd_pt`.

    The non-exact floor branch uses `cexp_DN` to make the floor-rounded
    canonical float explicit. The ceil branch uses the Flocq `Exists_NE`
    parity theorem to transfer the even floor mantissa to an odd UP witness. -/
private theorem round_odd_pt_pos
  (x : ℝ)
  (hNE : FloatSpec.Core.RoundNE.Exists_NE beta fexp)
  (hβ : 1 < beta)
  (hxpos : 0 < x) :
  Rnd_odd_pt (beta := beta) (fexp := fexp) x
    (FloatSpec.Calc.Round.round beta fexp oddMode x) := by
  classical
  haveI : FloatSpec.Core.RoundNE.Exists_NE beta fexp := hNE
  set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x with hsm
  set e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x with he
  set mf : Int := FloatSpec.Core.Raux.Zfloor sm with hmf
  set r : ℝ := FloatSpec.Calc.Round.round beta fexp oddMode x with hr
  have hr_eval :
      r = ((Zodd sm : Int) : ℝ) * (beta : ℝ) ^ e := by
    simp [r, hr, FloatSpec.Calc.Round.round, oddMode,
      FloatSpec.Core.Generic_fmt.roundR, sm, hsm, e, he]
  have hscaled : sm * (beta : ℝ) ^ e = x := by
    have htrip := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
      (beta := beta) (fexp := fexp) (x := x)
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, sm, hsm, e, he]
      using htrip hβ
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hpow_e_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbposR e
  have hsm_pos : 0 < sm := by
    have hpow_neg_pos : 0 < (beta : ℝ) ^ (-(e)) := zpow_pos hbposR _
    have hsm_def : sm = x * (beta : ℝ) ^ (-(e)) := by
      simp [sm, hsm, e, he, FloatSpec.Core.Generic_fmt.scaled_mantissa]
    rw [hsm_def]
    exact mul_pos hxpos hpow_neg_pos
  have hfmt_r : generic_format beta fexp r := by
    simpa [r, hr, FloatSpec.Calc.Round.round, oddMode] using
      FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := beta) (fexp := fexp) (rnd := Zodd) (x := x) hβ
  refine ⟨hfmt_r, ?_⟩
  by_cases hrx : r = x
  · exact Or.inl hrx
  right
  have hxNF : ¬ generic_format beta fexp x := by
    intro hxF
    have hfix := FloatSpec.Core.Generic_fmt.roundR_generic
      (beta := beta) (fexp := fexp) (rnd := Zodd) (x := x) hβ hxF
    exact hrx (by simpa [r, hr, FloatSpec.Calc.Round.round, oddMode] using hfix)
  have hsm_nonint : ¬ sm = ((FloatSpec.Core.Raux.Zfloor sm : Int) : ℝ) := by
    intro hsm_int
    have hzodd : Zodd sm = FloatSpec.Core.Raux.Zfloor sm :=
      Zodd_of_int_floor sm hsm_int
    apply hrx
    calc
      r = ((Zodd sm : Int) : ℝ) * (beta : ℝ) ^ e := hr_eval
      _ = ((FloatSpec.Core.Raux.Zfloor sm : Int) : ℝ) * (beta : ℝ) ^ e := by rw [hzodd]
      _ = sm * (beta : ℝ) ^ e := by
        exact congrArg (fun t : ℝ => t * (beta : ℝ) ^ e) hsm_int.symm
      _ = x := hscaled
  have hmf_nonneg : (0 : Int) ≤ mf := by
    rw [hmf]
    exact Int.floor_nonneg.mpr (le_of_lt hsm_pos)
  let rd : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp
    (fun y => FloatSpec.Core.Raux.Zfloor y) x
  let ru : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp
    (fun y => FloatSpec.Core.Raux.Zceil y) x
  have hrd_eval : rd = ((mf : Int) : ℝ) * (beta : ℝ) ^ e := by
    simp [rd, FloatSpec.Core.Generic_fmt.roundR, sm, hsm, e, he, mf, hmf]
  have hceil_eval :
      ru = ((FloatSpec.Core.Raux.Zceil sm : Int) : ℝ) * (beta : ℝ) ^ e := by
    simp [ru, FloatSpec.Core.Generic_fmt.roundR, sm, hsm, e, he]
  have hDN : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x rd := by
    simpa [rd] using roundR_floor_DN_pt_local (beta := beta) (fexp := fexp) x hβ
  have hUP : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x ru := by
    simpa [ru] using roundR_ceil_UP_pt_local (beta := beta) (fexp := fexp) x hβ
  have hpar_prop : FloatSpec.Core.RoundNE.DN_UP_parity_payload beta fexp := by
    have htrip := FloatSpec.Core.RoundNE.DN_UP_parity_generic_payload
      (beta := beta) (fexp := fexp)
    simpa [FloatSpec.Core.RoundNE.DN_UP_parity_generic_check, pure,
      decide_eq_true_iff] using (htrip hβ)
  rcases hpar_prop x rd ru hxNF hDN hUP with
    ⟨gd, gu, Hgd, Hgu, Cgd, Cgu, Hpar⟩
  have floor_canonical_parity :
      gd.Fnum % 2 = mf % 2 := by
    by_cases hmf0 : mf = 0
    · let gz : FloatSpec.Core.Defs.FlocqFloat beta :=
        FloatSpec.Core.Defs.FlocqFloat.mk 0 (fexp (FloatSpec.Core.Raux.mag beta 0))
      have Cgz : FloatSpec.Core.Generic_fmt.canonical beta fexp gz := by
        simpa [gz] using FloatSpec.Core.Generic_fmt.canonical_0 (beta := beta) (fexp := fexp)
      have hrd0 : rd = 0 := by
        simp [hrd_eval, hmf0]
      have hgd_eq : gd = gz := by
        apply FloatSpec.Core.Generic_fmt.canonical_unique
          (beta := beta) (hbeta := hβ) (fexp := fexp)
        · exact Cgd
        · exact Cgz
        · rw [← Hgd, hrd0]
          simp [gz, FloatSpec.Core.Defs.F2R]
      simp [hgd_eq, gz, hmf0]
    · have hmf_pos : 0 < mf := lt_of_le_of_ne hmf_nonneg (Ne.symm hmf0)
      have hrd_pos : 0 < rd := by
        have hmf_posR : 0 < ((mf : Int) : ℝ) := by exact_mod_cast hmf_pos
        simpa [hrd_eval] using mul_pos hmf_posR hpow_e_pos
      let gf : FloatSpec.Core.Defs.FlocqFloat beta :=
        FloatSpec.Core.Defs.FlocqFloat.mk mf e
      have hgf_val : FloatSpec.Core.Defs.F2R gf = rd := by
        simpa [gf, FloatSpec.Core.Defs.F2R, hrd_eval]
      have hcexp_rd :
          FloatSpec.Core.Generic_fmt.cexp beta fexp rd = e := by
        have htrip := FloatSpec.Core.Generic_fmt.cexp_DN
          (beta := beta) (fexp := fexp) (x := x)
        have himp :
            0 < FloatSpec.Core.Generic_fmt.roundR beta fexp
                FloatSpec.Core.Generic_fmt.rnd_floor x →
              FloatSpec.Core.Generic_fmt.cexp beta fexp
                  (FloatSpec.Core.Generic_fmt.roundR beta fexp
                    FloatSpec.Core.Generic_fmt.rnd_floor x) =
                FloatSpec.Core.Generic_fmt.cexp beta fexp x := by
          simpa [FloatSpec.Core.Generic_fmt.round_to_generic] using htrip
        have hrd_floor :
            rd = FloatSpec.Core.Generic_fmt.roundR beta fexp
                FloatSpec.Core.Generic_fmt.rnd_floor x := by
          rfl
        simpa [rd, FloatSpec.Core.Generic_fmt.rnd_floor, e, he] using
          himp (by simpa [hrd_floor] using hrd_pos)
      have Cgf : FloatSpec.Core.Generic_fmt.canonical beta fexp gf := by
        unfold FloatSpec.Core.Generic_fmt.canonical
        calc
          e = FloatSpec.Core.Generic_fmt.cexp beta fexp rd := hcexp_rd.symm
          _ = FloatSpec.Core.Generic_fmt.cexp beta fexp (F2R gf) := by
            exact congrArg (FloatSpec.Core.Generic_fmt.cexp beta fexp) hgf_val.symm
      have hgd_eq : gd = gf := by
        apply FloatSpec.Core.Generic_fmt.canonical_unique
          (beta := beta) (hbeta := hβ) (fexp := fexp)
        · exact Cgd
        · exact Cgf
        · rw [← Hgd, ← hgf_val]
      simp [hgd_eq, gf]
  by_cases hmf_even : mf % 2 = 0
  · have hzodd_ceil : Zodd sm = FloatSpec.Core.Raux.Zceil sm := by
      exact Zodd_of_floor_even sm (by simpa [mf, hmf] using hsm_nonint)
        (by simpa [mf, hmf] using hmf_even)
    have hr_ru : r = ru := by
      calc
        r = ((Zodd sm : Int) : ℝ) * (beta : ℝ) ^ e := hr_eval
        _ = ((FloatSpec.Core.Raux.Zceil sm : Int) : ℝ) * (beta : ℝ) ^ e := by rw [hzodd_ceil]
        _ = ru := hceil_eval.symm
    have hgu_odd : gu.Fnum % 2 ≠ 0 := by
      intro hgu_even
      have hgd_even : gd.Fnum % 2 = 0 := by
        simpa [floor_canonical_parity] using hmf_even
      exact Hpar (by rw [hgd_even, hgu_even])
    refine ⟨Or.inr (by simpa [hr_ru] using hUP), ?_⟩
    exact ⟨gu, by rw [hr_ru, Hgu], Cgu, hgu_odd⟩
  · have hzodd_floor : Zodd sm = FloatSpec.Core.Raux.Zfloor sm := by
      exact Zodd_of_floor_odd sm (by simpa [mf, hmf] using hsm_nonint)
        (by simpa [mf, hmf] using hmf_even)
    have hr_rd : r = rd := by
      calc
        r = ((Zodd sm : Int) : ℝ) * (beta : ℝ) ^ e := hr_eval
        _ = ((FloatSpec.Core.Raux.Zfloor sm : Int) : ℝ) * (beta : ℝ) ^ e := by rw [hzodd_floor]
        _ = rd := by simpa [hrd_eval, mf, hmf]
    have hgd_odd : gd.Fnum % 2 ≠ 0 := by
      intro hgd_even
      exact hmf_even (by simpa [floor_canonical_parity] using hgd_even)
    refine ⟨Or.inl (by simpa [hr_rd] using hDN), ?_⟩
    exact ⟨gd, by rw [hr_rd, Hgd], Cgd, hgd_odd⟩

/-- Coq: `round_odd_pt`.

    The Coq theorem is stated under `Exists_NE`; the Lean statement keeps that
    hypothesis explicit. -/
theorem round_odd_pt
  (x : ℝ)
  (hNE : FloatSpec.Core.RoundNE.Exists_NE beta fexp)
  (hβ : 1 < beta) :
  Rnd_odd_pt (beta := beta) (fexp := fexp) x
    (FloatSpec.Calc.Round.round beta fexp oddMode x) := by
  classical
  by_cases hxpos : 0 < x
  · exact round_odd_pt_pos (beta := beta) (fexp := fexp) x hNE hβ hxpos
  have hxle : x ≤ 0 := le_of_not_gt hxpos
  rcases lt_or_eq_of_le hxle with hxneg | hxzero
  · have hpos := round_odd_pt_pos (beta := beta) (fexp := fexp) (-x) hNE hβ
      (by simpa using neg_pos.mpr hxneg)
    have hopp := round_odd_opp (beta := beta) (fexp := fexp) (x := x) hβ
    exact Rnd_odd_pt_opp_inv (beta := beta) (fexp := fexp) x
      (FloatSpec.Calc.Round.round beta fexp oddMode x) (by
        simpa [hopp] using hpos)
  · subst hxzero
    have hround0 :
        FloatSpec.Calc.Round.round beta fexp oddMode 0 = 0 := by
      simp [FloatSpec.Calc.Round.round, oddMode, FloatSpec.Core.Generic_fmt.roundR,
      FloatSpec.Core.Generic_fmt.scaled_mantissa, Zodd, FloatSpec.Core.Raux.Zfloor]
    refine ⟨by
      simpa [hround0] using
        FloatSpec.Core.Generic_fmt.generic_format_0_run (beta := beta) (fexp := fexp), ?_⟩
    exact Or.inl hround0

/-- Coq: `Rnd_odd_pt_monotone`.

    Monotonicity of the round-to-odd predicate follows from uniqueness of
    round-to-odd witnesses and monotonicity of the concrete odd rounding
    function. -/
theorem Rnd_odd_pt_monotone
  (hNE : FloatSpec.Core.RoundNE.Exists_NE beta fexp)
  (hβ : 1 < beta) :
  FloatSpec.Core.Defs.round_pred_monotone
    (Rnd_odd_pt (beta := beta) (fexp := fexp)) := by
  intro x y f g hf hg hxy
  let rx := FloatSpec.Calc.Round.round beta fexp oddMode x
  let ry := FloatSpec.Calc.Round.round beta fexp oddMode y
  have hfx : f = rx := by
    exact Rnd_odd_pt_unique (beta := beta) (fexp := fexp) x f rx hNE hβ hf
      (by simpa [rx] using round_odd_pt (beta := beta) (fexp := fexp) x hNE hβ)
  have hgy : g = ry := by
    exact Rnd_odd_pt_unique (beta := beta) (fexp := fexp) y g ry hNE hβ hg
      (by simpa [ry] using round_odd_pt (beta := beta) (fexp := fexp) y hNE hβ)
  have hround_le : rx ≤ ry := by
    have h := FloatSpec.Core.Generic_fmt.roundR_le
      (beta := beta) (fexp := fexp) (rnd := Zodd) (x := x) (y := y) hβ hxy
    simpa [rx, ry, FloatSpec.Calc.Round.round, oddMode] using h
  simpa [hfx, hgy] using hround_le

/-- Coq: `d_eq`
    Equality between the DN-witness value and rounding with `Zfloor`.
    Mirrors: `F2R d = round beta fexp Zfloor x`.

    We state it over Core’s `roundR` with the concrete rounding function `Zfloor`.
-/
lemma d_eq_from_full_section_payload (x : ℝ)
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

lemma d_eq (x : ℝ) (d : FloatSpec.Core.Defs.FlocqFloat beta)
    (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (hβ : 1 < beta) :
    F2R d = FloatSpec.Core.Generic_fmt.roundR beta fexp
      FloatSpec.Core.Raux.Zfloor x := by
  exact Rnd_DN_pt_unique_pure (generic_format beta fexp) x (F2R d)
    (FloatSpec.Core.Generic_fmt.roundR beta fexp
      FloatSpec.Core.Raux.Zfloor x)
    Hd (roundR_floor_DN_pt_local (beta := beta) (fexp := fexp) x hβ)

/-- Coq: `u_eq`
    Equality between the UP-witness value and rounding with `Zceil`.

    Mirrors: `F2R u = round beta fexp Zceil x`. We use the Core `roundR`
    helper with the integer rounding function `Zceil` (as `Int` via `.run`). -/
lemma u_eq_from_full_section_payload (x : ℝ)
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

lemma u_eq (x : ℝ) (u : FloatSpec.Core.Defs.FlocqFloat beta)
    (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
    (hβ : 1 < beta) :
    F2R u = FloatSpec.Core.Generic_fmt.roundR beta fexp
      FloatSpec.Core.Raux.Zceil x := by
  exact FloatSpec.Core.Round_pred.Rnd_UP_pt_unique_pure
    (generic_format beta fexp) x (F2R u)
    (FloatSpec.Core.Generic_fmt.roundR beta fexp
      FloatSpec.Core.Raux.Zceil x)
    Hu (roundR_ceil_UP_pt_local (beta := beta) (fexp := fexp) x hβ)

/-- Coq: `d_ge_0`
    From the DN-witness hypothesis, the down-rounded value `F2R d` is
    nonnegative when `0 < x`. -/
lemma d_ge_0_from_full_section_payload (x : ℝ)
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

lemma d_ge_0 (x : ℝ) (d : FloatSpec.Core.Defs.FlocqFloat beta)
    (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (xPos : 0 < x) : 0 ≤ F2R d := by
  have hzero_fmt : generic_format beta fexp 0 :=
    FloatSpec.Core.Generic_fmt.generic_format_0_run
      (beta := beta) (fexp := fexp)
  exact Hd.2.2 0 hzero_fmt (le_of_lt xPos)

/-- Coq: `mag_d`.
    A positive DN witness has the same magnitude as the rounded input. -/
lemma mag_d_from_full_section_payload (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) (hβ : 1 < beta)
  (hd_pos : 0 < F2R d) :
  FloatSpec.Core.Raux.mag beta (F2R d) = FloatSpec.Core.Raux.mag beta x := by
  have hdn := d_eq (beta := beta) (fexp := fexp) x d Hd hβ
  have hdn_floor :
      F2R d =
        FloatSpec.Core.Generic_fmt.roundR beta fexp
          FloatSpec.Core.Generic_fmt.rnd_floor x := by
    simpa [FloatSpec.Core.Generic_fmt.rnd_floor] using hdn
  have hpos_round :
      0 < FloatSpec.Core.Generic_fmt.roundR beta fexp
          FloatSpec.Core.Generic_fmt.rnd_floor x := by
    rw [← hdn_floor]
    exact hd_pos
  have hmag := FloatSpec.Core.Generic_fmt.mag_DN
    (beta := beta) (fexp := fexp) (x := x)
    (by simpa [FloatSpec.Core.Generic_fmt.round_to_generic] using hpos_round)
  calc
    FloatSpec.Core.Raux.mag beta (F2R d) =
        FloatSpec.Core.Raux.mag beta
          (FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_floor x) :=
      congrArg (FloatSpec.Core.Raux.mag beta) hdn_floor
    _ = FloatSpec.Core.Raux.mag beta
          (FloatSpec.Core.Generic_fmt.round_to_generic beta fexp
            FloatSpec.Core.Generic_fmt.rnd_floor x) := by
      rw [FloatSpec.Core.Generic_fmt.round_to_generic_int_eq_roundR]
    _ = FloatSpec.Core.Raux.mag beta x := hmag

lemma mag_d (x : ℝ) (d : FloatSpec.Core.Defs.FlocqFloat beta)
    (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (hβ : 1 < beta) (hd_pos : 0 < F2R d) :
    FloatSpec.Core.Raux.mag beta (F2R d) =
      FloatSpec.Core.Raux.mag beta x := by
  have hdn := d_eq (beta := beta) (fexp := fexp) x d Hd hβ
  have hdn_floor :
      F2R d = FloatSpec.Core.Generic_fmt.roundR beta fexp
        FloatSpec.Core.Generic_fmt.rnd_floor x := by
    simpa [FloatSpec.Core.Generic_fmt.rnd_floor] using hdn
  have hpos_round :
      0 < FloatSpec.Core.Generic_fmt.roundR beta fexp
        FloatSpec.Core.Generic_fmt.rnd_floor x := by
    rw [← hdn_floor]
    exact hd_pos
  have hmag := FloatSpec.Core.Generic_fmt.mag_DN
    (beta := beta) (fexp := fexp) (x := x)
    (by simpa [FloatSpec.Core.Generic_fmt.round_to_generic] using hpos_round)
  rw [hdn_floor]
  simpa [FloatSpec.Core.Generic_fmt.round_to_generic] using hmag

/-- Coq: `Fexp_d`.
    A positive canonical DN witness has exponent `fexp (mag beta x)`. -/
lemma Fexp_d_from_full_section_payload (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) (hβ : 1 < beta)
  (hd_pos : 0 < F2R d) :
  d.Fexp = fexp (FloatSpec.Core.Raux.mag beta x) := by
  have hmag := mag_d (beta := beta) (fexp := fexp) x d Hd hβ hd_pos
  unfold FloatSpec.Core.Generic_fmt.canonical at Cd
  calc
    d.Fexp = fexp (FloatSpec.Core.Raux.mag beta (F2R d)) := Cd
    _ = fexp (FloatSpec.Core.Raux.mag beta x) := by rw [hmag]

lemma Fexp_d (x : ℝ) (d : FloatSpec.Core.Defs.FlocqFloat beta)
    (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
    (hβ : 1 < beta) (hd_pos : 0 < F2R d) :
    d.Fexp = fexp (FloatSpec.Core.Raux.mag beta x) := by
  have hmag := mag_d (beta := beta) (fexp := fexp) x d Hd hβ hd_pos
  calc
    d.Fexp = fexp (FloatSpec.Core.Raux.mag beta (F2R d)) := Cd
    _ = fexp (FloatSpec.Core.Raux.mag beta x) := by rw [hmag]

/-- Coq: `format_bpow_x`.
    If the DN witness is positive, the power at `mag beta x` is in the
    generic format. -/
lemma format_bpow_x_from_full_section_payload (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) (hβ : 1 < beta)
  (hd_pos : 0 < F2R d) :
  generic_format beta fexp ((beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x)) := by
  have hmag := mag_d (beta := beta) (fexp := fexp) x d Hd hβ hd_pos
  have hfmt_d : generic_format beta fexp (F2R d) :=
    FloatSpec.Core.Generic_fmt.generic_format_canonical
      (beta := beta) (fexp := fexp) (f := d) Cd
  have hmg := (FloatSpec.Core.Generic_fmt.mag_generic_gt
    (beta := beta) (fexp := fexp) (x := F2R d)) ⟨hβ, ne_of_gt hd_pos, hfmt_d⟩
  have hcexp_le :
      FloatSpec.Core.Generic_fmt.cexp beta fexp (F2R d) ≤
        FloatSpec.Core.Raux.mag beta (F2R d) := by
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using (le_of_lt hmg)
  have hfe_le_d :
      fexp (FloatSpec.Core.Raux.mag beta (F2R d)) ≤
        FloatSpec.Core.Raux.mag beta (F2R d) := by
    simpa [FloatSpec.Core.Generic_fmt.cexp] using hcexp_le
  have hfe_le :
      fexp (FloatSpec.Core.Raux.mag beta x) ≤
        FloatSpec.Core.Raux.mag beta x := by
    rw [hmag] at hfe_le_d
    exact hfe_le_d
  have hpow := (FloatSpec.Core.Generic_fmt.generic_format_bpow'
    (beta := beta) (fexp := fexp) (e := FloatSpec.Core.Raux.mag beta x))
      ⟨hβ, hfe_le⟩
  simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using hpow

lemma format_bpow_x (x : ℝ) (d : FloatSpec.Core.Defs.FlocqFloat beta)
    (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
    (hβ : 1 < beta) (hd_pos : 0 < F2R d) :
    generic_format beta fexp
      ((beta : ℝ) ^ FloatSpec.Core.Raux.mag beta x) := by
  have hmag := mag_d (beta := beta) (fexp := fexp) x d Hd hβ hd_pos
  have hfmt_d : generic_format beta fexp (F2R d) :=
    FloatSpec.Core.Generic_fmt.generic_format_canonical
      (beta := beta) (fexp := fexp) (f := d) Cd
  have hmg := (FloatSpec.Core.Generic_fmt.mag_generic_gt
    (beta := beta) (fexp := fexp) (x := F2R d))
      ⟨hβ, ne_of_gt hd_pos, hfmt_d⟩
  have hfe_le_d :
      fexp (FloatSpec.Core.Raux.mag beta (F2R d)) ≤
        FloatSpec.Core.Raux.mag beta (F2R d) := by
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Generic_fmt.cexp] using (le_of_lt hmg)
  have hfe_le : fexp (FloatSpec.Core.Raux.mag beta x) ≤
      FloatSpec.Core.Raux.mag beta x := by
    rw [hmag] at hfe_le_d
    exact hfe_le_d
  have hpow := FloatSpec.Core.Generic_fmt.generic_format_bpow'
    (beta := beta) (fexp := fexp) (e := FloatSpec.Core.Raux.mag beta x)
      ⟨hβ, hfe_le⟩
  simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using hpow

/-- Coq: `format_bpow_d`.
    If the DN witness is positive, the power at `mag beta (F2R d)` is in the
    generic format. -/
lemma format_bpow_d_from_full_section_payload (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) (hβ : 1 < beta)
  (hd_pos : 0 < F2R d) :
  generic_format beta fexp ((beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta (F2R d))) := by
  have hfmt_d : generic_format beta fexp (F2R d) :=
    FloatSpec.Core.Generic_fmt.generic_format_canonical
      (beta := beta) (fexp := fexp) (f := d) Cd
  have hmg := (FloatSpec.Core.Generic_fmt.mag_generic_gt
    (beta := beta) (fexp := fexp) (x := F2R d)) ⟨hβ, ne_of_gt hd_pos, hfmt_d⟩
  have hcexp_le :
      FloatSpec.Core.Generic_fmt.cexp beta fexp (F2R d) ≤
        FloatSpec.Core.Raux.mag beta (F2R d) := by
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using (le_of_lt hmg)
  have hfe_le :
      fexp (FloatSpec.Core.Raux.mag beta (F2R d)) ≤
        FloatSpec.Core.Raux.mag beta (F2R d) := by
    simpa [FloatSpec.Core.Generic_fmt.cexp] using hcexp_le
  have hpow := (FloatSpec.Core.Generic_fmt.generic_format_bpow'
    (beta := beta) (fexp := fexp) (e := FloatSpec.Core.Raux.mag beta (F2R d)))
      ⟨hβ, hfe_le⟩
  simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using hpow

lemma format_bpow_d (d : FloatSpec.Core.Defs.FlocqFloat beta)
    (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
    (hβ : 1 < beta) (hd_pos : 0 < F2R d) :
    generic_format beta fexp
      ((beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (F2R d)) := by
  have hfmt_d : generic_format beta fexp (F2R d) :=
    FloatSpec.Core.Generic_fmt.generic_format_canonical
      (beta := beta) (fexp := fexp) (f := d) Cd
  have hmg := (FloatSpec.Core.Generic_fmt.mag_generic_gt
    (beta := beta) (fexp := fexp) (x := F2R d))
      ⟨hβ, ne_of_gt hd_pos, hfmt_d⟩
  have hfe_le : fexp (FloatSpec.Core.Raux.mag beta (F2R d)) ≤
      FloatSpec.Core.Raux.mag beta (F2R d) := by
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Generic_fmt.cexp] using (le_of_lt hmg)
  have hpow := FloatSpec.Core.Generic_fmt.generic_format_bpow'
    (beta := beta) (fexp := fexp)
    (e := FloatSpec.Core.Raux.mag beta (F2R d)) ⟨hβ, hfe_le⟩
  simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using hpow

/-- Midpoint between the DN/UP witnesses used in Coq's section `Fcore_rnd_odd`.
    We keep it as a plain real number constructed from `d` and `u`. -/
noncomputable def m (d u : FloatSpec.Core.Defs.FlocqFloat beta) : ℝ :=
  (F2R d + F2R u) / 2

/-- Coq: `d_le_m`. The down-rounded value is below the midpoint `m`. -/
lemma d_le_m_from_full_section_payload (x : ℝ)
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

lemma d_le_m (x : ℝ) (d u : FloatSpec.Core.Defs.FlocqFloat beta)
    (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u)) :
    F2R d ≤ m (beta := beta) d u := by
  have hdu : F2R d ≤ F2R u := le_trans Hd.2.1 Hu.2.1
  unfold m
  linarith

/-- Coq: `m_le_u`. The midpoint `m` is below the up-rounded value. -/
lemma m_le_u_from_full_section_payload (x : ℝ)
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

lemma m_le_u (x : ℝ) (d u : FloatSpec.Core.Defs.FlocqFloat beta)
    (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u)) :
    m (beta := beta) d u ≤ F2R u := by
  have hdu : F2R d ≤ F2R u := le_trans Hd.2.1 Hu.2.1
  unfold m
  linarith

/-- Coq: `mag_m`.
    If the DN witness is positive, the midpoint has the same magnitude as the
    DN witness. -/
lemma mag_m (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (hβ : 1 < beta)
  (hd_pos : 0 < F2R d) :
  FloatSpec.Core.Raux.mag beta (m (beta := beta) d u) =
    FloatSpec.Core.Raux.mag beta (F2R d) := by
  let md := FloatSpec.Core.Raux.mag beta (F2R d)
  have hmd_lower : (beta : ℝ) ^ (md - 1) ≤ F2R d := by
    have htrip := FloatSpec.Core.Raux.mag_lower_bound
      (beta := beta) (x := F2R d) hβ (ne_of_gt hd_pos)
    have h : (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta (F2R d) - 1) ≤
        abs (F2R d) := by
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure,
        FloatSpec.Core.Raux.abs_val] using htrip True.intro
    rw [abs_of_pos hd_pos] at h
    simpa [md] using h
  have hmd_upper : F2R d < (beta : ℝ) ^ md := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := F2R d) hβ (ne_of_gt hd_pos)
    have h : abs (F2R d) < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta (F2R d)) := by
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure,
        FloatSpec.Core.Raux.abs_val] using htrip True.intro
    rw [abs_of_pos hd_pos] at h
    simpa [md] using h
  have hdm : F2R d ≤ m (beta := beta) d u :=
    d_le_m (beta := beta) (fexp := fexp) x d u Hd Hu
  have hmu : m (beta := beta) d u ≤ F2R u :=
    m_le_u (beta := beta) (fexp := fexp) x d u Hd Hu
  have hfmt_bpow_d :
      generic_format beta fexp ((beta : ℝ) ^ md) := by
    simpa [md] using
      format_bpow_d (beta := beta) (fexp := fexp) d Cd hβ hd_pos
  have hx_le_bpow : x ≤ (beta : ℝ) ^ md := by
    by_contra hx_not
    have hbpow_lt_x : (beta : ℝ) ^ md < x := lt_of_not_ge hx_not
    have hround_ge :=
      FloatSpec.Core.Generic_fmt.roundR_ge_generic
        (beta := beta) (fexp := fexp)
        (rnd := FloatSpec.Core.Generic_fmt.rnd_floor)
        ((beta : ℝ) ^ md) x hβ hfmt_bpow_d (le_of_lt hbpow_lt_x)
    have hdn_floor :
        F2R d =
          FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_floor x := by
      have hdn := d_eq (beta := beta) (fexp := fexp) x d Hd hβ
      simpa [FloatSpec.Core.Generic_fmt.rnd_floor] using hdn
    have hbpow_le_d : (beta : ℝ) ^ md ≤ F2R d := by
      rw [← hdn_floor] at hround_ge
      exact hround_ge
    exact (not_le_of_gt hmd_upper) hbpow_le_d
  have hu_le_bpow : F2R u ≤ (beta : ℝ) ^ md := by
    have hround_le :=
      FloatSpec.Core.Generic_fmt.roundR_le_generic
        (beta := beta) (fexp := fexp)
        (rnd := FloatSpec.Core.Generic_fmt.rnd_ceil)
        x ((beta : ℝ) ^ md) hβ hfmt_bpow_d hx_le_bpow
    have hu_ceil :
        F2R u =
          FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_ceil x := by
      have hu_eq := u_eq (beta := beta) (fexp := fexp) x u Hu hβ
      simpa [FloatSpec.Core.Generic_fmt.rnd_ceil] using hu_eq
    rw [← hu_ceil] at hround_le
    exact hround_le
  have hm_pos : 0 < m (beta := beta) d u := lt_of_lt_of_le hd_pos hdm
  have hm_lower : (beta : ℝ) ^ (md - 1) ≤ m (beta := beta) d u :=
    le_trans hmd_lower hdm
  have hm_upper : m (beta := beta) d u < (beta : ℝ) ^ md :=
    by
      unfold m
      linarith
  have huniq := FloatSpec.Core.Raux.mag_unique_pos
    (beta := beta) (x := m (beta := beta) d u) (e := md)
    hβ ⟨hm_lower, hm_upper⟩
  simpa [md] using huniq

lemma mag_m_from_full_section_payload (x : ℝ)
    (d u : FloatSpec.Core.Defs.FlocqFloat beta)
    (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
    (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
    (_Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
    (_xPos : 0 < x) (hβ : 1 < beta) (hd_pos : 0 < F2R d) :
    FloatSpec.Core.Raux.mag beta (m (beta := beta) d u) =
      FloatSpec.Core.Raux.mag beta (F2R d) :=
  mag_m (beta := beta) (fexp := fexp) x d u Hd Cd Hu hβ hd_pos

/-- Coq: `u'_eq`.
    In the positive-DN branch, the UP value has a float representative using
    the DN exponent. -/
lemma u'_eq (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (hβ : 1 < beta)
  (hd_pos : 0 < F2R d) :
  ∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
    F2R f = F2R u ∧ f.Fexp = d.Fexp := by
  let f : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk
      (FloatSpec.Core.Generic_fmt.rnd_ceil
        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x))
      d.Fexp
  refine ⟨f, ?_, rfl⟩
  have hu_ceil := u_eq (beta := beta) (fexp := fexp) x u Hu hβ
  have hd_exp := Fexp_d (beta := beta) (fexp := fexp) x d Hd Cd hβ hd_pos
  have hcexp : FloatSpec.Core.Generic_fmt.cexp beta fexp x = d.Fexp := by
    simpa [FloatSpec.Core.Generic_fmt.cexp] using hd_exp.symm
  calc
    F2R f
        = ((FloatSpec.Core.Generic_fmt.rnd_ceil
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x) : Int) : ℝ)
            * (beta : ℝ) ^ d.Fexp := by
            rfl
    _ = FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_ceil x := by
            simp [FloatSpec.Core.Generic_fmt.roundR,
              FloatSpec.Core.Generic_fmt.scaled_mantissa, hcexp]
    _ = F2R u := by
            simpa [FloatSpec.Core.Generic_fmt.rnd_ceil] using hu_ceil.symm

lemma u'_eq_from_full_section_payload (x : ℝ)
    (d u : FloatSpec.Core.Defs.FlocqFloat beta)
    (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
    (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
    (_Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
    (_xPos : 0 < x) (hβ : 1 < beta) (hd_pos : 0 < F2R d) :
    ∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
      F2R f = F2R u ∧ f.Fexp = d.Fexp :=
  u'_eq (beta := beta) (fexp := fexp) x d u Hd Cd Hu hβ hd_pos

/-- Coq: `m_eq`.
    In the positive-DN branch, the midpoint is representable one exponent below
    `fexp (mag beta x)`. -/
lemma m_eq (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (hβ : 1 < beta)
  (Ebeta : ∃ b : Int, beta = 2 * b)
  (hd_pos : 0 < F2R d) :
  ∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
    F2R f = m (beta := beta) d u ∧
      f.Fexp = fexp (FloatSpec.Core.Raux.mag beta x) - 1 := by
  classical
  rcases Ebeta with ⟨b, hb⟩
  rcases u'_eq (beta := beta) (fexp := fexp) x d u Hd Cd Hu hβ hd_pos with
    ⟨u', hu'_val, hu'_exp⟩
  let f : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk (b * (d.Fnum + u'.Fnum)) (d.Fexp - 1)
  have hd_exp := Fexp_d (beta := beta) (fexp := fexp) x d Hd Cd hβ hd_pos
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposℝ : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbneℝ : (beta : ℝ) ≠ 0 := ne_of_gt hbposℝ
  have hpow_split :
      (beta : ℝ) ^ d.Fexp = (beta : ℝ) ^ (d.Fexp - 1) * (beta : ℝ) := by
    have h := zpow_add₀ hbneℝ (d.Fexp - 1) (1 : Int)
    simpa [sub_add_cancel, zpow_one] using h
  have hb_real : (beta : ℝ) = 2 * (b : ℝ) := by
    exact_mod_cast hb
  have hb_half : (b : ℝ) = (beta : ℝ) / 2 := by
    nlinarith
  have hu'_val_exp : F2R u' = (u'.Fnum : ℝ) * (beta : ℝ) ^ d.Fexp := by
    rw [show d.Fexp = u'.Fexp from hu'_exp.symm]
    rfl
  refine ⟨f, ?_, ?_⟩
  · calc
      F2R f
          = ((b * (d.Fnum + u'.Fnum) : Int) : ℝ) *
              (beta : ℝ) ^ (d.Fexp - 1) := by
                rfl
      _ = ((b : ℝ) * ((d.Fnum : ℝ) + (u'.Fnum : ℝ))) *
              (beta : ℝ) ^ (d.Fexp - 1) := by
                simp [Int.cast_mul, Int.cast_add]
      _ = (((d.Fnum : ℝ) + (u'.Fnum : ℝ)) *
              (((beta : ℝ) ^ (d.Fexp - 1) * (beta : ℝ)) / 2)) := by
                rw [hb_half]
                ring
      _ = (((d.Fnum : ℝ) + (u'.Fnum : ℝ)) *
              ((beta : ℝ) ^ d.Fexp / 2)) := by
                rw [hpow_split]
      _ = (((d.Fnum : ℝ) * (beta : ℝ) ^ d.Fexp +
              (u'.Fnum : ℝ) * (beta : ℝ) ^ d.Fexp) / 2) := by
                ring
      _ = (F2R d + F2R u') / 2 := by
                rw [hu'_val_exp]
                rfl
      _ = (F2R d + F2R u) / 2 := by
                rw [hu'_val]
      _ = m (beta := beta) d u := by
                rfl
  · simp [f, hd_exp]

lemma m_eq_from_full_section_payload (x : ℝ)
    (d u : FloatSpec.Core.Defs.FlocqFloat beta)
    (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
    (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
    (_Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
    (_xPos : 0 < x) (hβ : 1 < beta)
    (Ebeta : ∃ b : Int, beta = 2 * b) (hd_pos : 0 < F2R d) :
    ∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
      F2R f = m (beta := beta) d u ∧
        f.Fexp = fexp (FloatSpec.Core.Raux.mag beta x) - 1 :=
  m_eq (beta := beta) (fexp := fexp) x d u Hd Cd Hu hβ Ebeta hd_pos

/-- Coq: `m_eq_0`.
    In the zero-DN branch, the midpoint is representable one exponent below
    the UP witness's canonical exponent. -/
lemma m_eq_0 (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (hβ : 1 < beta)
  (Ebeta : ∃ b : Int, beta = 2 * b)
  (hd_zero : 0 = F2R d) :
  ∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
    F2R f = m (beta := beta) d u ∧
      f.Fexp = fexp (FloatSpec.Core.Raux.mag beta (F2R u)) - 1 := by
  classical
  rcases Ebeta with ⟨b, hb⟩
  let f : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk (b * u.Fnum) (u.Fexp - 1)
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposℝ : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbneℝ : (beta : ℝ) ≠ 0 := ne_of_gt hbposℝ
  have hpow_split :
      (beta : ℝ) ^ u.Fexp = (beta : ℝ) ^ (u.Fexp - 1) * (beta : ℝ) := by
    have h := zpow_add₀ hbneℝ (u.Fexp - 1) (1 : Int)
    simpa [sub_add_cancel, zpow_one] using h
  have hb_real : (beta : ℝ) = 2 * (b : ℝ) := by
    exact_mod_cast hb
  have hb_half : (b : ℝ) = (beta : ℝ) / 2 := by
    nlinarith
  have hd_zero' : F2R d = 0 := hd_zero.symm
  refine ⟨f, ?_, ?_⟩
  · calc
      F2R f
          = ((b * u.Fnum : Int) : ℝ) *
              (beta : ℝ) ^ (u.Fexp - 1) := by
                rfl
      _ = ((b : ℝ) * (u.Fnum : ℝ)) *
              (beta : ℝ) ^ (u.Fexp - 1) := by
                simp [Int.cast_mul]
      _ = (u.Fnum : ℝ) *
              (((beta : ℝ) ^ (u.Fexp - 1) * (beta : ℝ)) / 2) := by
                rw [hb_half]
                ring
      _ = ((u.Fnum : ℝ) * (beta : ℝ) ^ u.Fexp) / 2 := by
                rw [hpow_split]
                ring
      _ = F2R u / 2 := by
                rfl
      _ = (F2R d + F2R u) / 2 := by
                rw [hd_zero']
                ring
      _ = m (beta := beta) d u := by
                rfl
  · simp [f]
    exact Cu

lemma m_eq_0_from_full_section_payload (x : ℝ)
    (d u : FloatSpec.Core.Defs.FlocqFloat beta)
    (_Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (_Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
    (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
    (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
    (_xPos : 0 < x) (hβ : 1 < beta)
    (Ebeta : ∃ b : Int, beta = 2 * b) (hd_zero : 0 = F2R d) :
    ∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
      F2R f = m (beta := beta) d u ∧
        f.Fexp = fexp (FloatSpec.Core.Raux.mag beta (F2R u)) - 1 :=
  m_eq_0 (beta := beta) (fexp := fexp) x d u Hu Cu hβ Ebeta hd_zero

/-- Coq: `fexp_m_eq_0`.
    In the zero-DN branch, the UP power sits in the small exponent plateau used
    by the midpoint witness. -/
lemma fexp_m_eq_0 (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (xPos : 0 < x) (hβ : 1 < beta)
  (hNE : FloatSpec.Core.RoundNE.Exists_NE beta fexp)
  (Ebeta : ∃ b : Int, beta = 2 * b)
  (hd_zero : 0 = F2R d) :
  fexp (FloatSpec.Core.Raux.mag beta (F2R u) - 1) <
    fexp (FloatSpec.Core.Raux.mag beta (F2R u)) + 1 := by
  classical
  haveI : FloatSpec.Core.RoundNE.Exists_NE beta fexp := hNE
  let e := FloatSpec.Core.Raux.mag beta x
  have hx_ne : x ≠ 0 := ne_of_gt xPos
  have hmag_bounds :
      (beta : ℝ) ^ (e - 1) ≤ x ∧ x < (beta : ℝ) ^ e := by
    have hlow := FloatSpec.Core.Raux.mag_lower_bound
      (beta := beta) (x := x) hβ hx_ne
    have hhigh := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := x) hβ hx_ne
    constructor
    · have h : (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 1) ≤ abs x := by
        simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure,
          FloatSpec.Core.Raux.abs_val] using hlow True.intro
      simpa [e, abs_of_pos xPos] using h
    · have h : abs x < (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta x := by
        simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure,
          FloatSpec.Core.Raux.abs_val] using hhigh True.intro
      simpa [e, abs_of_pos xPos] using h
  have hdn_floor :
      F2R d =
        FloatSpec.Core.Generic_fmt.roundR beta fexp
          FloatSpec.Core.Generic_fmt.rnd_floor x := by
    have hdn := d_eq (beta := beta) (fexp := fexp) x d Hd hβ
    simpa [FloatSpec.Core.Generic_fmt.rnd_floor] using hdn
  have hfloor_zero :
      FloatSpec.Core.Generic_fmt.roundR beta fexp
        FloatSpec.Core.Generic_fmt.rnd_floor x = 0 := by
    rw [← hdn_floor]
    exact hd_zero.symm
  have hsmall : e ≤ fexp e := by
    by_contra hnot
    have hlarge : fexp e < e := lt_of_not_ge hnot
    have hfe_le : fexp e ≤ e - 1 := Int.le_sub_one_iff.mpr hlarge
    have hfmt_bpow :
        generic_format beta fexp ((beta : ℝ) ^ (e - 1)) := by
      have hfe_le' : fexp (e - 1 + 1) ≤ e - 1 := by
        simpa [sub_add_cancel] using hfe_le
      have htrip := FloatSpec.Core.Generic_fmt.generic_format_bpow
        (beta := beta) (fexp := fexp) (e := e - 1)
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure]
        using htrip ⟨hβ, hfe_le'⟩
    have hle_round :
        (beta : ℝ) ^ (e - 1) ≤
          FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_floor x :=
      FloatSpec.Core.Generic_fmt.roundR_ge_generic
        (beta := beta) (fexp := fexp)
        (rnd := FloatSpec.Core.Generic_fmt.rnd_floor)
        ((beta : ℝ) ^ (e - 1)) x hβ hfmt_bpow hmag_bounds.1
    have hle0 : (beta : ℝ) ^ (e - 1) ≤ 0 := by
      rw [hfloor_zero] at hle_round
      exact hle_round
    have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposℝ : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    exact (not_le_of_gt (zpow_pos hbposℝ (e - 1))) hle0
  have hup_ceil :
      F2R u =
        FloatSpec.Core.Generic_fmt.roundR beta fexp
          FloatSpec.Core.Generic_fmt.rnd_ceil x := by
    have hu := u_eq (beta := beta) (fexp := fexp) x u Hu hβ
    simpa [FloatSpec.Core.Generic_fmt.rnd_ceil] using hu
  have hup_small_tg :
      FloatSpec.Core.Generic_fmt.round_to_generic beta fexp
        FloatSpec.Core.Generic_fmt.rnd_ceil x = (beta : ℝ) ^ (fexp e) := by
    have htrip := FloatSpec.Core.Generic_fmt.round_UP_small_pos
      (beta := beta) (fexp := fexp) (x := x) (ex := e)
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure]
      using htrip ⟨hβ, hsmall, hmag_bounds⟩
  have hup_pow :
      F2R u = (beta : ℝ) ^ (fexp e) := by
    calc
      F2R u =
          FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_ceil x := hup_ceil
      _ = FloatSpec.Core.Generic_fmt.round_to_generic beta fexp
            FloatSpec.Core.Generic_fmt.rnd_ceil x := by
              exact (FloatSpec.Core.Generic_fmt.round_to_generic_int_eq_roundR
                (beta := beta) (fexp := fexp)
                (rnd := FloatSpec.Core.Generic_fmt.rnd_ceil) (x := x)).symm
      _ = (beta : ℝ) ^ (fexp e) := hup_small_tg
  have hmag_u :
      FloatSpec.Core.Raux.mag beta (F2R u) = fexp e + 1 := by
    rw [hup_pow]
    have htrip := FloatSpec.Core.Raux.mag_bpow (beta := beta) (e := fexp e) hβ
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hself : fexp (fexp e) = fexp e := by
    have hpair := FloatSpec.Core.Generic_fmt.Valid_exp.valid_exp
      (fexp := fexp) e
    exact (hpair.right hsmall).right (fexp e) le_rfl
  have hnext : fexp (fexp e + 1) = fexp e := by
    rcases FloatSpec.Core.RoundNE.Exists_NE.exists_ne (beta := beta) (fexp := fexp) with hodd | heven
    · rcases Ebeta with ⟨b, hb⟩
      have hmod : beta % 2 = 0 := by
        rw [hb]
        exact Int.mul_emod_right 2 b
      exact False.elim (hodd hmod)
    · exact (heven e).right hsmall
  rw [hmag_u]
  have : fexp (fexp e) < fexp (fexp e + 1) + 1 := by
    rw [hself, hnext]
    omega
  simpa [sub_eq_add_neg, add_assoc] using this

lemma fexp_m_eq_0_from_full_section_payload (x : ℝ)
    (d u : FloatSpec.Core.Defs.FlocqFloat beta)
    (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (_Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
    (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
    (_Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
    (xPos : 0 < x) (hβ : 1 < beta)
    (hNE : FloatSpec.Core.RoundNE.Exists_NE beta fexp)
    (Ebeta : ∃ b : Int, beta = 2 * b) (hd_zero : 0 = F2R d) :
    fexp (FloatSpec.Core.Raux.mag beta (F2R u) - 1) <
      fexp (FloatSpec.Core.Raux.mag beta (F2R u)) + 1 :=
  fexp_m_eq_0 (beta := beta) (fexp := fexp) x d u Hd Hu xPos hβ
    hNE Ebeta hd_zero

/-- Coq: `mag_m_0`.
    In the zero-DN branch, the midpoint is one binade below the UP witness. -/
lemma mag_m_0 (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (xPos : 0 < x) (hβ : 1 < beta)
  (hd_zero : 0 = F2R d) :
  FloatSpec.Core.Raux.mag beta (m (beta := beta) d u) =
    FloatSpec.Core.Raux.mag beta (F2R u) - 1 := by
  classical
  let e := FloatSpec.Core.Raux.mag beta x
  have hx_ne : x ≠ 0 := ne_of_gt xPos
  have hmag_bounds :
      (beta : ℝ) ^ (e - 1) ≤ x ∧ x < (beta : ℝ) ^ e := by
    have hlow := FloatSpec.Core.Raux.mag_lower_bound
      (beta := beta) (x := x) hβ hx_ne
    have hhigh := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := x) hβ hx_ne
    constructor
    · have h : (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 1) ≤ abs x := by
        simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure,
          FloatSpec.Core.Raux.abs_val] using hlow True.intro
      simpa [e, abs_of_pos xPos] using h
    · have h : abs x < (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta x := by
        simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure,
          FloatSpec.Core.Raux.abs_val] using hhigh True.intro
      simpa [e, abs_of_pos xPos] using h
  have hdn_floor :
      F2R d =
        FloatSpec.Core.Generic_fmt.roundR beta fexp
          FloatSpec.Core.Generic_fmt.rnd_floor x := by
    have hdn := d_eq (beta := beta) (fexp := fexp) x d Hd hβ
    simpa [FloatSpec.Core.Generic_fmt.rnd_floor] using hdn
  have hfloor_zero :
      FloatSpec.Core.Generic_fmt.roundR beta fexp
        FloatSpec.Core.Generic_fmt.rnd_floor x = 0 := by
    rw [← hdn_floor]
    exact hd_zero.symm
  have hsmall : e ≤ fexp e := by
    apply FloatSpec.Core.Generic_fmt.exp_small_round_0_pos
      (beta := beta) (fexp := fexp)
      (rnd := FloatSpec.Core.Generic_fmt.rnd_floor) hmag_bounds
    simpa [FloatSpec.Core.Generic_fmt.round_to_generic_int_eq_roundR]
      using hfloor_zero
  have hup_ceil :
      F2R u =
        FloatSpec.Core.Generic_fmt.roundR beta fexp
          FloatSpec.Core.Generic_fmt.rnd_ceil x := by
    have hu := u_eq (beta := beta) (fexp := fexp) x u Hu hβ
    simpa [FloatSpec.Core.Generic_fmt.rnd_ceil] using hu
  have hup_small_tg :
      FloatSpec.Core.Generic_fmt.round_to_generic beta fexp
        FloatSpec.Core.Generic_fmt.rnd_ceil x = (beta : ℝ) ^ (fexp e) := by
    have htrip := FloatSpec.Core.Generic_fmt.round_UP_small_pos
      (beta := beta) (fexp := fexp) (x := x) (ex := e)
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure]
      using htrip ⟨hβ, hsmall, hmag_bounds⟩
  have hup_pow :
      F2R u = (beta : ℝ) ^ (fexp e) := by
    calc
      F2R u =
          FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_ceil x := hup_ceil
      _ = FloatSpec.Core.Generic_fmt.round_to_generic beta fexp
            FloatSpec.Core.Generic_fmt.rnd_ceil x := by
              exact (FloatSpec.Core.Generic_fmt.round_to_generic_int_eq_roundR
                (beta := beta) (fexp := fexp)
                (rnd := FloatSpec.Core.Generic_fmt.rnd_ceil) (x := x)).symm
      _ = (beta : ℝ) ^ (fexp e) := hup_small_tg
  have hmag_u :
      FloatSpec.Core.Raux.mag beta (F2R u) = fexp e + 1 := by
    rw [hup_pow]
    have htrip := FloatSpec.Core.Raux.mag_bpow (beta := beta) (e := fexp e) hβ
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip True.intro
  let em := fexp e
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposℝ : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbneℝ : (beta : ℝ) ≠ 0 := ne_of_gt hbposℝ
  have hbeta_ge_two : (2 : ℝ) ≤ (beta : ℝ) := by
    exact_mod_cast (Int.add_one_le_iff.mpr hβ : (2 : Int) ≤ beta)
  have hpow_split :
      (beta : ℝ) ^ em = (beta : ℝ) ^ (em - 1) * (beta : ℝ) := by
    have h := zpow_add₀ hbneℝ (em - 1) (1 : Int)
    simpa [em, sub_add_cancel, zpow_one] using h
  have hm_eq_half : m (beta := beta) d u = (beta : ℝ) ^ em / 2 := by
    unfold m
    rw [hd_zero.symm, hup_pow]
    ring
  have hm_pos : 0 < m (beta := beta) d u := by
    rw [hm_eq_half]
    positivity
  have hm_lower : (beta : ℝ) ^ (em - 1) ≤ m (beta := beta) d u := by
    have hpow_pos : 0 < (beta : ℝ) ^ (em - 1) := zpow_pos hbposℝ _
    rw [hm_eq_half]
    have hmul_le :
        (beta : ℝ) ^ (em - 1) * 2 ≤
          (beta : ℝ) ^ (em - 1) * (beta : ℝ) :=
      mul_le_mul_of_nonneg_left hbeta_ge_two (le_of_lt hpow_pos)
    have hle : (beta : ℝ) ^ (em - 1) ≤
        ((beta : ℝ) ^ (em - 1) * (beta : ℝ)) / 2 := by
      nlinarith
    simpa [← hpow_split] using hle
  have hm_upper : m (beta := beta) d u < (beta : ℝ) ^ em := by
    rw [hm_eq_half]
    have hpow_pos : 0 < (beta : ℝ) ^ em := zpow_pos hbposℝ _
    nlinarith
  have huniq := FloatSpec.Core.Raux.mag_unique_pos
    (beta := beta) (x := m (beta := beta) d u) (e := em)
    hβ ⟨hm_lower, hm_upper⟩
  have hmag_m : FloatSpec.Core.Raux.mag beta (m (beta := beta) d u) = em := by
    simpa [em] using huniq
  rw [hmag_m, hmag_u]
  omega

lemma mag_m_0_from_full_section_payload (x : ℝ)
    (d u : FloatSpec.Core.Defs.FlocqFloat beta)
    (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (_Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
    (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
    (_Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
    (xPos : 0 < x) (hβ : 1 < beta)
    (_hNE : FloatSpec.Core.RoundNE.Exists_NE beta fexp)
    (_Ebeta : ∃ b : Int, beta = 2 * b) (hd_zero : 0 = F2R d) :
    FloatSpec.Core.Raux.mag beta (m (beta := beta) d u) =
      FloatSpec.Core.Raux.mag beta (F2R u) - 1 :=
  mag_m_0 (beta := beta) (fexp := fexp) x d u Hd Hu xPos hβ hd_zero

/-- Coq: `Fm`.
    The midpoint belongs to the auxiliary generic format. -/
lemma Fm (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) (hβ : 1 < beta)
  (hNE : FloatSpec.Core.RoundNE.Exists_NE beta fexp)
  (Ebeta : ∃ b : Int, beta = 2 * b)
  (hrel : ∀ e, fexpe e ≤ fexp e - 2) :
  generic_format beta fexpe (m (beta := beta) d u) := by
  classical
  have hd_nonneg := d_ge_0 (beta := beta) (fexp := fexp) x d Hd xPos
  by_cases hd_pos : 0 < F2R d
  · rcases m_eq (beta := beta) (fexp := fexp) x d u Hd Cd Hu hβ Ebeta hd_pos with
      ⟨g, hg_val, hg_exp⟩
    have hfmt := FloatSpec.Core.Generic_fmt.generic_format_F2R'
      (beta := beta) (fexp := fexpe) (x := m (beta := beta) d u) (f := g)
    have hbound :
        m (beta := beta) d u ≠ 0 →
          FloatSpec.Core.Generic_fmt.cexp beta fexpe (m (beta := beta) d u) ≤ g.Fexp := by
      intro _hm_ne
      have hmag := mag_m (beta := beta) (fexp := fexp) x d u Hd Cd Hu hβ hd_pos
      have hmagd := mag_d (beta := beta) (fexp := fexp) x d Hd hβ hd_pos
      have hrel_d := hrel (FloatSpec.Core.Raux.mag beta (F2R d))
      have hrel_x :
          fexpe (FloatSpec.Core.Raux.mag beta x) ≤
            fexp (FloatSpec.Core.Raux.mag beta x) - 2 := by
        rw [hmagd] at hrel_d
        exact hrel_d
      unfold FloatSpec.Core.Generic_fmt.cexp
      rw [hmag, hmagd, hg_exp]
      change fexpe (FloatSpec.Core.Raux.mag beta x) ≤
        fexp (FloatSpec.Core.Raux.mag beta x) - 1
      omega
    have hrun : generic_format beta fexpe (m (beta := beta) d u) := by
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure]
        using hfmt ⟨hβ, hg_val, hbound⟩
    exact hrun
  · have hd_eq : F2R d = 0 := le_antisymm (le_of_not_gt hd_pos) hd_nonneg
    have hd_zero : 0 = F2R d := hd_eq.symm
    rcases m_eq_0 (beta := beta) (fexp := fexp) x d u Hu Cu hβ Ebeta hd_zero with
      ⟨g, hg_val, hg_exp⟩
    have hfmt := FloatSpec.Core.Generic_fmt.generic_format_F2R'
      (beta := beta) (fexp := fexpe) (x := m (beta := beta) d u) (f := g)
    have hbound :
        m (beta := beta) d u ≠ 0 →
          FloatSpec.Core.Generic_fmt.cexp beta fexpe (m (beta := beta) d u) ≤ g.Fexp := by
      intro _hm_ne
      have hmag0 := mag_m_0 (beta := beta) (fexp := fexp)
        x d u Hd Hu xPos hβ hd_zero
      have hfexp0 := fexp_m_eq_0 (beta := beta) (fexp := fexp)
        x d u Hd Hu xPos hβ hNE Ebeta hd_zero
      have hrel_m := hrel (FloatSpec.Core.Raux.mag beta (F2R u) - 1)
      have hfexp0_le :
          fexp (FloatSpec.Core.Raux.mag beta (F2R u) - 1) ≤
            fexp (FloatSpec.Core.Raux.mag beta (F2R u)) := by
        omega
      unfold FloatSpec.Core.Generic_fmt.cexp
      rw [hmag0, hg_exp]
      change fexpe (FloatSpec.Core.Raux.mag beta (F2R u) - 1) ≤
        fexp (FloatSpec.Core.Raux.mag beta (F2R u)) - 1
      omega
    have hrun : generic_format beta fexpe (m (beta := beta) d u) := by
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure]
        using hfmt ⟨hβ, hg_val, hbound⟩
    exact hrun

/-- Coq: `Zm`.
    The midpoint has an even canonical representative in the auxiliary format. -/
lemma Zm (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) (hβ : 1 < beta)
  (hNE : FloatSpec.Core.RoundNE.Exists_NE beta fexp)
  (Ebeta : ∃ b : Int, beta = 2 * b)
  (hrel : ∀ e, fexpe e ≤ fexp e - 2) :
  ∃ g : FloatSpec.Core.Defs.FlocqFloat beta,
    F2R g = m (beta := beta) d u ∧
      FloatSpec.Core.Generic_fmt.canonical beta fexpe g ∧ g.Fnum % 2 = 0 := by
  classical
  have hd_nonneg := d_ge_0 (beta := beta) (fexp := fexp) x d Hd xPos
  by_cases hd_pos : 0 < F2R d
  · rcases m_eq (beta := beta) (fexp := fexp) x d u Hd Cd Hu hβ Ebeta hd_pos with
      ⟨g, hg_val, hg_exp⟩
    apply exists_even_fexp_lt (beta := beta) Ebeta hβ fexpe (m (beta := beta) d u)
    refine ⟨g, hg_val, ?_⟩
    have hmag := mag_m (beta := beta) (fexp := fexp) x d u Hd Cd Hu hβ hd_pos
    have hmagd := mag_d (beta := beta) (fexp := fexp) x d Hd hβ hd_pos
    have hrel_d := hrel (FloatSpec.Core.Raux.mag beta (F2R d))
    have hrel_x :
        fexpe (FloatSpec.Core.Raux.mag beta x) ≤
          fexp (FloatSpec.Core.Raux.mag beta x) - 2 := by
      rw [hmagd] at hrel_d
      exact hrel_d
    rw [hmag, hmagd, hg_exp]
    change fexpe (FloatSpec.Core.Raux.mag beta x) <
      fexp (FloatSpec.Core.Raux.mag beta x) - 1
    omega
  · have hd_eq : F2R d = 0 := le_antisymm (le_of_not_gt hd_pos) hd_nonneg
    have hd_zero : 0 = F2R d := hd_eq.symm
    rcases m_eq_0 (beta := beta) (fexp := fexp) x d u Hu Cu hβ Ebeta hd_zero with
      ⟨g, hg_val, hg_exp⟩
    apply exists_even_fexp_lt (beta := beta) Ebeta hβ fexpe (m (beta := beta) d u)
    refine ⟨g, hg_val, ?_⟩
    have hmag0 := mag_m_0 (beta := beta) (fexp := fexp)
      x d u Hd Hu xPos hβ hd_zero
    have hfexp0 := fexp_m_eq_0 (beta := beta) (fexp := fexp)
      x d u Hd Hu xPos hβ hNE Ebeta hd_zero
    have hrel_m := hrel (FloatSpec.Core.Raux.mag beta (F2R u) - 1)
    have hfexp0_le :
        fexp (FloatSpec.Core.Raux.mag beta (F2R u) - 1) ≤
          fexp (FloatSpec.Core.Raux.mag beta (F2R u)) := by
      omega
    rw [hmag0, hg_exp]
    change fexpe (FloatSpec.Core.Raux.mag beta (F2R u) - 1) <
      fexp (FloatSpec.Core.Raux.mag beta (F2R u)) - 1
    omega

/-- Coq: `DN_odd_d_aux`.
    For any `z` between `F2R d` and `F2R u`, the DN rounding predicate
    selects `F2R d`. -/
lemma DN_odd_d_aux (x z : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Hz : F2R d ≤ z ∧ z < F2R u) :
  FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) z (F2R d) := by
  refine ⟨Hd.1, Hz.1, ?_⟩
  intro g hg hgz
  by_cases hxg : x ≤ g
  · have hug : F2R u ≤ g := Hu.2.2 g hg hxg
    linarith
  · have hgx : g ≤ x := le_of_lt (lt_of_not_ge hxg)
    exact Hd.2.2 g hg hgx

lemma DN_odd_d_aux_from_full_section_payload (x z : ℝ)
    (d u : FloatSpec.Core.Defs.FlocqFloat beta)
    (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (_Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
    (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
    (_Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
    (_xPos : 0 < x) (Hz : F2R d ≤ z ∧ z < F2R u) :
    FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) z (F2R d) :=
  DN_odd_d_aux (beta := beta) (fexp := fexp) x z d u Hd Hu Hz

/-- Coq: `UP_odd_d_aux`.
    For any `z` strictly between `F2R d` and `F2R u` (up to `≤` on the right),
    the UP rounding predicate selects `F2R u`. -/
lemma UP_odd_d_aux (x z : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Hz : F2R d < z ∧ z ≤ F2R u) :
  FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) z (F2R u) := by
  refine ⟨Hu.1, Hz.2, ?_⟩
  intro g hg hzg
  by_cases hgx : g ≤ x
  · have hgd : g ≤ F2R d := Hd.2.2 g hg hgx
    linarith
  · have hxg : x ≤ g := le_of_lt (lt_of_not_ge hgx)
    exact Hu.2.2 g hg hxg

lemma UP_odd_d_aux_from_full_section_payload (x z : ℝ)
    (d u : FloatSpec.Core.Defs.FlocqFloat beta)
    (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (_Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
    (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
    (_Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
    (_xPos : 0 < x) (Hz : F2R d < z ∧ z ≤ F2R u) :
    FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) z (F2R u) :=
  UP_odd_d_aux (beta := beta) (fexp := fexp) x z d u Hd Hu Hz

/-- Coq: `round_N_odd_pos`.
    Positive core of round-to-nearest after round-to-odd double rounding. -/
theorem round_N_odd_pos (choice : Int → Bool) (x : ℝ)
  (d u : FloatSpec.Core.Defs.FlocqFloat beta)
  (Hd : FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) x (F2R d))
  (Cd : FloatSpec.Core.Generic_fmt.canonical beta fexp d)
  (Hu : FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) x (F2R u))
  (Cu : FloatSpec.Core.Generic_fmt.canonical beta fexp u)
  (xPos : 0 < x) (hβ : 1 < beta)
  (hNE : FloatSpec.Core.RoundNE.Exists_NE beta fexp)
  (hNEe : FloatSpec.Core.RoundNE.Exists_NE beta fexpe)
  (Ebeta : ∃ b : Int, beta = 2 * b)
  (hrel : ∀ e, fexpe e ≤ fexp e - 2) :
  FloatSpec.Core.Generic_fmt.roundR beta fexp
      (FloatSpec.Core.Generic_fmt.Znearest choice)
      (FloatSpec.Calc.Round.round beta fexpe oddMode x) =
    FloatSpec.Core.Generic_fmt.roundR beta fexp
      (FloatSpec.Core.Generic_fmt.Znearest choice) x := by
  classical
  haveI : FloatSpec.Core.RoundNE.Exists_NE beta fexp := hNE
  haveI : FloatSpec.Core.RoundNE.Exists_NE beta fexpe := hNEe
  let o : ℝ := FloatSpec.Calc.Round.round beta fexpe oddMode x
  by_cases hx_fmt : generic_format beta fexp x
  · have ho_eq_x : o = x := by
      have hx_fexpe : generic_format beta fexpe x :=
        generic_format_fexpe_fexp (beta := beta) (fexp := fexp)
          (fexpe := fexpe) hβ hrel x hx_fmt
      have hfix := FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexpe) (rnd := Zodd) (x := x) hβ hx_fexpe
      simpa [o, FloatSpec.Calc.Round.round, oddMode] using hfix
    simp [o, ho_eq_x]
  · have hd_fmt_fexpe : generic_format beta fexpe (F2R d) :=
      generic_format_fexpe_fexp (beta := beta) (fexp := fexp)
        (fexpe := fexpe) hβ hrel (F2R d) Hd.1
    have hu_fmt_fexpe : generic_format beta fexpe (F2R u) :=
      generic_format_fexpe_fexp (beta := beta) (fexp := fexp)
        (fexpe := fexpe) hβ hrel (F2R u) Hu.1
    have ho_ge_d : F2R d ≤ o := by
      simpa [o, FloatSpec.Calc.Round.round, oddMode] using
        FloatSpec.Core.Generic_fmt.roundR_ge_generic
          (beta := beta) (fexp := fexpe) (rnd := Zodd)
          (x := F2R d) (y := x) hβ hd_fmt_fexpe Hd.2.1
    have ho_le_u : o ≤ F2R u := by
      simpa [o, FloatSpec.Calc.Round.round, oddMode] using
        FloatSpec.Core.Generic_fmt.roundR_le_generic
          (beta := beta) (fexp := fexpe) (rnd := Zodd)
          (x := x) (y := F2R u) hβ hu_fmt_fexpe Hu.2.1
    have hodd_o : Rnd_odd_pt (beta := beta) (fexp := fexpe) x o := by
      simpa [o] using round_odd_pt (beta := beta) (fexp := fexpe) x hNEe hβ
    have ho_mid_false_of_x_ne
        (hx_ne_m : x ≠ m (beta := beta) d u)
        (ho_mid : o = m (beta := beta) d u) : False := by
      rcases hodd_o with ⟨_, hodd_cases⟩
      rcases hodd_cases with ho_eq_x | ⟨_, g, hg_val, hg_can, hg_odd⟩
      · exact hx_ne_m (ho_eq_x.symm.trans ho_mid)
      · rcases Zm (beta := beta) (fexp := fexp) (fexpe := fexpe) x d u
          Hd Cd Hu Cu xPos hβ hNE Ebeta hrel with
          ⟨g', hg'_val, hg'_can, hg'_even⟩
        have hg_eq : g = g' := by
          apply FloatSpec.Core.Generic_fmt.canonical_unique
            (beta := beta) (hbeta := hβ) (fexp := fexpe)
          · exact hg_can
          · exact hg'_can
          · calc
              F2R g = o := hg_val.symm
              _ = m (beta := beta) d u := ho_mid
              _ = F2R g' := hg'_val.symm
        exact hg_odd (by simpa [hg_eq] using hg'_even)
    rcases lt_or_eq_of_le ho_ge_d with hd_lt_o | ho_eq_d
    · rcases lt_or_eq_of_le ho_le_u with ho_lt_u | ho_eq_u
      · by_cases hxm : x ≤ m (beta := beta) d u
        · rcases lt_or_eq_of_le hxm with hx_lt_m | hx_eq_m
          · have ho_le_m : o ≤ m (beta := beta) d u := by
              have hfmt_m := Fm (beta := beta) (fexp := fexp) (fexpe := fexpe) x d u
                Hd Cd Hu Cu xPos hβ hNE Ebeta hrel
              simpa [o, FloatSpec.Calc.Round.round, oddMode] using
                FloatSpec.Core.Generic_fmt.roundR_le_generic
                  (beta := beta) (fexp := fexpe) (rnd := Zodd)
                  (x := x) (y := m (beta := beta) d u) hβ hfmt_m (le_of_lt hx_lt_m)
            have ho_lt_m : o < m (beta := beta) d u :=
              lt_of_le_of_ne ho_le_m
                (fun ho_mid => ho_mid_false_of_x_ne (ne_of_lt hx_lt_m) ho_mid)
            calc
              FloatSpec.Core.Generic_fmt.roundR beta fexp
                  (FloatSpec.Core.Generic_fmt.Znearest choice) o = F2R d := by
                exact roundR_nearest_eq_DN_of_lt_mid
                  (beta := beta) (fexp := fexp) choice o (F2R d) (F2R u)
                  (DN_odd_d_aux (beta := beta) (fexp := fexp) x o d u Hd Hu
                    ⟨le_of_lt hd_lt_o, ho_lt_u⟩)
                  (UP_odd_d_aux (beta := beta) (fexp := fexp) x o d u Hd Hu
                    ⟨hd_lt_o, le_of_lt ho_lt_u⟩)
                  hβ ho_lt_m
              _ = FloatSpec.Core.Generic_fmt.roundR beta fexp
                  (FloatSpec.Core.Generic_fmt.Znearest choice) x := by
                symm
                exact roundR_nearest_eq_DN_of_lt_mid
                  (beta := beta) (fexp := fexp) choice x (F2R d) (F2R u)
                  Hd Hu hβ hx_lt_m
          · have hfmt_m := Fm (beta := beta) (fexp := fexp) (fexpe := fexpe) x d u
              Hd Cd Hu Cu xPos hβ hNE Ebeta hrel
            have hx_fexpe : generic_format beta fexpe x := by
              simpa [hx_eq_m] using hfmt_m
            have hfix := FloatSpec.Core.Generic_fmt.roundR_generic
              (beta := beta) (fexp := fexpe) (rnd := Zodd) (x := x) hβ hx_fexpe
            have hround_eq_x :
                FloatSpec.Calc.Round.round beta fexpe oddMode x = x := by
              simpa [FloatSpec.Calc.Round.round, oddMode] using hfix
            simpa [hround_eq_x]
        · have hm_lt_x : m (beta := beta) d u < x := lt_of_not_ge hxm
          have hm_le_o : m (beta := beta) d u ≤ o := by
            have hfmt_m := Fm (beta := beta) (fexp := fexp) (fexpe := fexpe) x d u
              Hd Cd Hu Cu xPos hβ hNE Ebeta hrel
            simpa [o, FloatSpec.Calc.Round.round, oddMode] using
              FloatSpec.Core.Generic_fmt.roundR_ge_generic
                (beta := beta) (fexp := fexpe) (rnd := Zodd)
                (x := m (beta := beta) d u) (y := x) hβ hfmt_m (le_of_lt hm_lt_x)
          have hm_lt_o : m (beta := beta) d u < o :=
            lt_of_le_of_ne hm_le_o
              (fun hm_eq_o => ho_mid_false_of_x_ne (ne_of_gt hm_lt_x) hm_eq_o.symm)
          calc
            FloatSpec.Core.Generic_fmt.roundR beta fexp
                (FloatSpec.Core.Generic_fmt.Znearest choice) o = F2R u := by
              exact roundR_nearest_eq_UP_of_mid_lt
                (beta := beta) (fexp := fexp) choice o (F2R d) (F2R u)
                (DN_odd_d_aux (beta := beta) (fexp := fexp) x o d u Hd Hu
                  ⟨le_of_lt hd_lt_o, ho_lt_u⟩)
                (UP_odd_d_aux (beta := beta) (fexp := fexp) x o d u Hd Hu
                  ⟨hd_lt_o, le_of_lt ho_lt_u⟩)
                hβ hm_lt_o
            _ = FloatSpec.Core.Generic_fmt.roundR beta fexp
                (FloatSpec.Core.Generic_fmt.Znearest choice) x := by
              symm
              exact roundR_nearest_eq_UP_of_mid_lt
                (beta := beta) (fexp := fexp) choice x (F2R d) (F2R u)
                Hd Hu hβ hm_lt_x
      · have ho_fmt : generic_format beta fexp o := by
          simpa [ho_eq_u] using Hu.1
        have hfalse : False := by
          rcases hodd_o with ⟨_, hodd_cases⟩
          rcases hodd_cases with ho_eq_x | ⟨_, g, hg_val, hg_can, hg_odd⟩
          · exact hx_fmt (by simpa [ho_eq_x] using ho_fmt)
          · let g' : FloatSpec.Core.Defs.FlocqFloat beta :=
              FloatSpec.Core.Defs.FlocqFloat.mk
                (FloatSpec.Core.Raux.Ztrunc
                  (o * (beta : ℝ) ^
                    (-(FloatSpec.Core.Generic_fmt.cexp beta fexp o))))
                (FloatSpec.Core.Generic_fmt.cexp beta fexp o)
            have hg'_val : F2R g' = o := by
              simpa [g', FloatSpec.Core.Generic_fmt.generic_format,
                FloatSpec.Core.Generic_fmt.scaled_mantissa] using ho_fmt.symm
            have hg'_exp :
                fexpe (FloatSpec.Core.Raux.mag beta o) < g'.Fexp := by
              simp [g', FloatSpec.Core.Generic_fmt.cexp]
              have h := hrel (FloatSpec.Core.Raux.mag beta o)
              omega
            rcases exists_even_fexp_lt (beta := beta) Ebeta hβ fexpe o
              ⟨g', hg'_val, hg'_exp⟩ with
              ⟨g'', hg''_val, hg''_can, hg''_even⟩
            have hg_eq : g = g'' := by
              apply FloatSpec.Core.Generic_fmt.canonical_unique
                (beta := beta) (hbeta := hβ) (fexp := fexpe)
              · exact hg_can
              · exact hg''_can
              · calc
                  F2R g = o := hg_val.symm
                  _ = F2R g'' := hg''_val.symm
            exact hg_odd (by simpa [hg_eq] using hg''_even)
        exact False.elim hfalse
    · have ho_fmt : generic_format beta fexp o := by
        simpa [← ho_eq_d] using Hd.1
      have hfalse : False := by
        rcases hodd_o with ⟨_, hodd_cases⟩
        rcases hodd_cases with ho_eq_x | ⟨_, g, hg_val, hg_can, hg_odd⟩
        · exact hx_fmt (by simpa [ho_eq_x] using ho_fmt)
        · let g' : FloatSpec.Core.Defs.FlocqFloat beta :=
            FloatSpec.Core.Defs.FlocqFloat.mk
              (FloatSpec.Core.Raux.Ztrunc
                (o * (beta : ℝ) ^
                  (-(FloatSpec.Core.Generic_fmt.cexp beta fexp o))))
              (FloatSpec.Core.Generic_fmt.cexp beta fexp o)
          have hg'_val : F2R g' = o := by
            simpa [g', FloatSpec.Core.Generic_fmt.generic_format,
              FloatSpec.Core.Generic_fmt.scaled_mantissa] using ho_fmt.symm
          have hg'_exp :
              fexpe (FloatSpec.Core.Raux.mag beta o) < g'.Fexp := by
            simp [g', FloatSpec.Core.Generic_fmt.cexp]
            have h := hrel (FloatSpec.Core.Raux.mag beta o)
            omega
          rcases exists_even_fexp_lt (beta := beta) Ebeta hβ fexpe o
            ⟨g', hg'_val, hg'_exp⟩ with
            ⟨g'', hg''_val, hg''_can, hg''_even⟩
          have hg_eq : g = g'' := by
            apply FloatSpec.Core.Generic_fmt.canonical_unique
              (beta := beta) (hbeta := hβ) (fexp := fexpe)
            · exact hg_can
            · exact hg''_can
            · calc
                F2R g = o := hg_val.symm
                _ = F2R g'' := hg''_val.symm
          exact hg_odd (by simpa [hg_eq] using hg''_even)
      exact False.elim hfalse

/-- Coq: `round_N_odd`.
    Rounding a round-to-odd result to the coarser nearest format is the same as
    rounding the original value directly. -/
theorem round_N_odd (choice : Int → Bool) (x : ℝ)
  (hβ : 1 < beta)
  (hNE : FloatSpec.Core.RoundNE.Exists_NE beta fexp)
  (hNEe : FloatSpec.Core.RoundNE.Exists_NE beta fexpe)
  (Ebeta : ∃ b : Int, beta = 2 * b)
  (hrel : ∀ e, fexpe e ≤ fexp e - 2) :
  FloatSpec.Core.Generic_fmt.roundR beta fexp
      (FloatSpec.Core.Generic_fmt.Znearest choice)
      (FloatSpec.Calc.Round.round beta fexpe oddMode x) =
    FloatSpec.Core.Generic_fmt.roundR beta fexp
      (FloatSpec.Core.Generic_fmt.Znearest choice) x := by
  classical
  let cf : ℝ → FloatSpec.Core.Defs.FlocqFloat beta := fun y =>
    FloatSpec.Core.Defs.FlocqFloat.mk
      (FloatSpec.Core.Raux.Ztrunc
        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp y))
      (FloatSpec.Core.Generic_fmt.cexp beta fexp y)
  have cf_val : ∀ {y : ℝ}, generic_format beta fexp y → F2R (cf y) = y := by
    intro y hy
    simpa [cf, FloatSpec.Core.Generic_fmt.generic_format] using hy.symm
  have cf_can : ∀ {y : ℝ}, generic_format beta fexp y →
      FloatSpec.Core.Generic_fmt.canonical beta fexp (cf y) := by
    intro y hy
    simpa [FloatSpec.Core.Generic_fmt.canonical, cf,
      FloatSpec.Core.Generic_fmt.cexp] using
        congrArg (fun z : ℝ => fexp (FloatSpec.Core.Raux.mag beta z))
          (cf_val hy).symm
  have dn_data : ∀ y : ℝ,
      let dReal := Classical.choose (FloatSpec.Core.Generic_fmt.round_DN_exists
        (beta := beta) (fexp := fexp) (x := y) (hβ := hβ))
      FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) y (F2R (cf dReal)) ∧
        FloatSpec.Core.Generic_fmt.canonical beta fexp (cf dReal) := by
    intro y
    dsimp
    have hspec := Classical.choose_spec (FloatSpec.Core.Generic_fmt.round_DN_exists
      (beta := beta) (fexp := fexp) (x := y) (hβ := hβ))
    constructor
    · change FloatSpec.Core.Defs.Rnd_DN_pt (generic_format beta fexp) y
          (F2R (cf (Classical.choose
            (FloatSpec.Core.Generic_fmt.round_DN_exists
              (beta := beta) (fexp := fexp) (x := y) (hβ := hβ)))))
      rw [cf_val hspec.1]
      exact hspec.2
    · exact cf_can hspec.1
  have up_data : ∀ y : ℝ,
      let uReal := Classical.choose (FloatSpec.Core.Generic_fmt.round_UP_exists
        (beta := beta) (fexp := fexp) (x := y) (hβ := hβ))
      FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) y (F2R (cf uReal)) ∧
        FloatSpec.Core.Generic_fmt.canonical beta fexp (cf uReal) := by
    intro y
    dsimp
    have hspec := Classical.choose_spec (FloatSpec.Core.Generic_fmt.round_UP_exists
      (beta := beta) (fexp := fexp) (x := y) (hβ := hβ))
    constructor
    · change FloatSpec.Core.Defs.Rnd_UP_pt (generic_format beta fexp) y
          (F2R (cf (Classical.choose
            (FloatSpec.Core.Generic_fmt.round_UP_exists
              (beta := beta) (fexp := fexp) (x := y) (hβ := hβ)))))
      rw [cf_val hspec.1]
      exact hspec.2
    · exact cf_can hspec.1
  rcases lt_trichotomy x 0 with hxneg | hxzero | hxpos
  · set dn := Classical.choose (FloatSpec.Core.Generic_fmt.round_DN_exists
      (beta := beta) (fexp := fexp) (x := -x) (hβ := hβ)) with hdn
    set up := Classical.choose (FloatSpec.Core.Generic_fmt.round_UP_exists
      (beta := beta) (fexp := fexp) (x := -x) (hβ := hβ)) with hup
    have hd := (dn_data (-x))
    have hu := (up_data (-x))
    let choice' : Int → Bool := fun t => ! choice (-(t + 1))
    have hpos := round_N_odd_pos (beta := beta) (fexp := fexp) (fexpe := fexpe)
      choice' (-x)
      (cf dn) (cf up)
      (by simpa [hdn] using hd.1) (by simpa [hdn] using hd.2)
      (by simpa [hup] using hu.1) (by simpa [hup] using hu.2)
      (by simpa using neg_pos.mpr hxneg) hβ hNE hNEe Ebeta hrel
    have hodd_opp := round_odd_opp (beta := beta) (fexp := fexpe) (x := x) hβ
    have hnearest_opp_o :=
      FloatSpec.Core.Generic_fmt.round_N_opp
        (beta := beta) (fexp := fexp) (choice := choice)
        (x := -(FloatSpec.Calc.Round.round beta fexpe oddMode x))
    have hnearest_opp_x :=
      FloatSpec.Core.Generic_fmt.round_N_opp
        (beta := beta) (fexp := fexp) (choice := choice) (x := -x)
    calc
      FloatSpec.Core.Generic_fmt.roundR beta fexp
          (FloatSpec.Core.Generic_fmt.Znearest choice)
          (FloatSpec.Calc.Round.round beta fexpe oddMode x)
          =
        - FloatSpec.Core.Generic_fmt.roundR beta fexp
          (FloatSpec.Core.Generic_fmt.Znearest choice')
          (-(FloatSpec.Calc.Round.round beta fexpe oddMode x)) := by
            simpa [choice'] using hnearest_opp_o
      _ =
        - FloatSpec.Core.Generic_fmt.roundR beta fexp
          (FloatSpec.Core.Generic_fmt.Znearest choice')
          (FloatSpec.Calc.Round.round beta fexpe oddMode (-x)) := by
            rw [hodd_opp]
      _ =
        - FloatSpec.Core.Generic_fmt.roundR beta fexp
          (FloatSpec.Core.Generic_fmt.Znearest choice') (-x) := by
            rw [hpos]
      _ =
        FloatSpec.Core.Generic_fmt.roundR beta fexp
          (FloatSpec.Core.Generic_fmt.Znearest choice) x := by
            simpa [choice'] using hnearest_opp_x.symm
  · subst hxzero
    have hround0 :
        FloatSpec.Calc.Round.round beta fexpe oddMode 0 = 0 := by
      simp [FloatSpec.Calc.Round.round, oddMode, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, Zodd, FloatSpec.Core.Raux.Zfloor]
    simp [hround0]
  · set dn := Classical.choose (FloatSpec.Core.Generic_fmt.round_DN_exists
      (beta := beta) (fexp := fexp) (x := x) (hβ := hβ)) with hdn
    set up := Classical.choose (FloatSpec.Core.Generic_fmt.round_UP_exists
      (beta := beta) (fexp := fexp) (x := x) (hβ := hβ)) with hup
    have hd := (dn_data x)
    have hu := (up_data x)
    exact round_N_odd_pos (beta := beta) (fexp := fexp) (fexpe := fexpe)
      choice x
      (cf dn) (cf up)
      (by simpa [hdn] using hd.1) (by simpa [hdn] using hd.2)
      (by simpa [hup] using hu.1) (by simpa [hup] using hu.2)
      hxpos hβ hNE hNEe Ebeta hrel

private theorem abs_roundR_ge_generic_local
  (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd]
  (x y : ℝ) (hβ : 1 < beta)
  (hxF : generic_format beta fexp x)
  (hxle : x ≤ |y|) :
  x ≤ |FloatSpec.Core.Generic_fmt.roundR beta fexp rnd y| := by
  classical
  by_cases hy : 0 ≤ y
  · have hy_abs : |y| = y := abs_of_nonneg hy
    have hxle' : x ≤ y := by simpa [hy_abs] using hxle
    have hx_le_r : x ≤ FloatSpec.Core.Generic_fmt.roundR beta fexp rnd y :=
      FloatSpec.Core.Generic_fmt.roundR_ge_generic
        (beta := beta) (fexp := fexp) (rnd := rnd)
        (x := x) (y := y) hβ hxF hxle'
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

private theorem abs_roundR_le_generic_local
  (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd]
  (x y : ℝ) (hβ : 1 < beta)
  (hyF : generic_format beta fexp y)
  (hxy : |x| ≤ y) :
  |FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x| ≤ y := by
  classical
  have hbounds : -y ≤ x ∧ x ≤ y := abs_le.mp hxy
  have hnegF : generic_format beta fexp (-y) :=
    FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := fexp) y hyF
  have hlo : -y ≤ FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x :=
    FloatSpec.Core.Generic_fmt.roundR_ge_generic
      (beta := beta) (fexp := fexp) (rnd := rnd)
      (x := -y) (y := x) hβ hnegF hbounds.left
  have hhi : FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x ≤ y :=
    FloatSpec.Core.Generic_fmt.roundR_le_generic
      (beta := beta) (fexp := fexp) (rnd := rnd)
      (x := x) (y := y) hβ hyF hbounds.right
  exact abs_le.mpr ⟨hlo, hhi⟩

/-- Coq: `mag_round_odd`.

    For FLT round-to-odd, if `x` is above the underflow threshold, rounding
    preserves its magnitude. The `Exists_NE` hypothesis is explicit in Lean
    because the local port keeps nearest-even existence as a typeclass rather
    than deriving it globally for every FLT exponent. -/
theorem mag_round_odd_from_explicit_payload
  (emin prec : Int) [Prec_gt_0 prec]
  (hβ : 1 < beta)
  (Ebeta : ∃ b : Int, beta = 2 * b)
  (hNE : FloatSpec.Core.RoundNE.Exists_NE beta (FLT_exp emin prec))
  (x : ℝ)
  (hprec : 1 < prec)
  (hxmag : emin < FloatSpec.Core.Raux.mag beta x) :
  FloatSpec.Core.Raux.mag beta
      (FloatSpec.Calc.Round.round beta (FLT_exp emin prec) oddMode x) =
    FloatSpec.Core.Raux.mag beta x := by
  classical
  haveI : FloatSpec.Core.RoundNE.Exists_NE beta (FLT_exp emin prec) := hNE
  let e : Int := FloatSpec.Core.Raux.mag beta x
  let r : ℝ := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) oddMode x
  by_cases hx0 : x = 0
  · subst hx0
    have hround0 : r = 0 := by
      simp [r, FloatSpec.Calc.Round.round, oddMode, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, Zodd, FloatSpec.Core.Raux.Zfloor]
    simp [r, hround0]
  have hlow_x : (beta : ℝ) ^ (e - 1) ≤ |x| := by
    have htrip := FloatSpec.Core.Raux.mag_lower_bound
      (beta := beta) (x := x) hβ hx0
    have h : (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 1) ≤ |x| := by
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure,
        FloatSpec.Core.Raux.abs_val] using htrip True.intro
    simpa [e] using h
  have hupp_x : |x| < (beta : ℝ) ^ e := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := x) hβ hx0
    have h : |x| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) := by
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure,
        FloatSpec.Core.Raux.abs_val] using htrip True.intro
    simpa [e] using h
  have hfmt_lower :
      generic_format beta (FLT_exp emin prec) ((beta : ℝ) ^ (e - 1)) := by
    have htrip := FloatSpec.Core.FLT.generic_format_FLT_bpow
      (prec := prec) (emin := emin) (beta := beta) (e := e - 1)
    have hemin_le : emin ≤ e - 1 := by
      have : emin + 1 ≤ e := Int.add_one_le_iff.mpr (by simpa [e] using hxmag)
      omega
    simpa [FLT_exp] using htrip ⟨hβ, hemin_le⟩
  have hlow_r :
      (beta : ℝ) ^ (e - 1) ≤ |r| := by
    simpa [r, FloatSpec.Calc.Round.round, oddMode] using
      abs_roundR_ge_generic_local
        (beta := beta) (fexp := FLT_exp emin prec)
        (rnd := Zodd) (x := (beta : ℝ) ^ (e - 1)) (y := x)
        hβ hfmt_lower hlow_x
  have hfmt_upper :
      generic_format beta (FLT_exp emin prec) ((beta : ℝ) ^ e) := by
    have htrip := FloatSpec.Core.FLT.generic_format_FLT_bpow
      (prec := prec) (emin := emin) (beta := beta) (e := e)
    have hemin_le : emin ≤ e := le_of_lt (by simpa [e] using hxmag)
    simpa [FLT_exp] using htrip ⟨hβ, hemin_le⟩
  have hupper_r_le :
      |r| ≤ (beta : ℝ) ^ e := by
    simpa [r, FloatSpec.Calc.Round.round, oddMode] using
      abs_roundR_le_generic_local
        (beta := beta) (fexp := FLT_exp emin prec)
        (rnd := Zodd) (x := x) (y := (beta : ℝ) ^ e)
        hβ hfmt_upper (le_of_lt hupp_x)
  have hupper_r : |r| < (beta : ℝ) ^ e := by
    rcases lt_or_eq_of_le hupper_r_le with hlt | heq
    · exact hlt
    have hodd : Rnd_odd_pt (beta := beta) (fexp := FLT_exp emin prec) x r := by
      simpa [r] using
        round_odd_pt
          (beta := beta) (fexp := FLT_exp emin prec) x hNE hβ
    rcases hodd with ⟨_, hcases⟩
    rcases hcases with hr_eq_x | ⟨_, g, hg_val, hg_can, hg_odd⟩
    · have : ¬ ((beta : ℝ) ^ e ≤ |x|) := not_le_of_gt hupp_x
      exact False.elim (this (by simpa [r, hr_eq_x] using heq.symm.le))
    · let gg : FloatSpec.Core.Defs.FlocqFloat beta :=
        FloatSpec.Core.Defs.FlocqFloat.mk
          (beta ^ Int.toNat (e - FLT_exp emin prec (e + 1)))
          (FLT_exp emin prec (e + 1))
      have hdiff_nonneg : 0 ≤ e - FLT_exp emin prec (e + 1) := by
        have hp_ge_two : (2 : Int) ≤ prec := Int.add_one_le_iff.mpr hprec
        have hleft : e + 1 - prec ≤ e := by omega
        have hright : emin ≤ e := le_of_lt (by simpa [e] using hxmag)
        simpa [FLT_exp, FloatSpec.Core.FLT.FLT_exp] using
          (max_le_iff.mpr ⟨hleft, hright⟩)
      have hdiff_cast :
          (Int.toNat (e - FLT_exp emin prec (e + 1)) : Int) =
            e - FLT_exp emin prec (e + 1) := by
        simpa using Int.toNat_of_nonneg hdiff_nonneg
      have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
      have hbposℝ : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
      have hbneℝ : (beta : ℝ) ≠ 0 := ne_of_gt hbposℝ
      have hgg_val : F2R gg = (beta : ℝ) ^ e := by
        calc
          F2R gg
              = ((beta ^ Int.toNat (e - FLT_exp emin prec (e + 1)) : Int) : ℝ) *
                  (beta : ℝ) ^ (FLT_exp emin prec (e + 1)) := by
                    rfl
          _ = (beta : ℝ) ^ (Int.toNat (e - FLT_exp emin prec (e + 1))) *
                  (beta : ℝ) ^ (FLT_exp emin prec (e + 1)) := by
                    simp [Int.cast_pow]
          _ = (beta : ℝ) ^ ((Int.toNat (e - FLT_exp emin prec (e + 1)) : Int)) *
                  (beta : ℝ) ^ (FLT_exp emin prec (e + 1)) := by
                    rw [zpow_natCast]
          _ = (beta : ℝ) ^ (e - FLT_exp emin prec (e + 1)) *
                  (beta : ℝ) ^ (FLT_exp emin prec (e + 1)) := by
                    rw [hdiff_cast]
          _ = (beta : ℝ) ^ ((e - FLT_exp emin prec (e + 1)) +
                  FLT_exp emin prec (e + 1)) := by
                    rw [zpow_add₀ hbneℝ]
          _ = (beta : ℝ) ^ e := by ring_nf
      have hgg_can :
          FloatSpec.Core.Generic_fmt.canonical beta (FLT_exp emin prec) gg := by
        have hmag := FloatSpec.Core.Raux.mag_bpow beta e hβ
        have hmag_eq :
            FloatSpec.Core.Raux.mag beta ((beta : ℝ) ^ e) = e + 1 := by
          simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure]
            using hmag True.intro
        unfold FloatSpec.Core.Generic_fmt.canonical
        change gg.Fexp = FLT_exp emin prec (FloatSpec.Core.Raux.mag beta (F2R gg))
        rw [hgg_val, hmag_eq]
      have habs_val :
          F2R
            (FloatSpec.Core.Defs.FlocqFloat.mk (Int.ofNat (Int.natAbs g.Fnum)) g.Fexp :
              FloatSpec.Core.Defs.FlocqFloat beta) =
            (beta : ℝ) ^ e := by
        have hFabs := FloatSpec.Core.Float_prop.F2R_Zabs
          (beta := beta) g hβ
        calc
          F2R
              (FloatSpec.Core.Defs.FlocqFloat.mk (Int.ofNat (Int.natAbs g.Fnum)) g.Fexp :
                FloatSpec.Core.Defs.FlocqFloat beta)
              = |F2R g| := hFabs.symm
          _ = |r| := by rw [hg_val]
          _ = (beta : ℝ) ^ e := heq
      have hg_abs_can :
          FloatSpec.Core.Generic_fmt.canonical beta (FLT_exp emin prec)
            (FloatSpec.Core.Defs.FlocqFloat.mk (Int.ofNat (Int.natAbs g.Fnum)) g.Fexp) := by
        simpa using FloatSpec.Core.Generic_fmt.canonical_abs
          (beta := beta) (fexp := FLT_exp emin prec)
          g.Fnum g.Fexp hg_can
      have huniq :
          gg =
            (FloatSpec.Core.Defs.FlocqFloat.mk (Int.ofNat (Int.natAbs g.Fnum)) g.Fexp :
              FloatSpec.Core.Defs.FlocqFloat beta) := by
        apply FloatSpec.Core.Generic_fmt.canonical_unique
          (beta := beta) (hbeta := hβ) (fexp := FLT_exp emin prec)
        · exact hgg_can
        · exact hg_abs_can
        · calc
            FloatSpec.Core.Defs.F2R gg = (beta : ℝ) ^ e := by
              simpa using hgg_val
            _ = FloatSpec.Core.Defs.F2R
                (FloatSpec.Core.Defs.FlocqFloat.mk (Int.ofNat (Int.natAbs g.Fnum)) g.Fexp :
                  FloatSpec.Core.Defs.FlocqFloat beta) := by
              exact habs_val.symm
      have hgg_even : gg.Fnum % 2 = 0 := by
        have hpow_exp_pos :
            0 < Int.toNat (e - FLT_exp emin prec (e + 1)) := by
          have hp_ge_two : (2 : Int) ≤ prec := Int.add_one_le_iff.mpr hprec
          have hflt_lt : FLT_exp emin prec (e + 1) < e := by
            have hleft : e + 1 - prec < e := by omega
            have hright : emin < e := by simpa [e] using hxmag
            simpa [FLT_exp, FloatSpec.Core.FLT.FLT_exp] using
              (max_lt_iff.mpr ⟨hleft, hright⟩)
          have hcast_pos :
              (0 : Int) < (Int.toNat (e - FLT_exp emin prec (e + 1)) : Int) := by
            simpa [hdiff_cast] using sub_pos.mpr hflt_lt
          exact Nat.cast_pos.mp hcast_pos
        obtain ⟨q, hq⟩ :
            ∃ q : Nat, Int.toNat (e - FLT_exp emin prec (e + 1)) = q + 1 :=
          ⟨Int.toNat (e - FLT_exp emin prec (e + 1)) - 1,
            (Nat.succ_pred_eq_of_pos hpow_exp_pos).symm⟩
        change (beta ^ Int.toNat (e - FLT_exp emin prec (e + 1))) % 2 = 0
        rw [hq, pow_succ]
        have hdiv_beta : (2 : Int) ∣ beta := by
          rcases Ebeta with ⟨b, hb⟩
          exact ⟨b, hb⟩
        have hdiv_prod : (2 : Int) ∣ beta ^ q * beta :=
          dvd_mul_of_dvd_right hdiv_beta (beta ^ q)
        exact (Int.dvd_iff_emod_eq_zero (a := (2 : Int))
          (b := beta ^ q * beta)).mp hdiv_prod
      have hg_abs_even :
          (Int.ofNat (Int.natAbs g.Fnum)) % 2 = 0 := by
        simpa [huniq] using hgg_even
      exact False.elim (hg_odd ((Zeven_abs g.Fnum).mp hg_abs_even))
  have hmag_r := FloatSpec.Core.Raux.mag_unique
    (beta := beta) (x := r) (e := e) hβ hlow_r hupper_r
  simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, e, r]
    using hmag_r True.intro

/-- Coq: `fexp_round_odd`.

    FLT round-to-odd preserves the canonical exponent. -/
theorem fexp_round_odd_from_explicit_payload
  (emin prec : Int) [Prec_gt_0 prec]
  (hβ : 1 < beta)
  (Ebeta : ∃ b : Int, beta = 2 * b)
  (hNE : FloatSpec.Core.RoundNE.Exists_NE beta (FLT_exp emin prec))
  (x : ℝ)
  (hprec : 1 < prec) :
  FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp emin prec)
      (FloatSpec.Calc.Round.round beta (FLT_exp emin prec) oddMode x) =
    FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp emin prec) x := by
  classical
  haveI : FloatSpec.Core.RoundNE.Exists_NE beta (FLT_exp emin prec) := hNE
  let r : ℝ := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) oddMode x
  by_cases hx0 : x = 0
  · subst hx0
    have hround0 : r = 0 := by
      simp [r, FloatSpec.Calc.Round.round, oddMode, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, Zodd, FloatSpec.Core.Raux.Zfloor]
    simp [r, hround0, FloatSpec.Core.Generic_fmt.cexp]
  by_cases hsmall : FloatSpec.Core.Raux.mag beta x ≤ emin
  · have hx_abs_lt_emin : |x| < (beta : ℝ) ^ emin := by
      have htrip := FloatSpec.Core.Raux.mag_upper_bound
        (beta := beta) (x := x) hβ hx0
      have hx_upper : |x| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) := by
        simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure,
          FloatSpec.Core.Raux.abs_val] using htrip True.intro
      have hbpos : (0 : ℝ) < (beta : ℝ) := by
        exact_mod_cast (lt_trans Int.zero_lt_one hβ)
      have hbase_ge_one : (1 : ℝ) ≤ (beta : ℝ) := le_of_lt (by exact_mod_cast hβ)
      have hmag_le : (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) ≤
          (beta : ℝ) ^ emin := zpow_le_zpow_right₀ hbase_ge_one hsmall
      exact lt_of_lt_of_le hx_upper hmag_le
    have hfmt_min :
        generic_format beta (FLT_exp emin prec) ((beta : ℝ) ^ emin) := by
      have htrip := FloatSpec.Core.FLT.generic_format_FLT_bpow
        (prec := prec) (emin := emin) (beta := beta) (e := emin)
      simpa [FLT_exp] using htrip ⟨hβ, le_rfl⟩
    have hr_abs_le :
        |r| ≤ (beta : ℝ) ^ emin := by
      simpa [r, FloatSpec.Calc.Round.round, oddMode] using
        abs_roundR_le_generic_local
          (beta := beta) (fexp := FLT_exp emin prec)
          (rnd := Zodd) (x := x) (y := (beta : ℝ) ^ emin)
          hβ hfmt_min (le_of_lt hx_abs_lt_emin)
    have hr_ne : r ≠ 0 := by
      have hodd : Rnd_odd_pt (beta := beta) (fexp := FLT_exp emin prec) x r := by
        simpa [r] using
          round_odd_pt
            (beta := beta) (fexp := FLT_exp emin prec) x hNE hβ
      rcases hodd with ⟨_, hcases⟩
      rcases hcases with hr_eq_x | ⟨_, g, hg_val, _hg_can, hg_odd⟩
      · exact by
          intro hr0
          exact hx0 (by simpa [r, hr_eq_x] using hr0)
      · intro hr0
        have hg_val_zero : FloatSpec.Core.Defs.F2R g = 0 := by
          rw [← hg_val]
          exact hr0
        have hg_zero : g.Fnum = 0 := by
          exact FloatSpec.Core.Float_prop.eq_0_F2R
            (beta := beta) g hβ hg_val_zero
        have hg_even : g.Fnum % 2 = 0 := by simp [hg_zero]
        exact hg_odd hg_even
    have hr_abs_pos : 0 < |r| := abs_pos.mpr hr_ne
    have hr_abs_eq : |r| = (beta : ℝ) ^ emin := by
      have hmin_pos : 0 < (beta : ℝ) ^ emin := by
        have hbpos : (0 : ℝ) < (beta : ℝ) := by
          exact_mod_cast (lt_trans Int.zero_lt_one hβ)
        exact zpow_pos hbpos emin
      refine le_antisymm hr_abs_le ?_
      by_contra hlt_not
      have hlt : |r| < (beta : ℝ) ^ emin := lt_of_not_ge hlt_not
      have hsucc_le : FloatSpec.Core.Ulp.succ beta (FLT_exp emin prec) 0 ≤ |r| := by
        have hfmt_abs_r :
            generic_format beta (FLT_exp emin prec) |r| := by
          have hfmt_r :
              generic_format beta (FLT_exp emin prec) r := by
            simpa [r, FloatSpec.Calc.Round.round, oddMode] using
              FloatSpec.Core.Generic_fmt.generic_format_roundR
                (beta := beta) (fexp := FLT_exp emin prec)
                (rnd := Zodd) x hβ
          simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using
            (FloatSpec.Core.Generic_fmt.generic_format_abs
              (beta := beta) (fexp := FLT_exp emin prec) r hfmt_r)
        have hfmt0 : generic_format beta (FLT_exp emin prec) (0 : ℝ) :=
          FloatSpec.Core.Generic_fmt.generic_format_0_run
            (beta := beta) (fexp := FLT_exp emin prec)
        have htrip := FloatSpec.Core.Ulp.succ_le_lt
          (beta := beta) (fexp := FLT_exp emin prec)
          (x := 0) (y := |r|) hfmt0 hfmt_abs_r hr_abs_pos
        simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure]
          using htrip hβ
      have hsucc0 :
          FloatSpec.Core.Ulp.succ beta (FLT_exp emin prec) 0 =
            FloatSpec.Core.Ulp.ulp beta (FLT_exp emin prec) 0 := by
        have htrip := FloatSpec.Core.Ulp.succ_0
          (beta := beta) (fexp := FLT_exp emin prec)
        simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure]
          using htrip True.intro
      have hulp0 :
          FloatSpec.Core.Ulp.ulp beta (FLT_exp emin prec) 0 =
            (beta : ℝ) ^ emin := by
        have htrip := FloatSpec.Core.FLT.ulp_FLT_small
          (prec := prec) (emin := emin) (beta := beta) (x := 0)
        have hsmall0 : |(0 : ℝ)| < (beta : ℝ) ^ (emin + prec) := by
          have hbpos : (0 : ℝ) < (beta : ℝ) := by
            exact_mod_cast (lt_trans Int.zero_lt_one hβ)
          simpa using (zpow_pos hbpos (emin + prec))
        simpa [FLT_exp, Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure]
          using htrip ⟨hβ, hsmall0⟩
      have : (beta : ℝ) ^ emin ≤ |r| := by simpa [hsucc0, hulp0] using hsucc_le
      exact not_lt_of_ge this hlt
    have hmag_abs_r :
        FloatSpec.Core.Raux.mag beta |r| = emin + 1 := by
      have htrip := FloatSpec.Core.Raux.mag_bpow (beta := beta) (e := emin) hβ
      simpa [hr_abs_eq, Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure]
        using htrip True.intro
    have hmag_r :
        FloatSpec.Core.Raux.mag beta r = emin + 1 := by
      have htrip := FloatSpec.Core.Raux.mag_abs (beta := beta) (x := r) hβ
      have h := htrip True.intro
      exact Eq.trans h.symm hmag_abs_r
    have hcexp_r :
        FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp emin prec) r = emin := by
      have hsub_le : emin + 1 - prec ≤ emin := by
        have hp_ge_one : (1 : Int) ≤ prec :=
          Int.add_one_le_iff.mpr (Prec_gt_0.pos : 0 < prec)
        omega
      simp [FloatSpec.Core.Generic_fmt.cexp, hmag_r, FLT_exp,
        FloatSpec.Core.FLT.FLT_exp, hsub_le]
    have hcexp_x :
        FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp emin prec) x = emin := by
      have hsub_le : FloatSpec.Core.Raux.mag beta x - prec ≤ emin := by
        have hprec_nonneg : (0 : Int) ≤ prec := le_of_lt (Prec_gt_0.pos : 0 < prec)
        omega
      simp [FloatSpec.Core.Generic_fmt.cexp, FLT_exp,
        FloatSpec.Core.FLT.FLT_exp, hsub_le]
    simpa [r, hcexp_r, hcexp_x]
  · have hxmag : emin < FloatSpec.Core.Raux.mag beta x := lt_of_not_ge hsmall
    have hmag := mag_round_odd_from_explicit_payload
      (beta := beta) (emin := emin) (prec := prec)
      hβ Ebeta hNE x hprec hxmag
    simp [FloatSpec.Core.Generic_fmt.cexp, r, hmag]

/-- Coq `mag_round_odd`, with only the `Odd_propbis` section hypotheses.
The radix, positive-precision, and nearest-even instances are derived locally. -/
theorem mag_round_odd
    (emin prec : Int)
    (Even_beta : beta % 2 = 0)
    (prec_gt_1 : 1 < prec)
    (x : ℝ)
    (hxmag : emin < FloatSpec.Core.Raux.mag beta x) :
    FloatSpec.Core.Raux.mag beta
        (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) Zrnd_odd x) =
      FloatSpec.Core.Raux.mag beta x := by
  letI : Prec_gt_0 prec := ⟨by omega⟩
  have Ebeta : ∃ b : Int, beta = 2 * b := by
    exact (Int.dvd_iff_emod_eq_zero (a := (2 : Int)) (b := beta)).mpr Even_beta
  have hNE : FloatSpec.Core.RoundNE.Exists_NE beta (FLT_exp emin prec) := by
    exact ⟨Or.inr (by
      intro e
      constructor
      · intro hlarge
        simp only [FLT_exp, FloatSpec.Core.FLT.FLT_exp] at hlarge ⊢
        rcases max_lt_iff.mp hlarge with ⟨_, hemin_lt⟩
        exact max_lt (by omega) hemin_lt
      · intro hsmall
        simp only [FLT_exp, FloatSpec.Core.FLT.FLT_exp] at hsmall ⊢
        by_cases he : e ≤ emin
        · have hleft : e - prec ≤ emin := by omega
          have hnext : emin + 1 - prec ≤ emin := by omega
          simp [max_eq_right hleft, max_eq_right hnext]
        · have hemin_lt : emin < e := lt_of_not_ge he
          have hlt : max (e - prec) emin < e := max_lt (by omega) hemin_lt
          exact False.elim ((not_lt_of_ge hsmall) hlt))⟩
  simpa [FloatSpec.Calc.Round.round, oddMode, Zrnd_odd] using
    (mag_round_odd_from_explicit_payload
      (beta := beta) (emin := emin) (prec := prec)
      ValidRadix.valid Ebeta hNE x prec_gt_1 hxmag)

/-- Coq `fexp_round_odd`, with only the `Odd_propbis` section hypotheses. -/
theorem fexp_round_odd
    (emin prec : Int)
    (Even_beta : beta % 2 = 0)
    (prec_gt_1 : 1 < prec)
    (x : ℝ) :
    FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp emin prec)
        (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) Zrnd_odd x) =
      FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp emin prec) x := by
  letI : Prec_gt_0 prec := ⟨by omega⟩
  have Ebeta : ∃ b : Int, beta = 2 * b := by
    exact (Int.dvd_iff_emod_eq_zero (a := (2 : Int)) (b := beta)).mpr Even_beta
  have hNE : FloatSpec.Core.RoundNE.Exists_NE beta (FLT_exp emin prec) := by
    exact ⟨Or.inr (by
      intro e
      constructor
      · intro hlarge
        simp only [FLT_exp, FloatSpec.Core.FLT.FLT_exp] at hlarge ⊢
        rcases max_lt_iff.mp hlarge with ⟨_, hemin_lt⟩
        exact max_lt (by omega) hemin_lt
      · intro hsmall
        simp only [FLT_exp, FloatSpec.Core.FLT.FLT_exp] at hsmall ⊢
        by_cases he : e ≤ emin
        · have hleft : e - prec ≤ emin := by omega
          have hnext : emin + 1 - prec ≤ emin := by omega
          simp [max_eq_right hleft, max_eq_right hnext]
        · have hemin_lt : emin < e := lt_of_not_ge he
          have hlt : max (e - prec) emin < e := max_lt (by omega) hemin_lt
          exact False.elim ((not_lt_of_ge hsmall) hlt))⟩
  simpa [FloatSpec.Calc.Round.round, oddMode, Zrnd_odd] using
    (fexp_round_odd_from_explicit_payload
      (beta := beta) (emin := emin) (prec := prec)
      ValidRadix.valid Ebeta hNE x prec_gt_1)
