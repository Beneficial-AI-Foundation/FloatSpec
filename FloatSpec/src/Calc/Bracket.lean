/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4, ported from Coq: https://flocq.gitlabpages.inria.fr/

Locations: where a real number is positioned with respect to its rounded-down value in an arbitrary format
Translated from Coq file: flocq/src/Calc/Bracket.v
-/

import FloatSpec.src.Core
import FloatSpec.src.Core.Zaux
import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Float_prop
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real
open FloatSpec.Core
open Std.Do

namespace FloatSpec.Calc.Bracket

/-- Location type for bracketing: indicates position relative to boundaries -/
inductive Location where
  | loc_Exact : Location  -- Exactly at boundary
  | loc_Inexact : Ordering → Location  -- In interior with ordering info
  deriving DecidableEq

/-- Compare two real numbers and return an Ordering -/
noncomputable def compare (x y : ℝ) : Ordering :=
  if x < y then Ordering.lt
  else if x > y then Ordering.gt
  else Ordering.eq

/-- Inductive predicate for location relationship -/
inductive inbetween (d u x : ℝ) : Location → Prop where
  | inbetween_Exact : x = d → inbetween d u x Location.loc_Exact
  | inbetween_Inexact (l : Ordering) :
      (d < x ∧ x < u) → compare x ((d + u) / 2) = l →
      inbetween d u x (Location.loc_Inexact l)

section BasicOperations

variable (d u : ℝ)
variable (Hdu : d < u)

-- Helper lemmas used in distance/midpoint comparison
private lemma compare_sub_zero_real (a b : ℝ) :
    compare a b = compare (a - b) 0 := by
  classical
  by_cases hlt : a < b
  · have hsublt : a - b < 0 := sub_lt_zero.mpr hlt
    simp [compare, hlt, hsublt]
  · have hnotlt : ¬ a < b := hlt
    by_cases hgt : a > b
    · have hsubgt : 0 < a - b := sub_pos.mpr hgt
      have hnlt : ¬ (a - b) < 0 := not_lt.mpr (le_of_lt hsubgt)
      simp [compare, hnotlt, hgt, hnlt, hsubgt]
    · have heq : a = b := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hnotlt)
      have hsubeq : a - b = 0 := sub_eq_zero.mpr heq
      simp [compare, hnotlt, hgt, heq, hsubeq]

private lemma compare_mul_pos_right_zero (t c : ℝ) (hc : 0 < c) :
    compare (c * t) 0 = compare t 0 := by
  classical
  by_cases hlt : t < 0
  · have : c * t < c * 0 := mul_lt_mul_of_pos_left hlt hc
    have hlt' : c * t < 0 := by simpa using this
    simp [compare, hlt, hlt']
  · have hnotlt : ¬ t < 0 := hlt
    by_cases hgt : t > 0
    · have : c * 0 < c * t := mul_lt_mul_of_pos_left hgt hc
      have hgt' : 0 < c * t := by simpa using this
      have hnlt' : ¬ c * t < 0 := not_lt.mpr (le_of_lt hgt')
      simp [compare, hnotlt, hgt, hnlt', hgt']
    · have heq : t = 0 := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hnotlt)
      simp [compare, heq]
variable (x : ℝ)

/-- Determine location of x relative to interval `[d, u)`

    Classifies a real number's position within an interval:
    - Exact if x equals the lower bound d
    - Inexact with ordering information based on midpoint comparison
-/
noncomputable def inbetween_loc : Id Location :=
  pure (if x > d then
    Location.loc_Inexact (compare x ((d + u) / 2))
  else
    Location.loc_Exact)

/-- Specification: Location determination is correct

    The computed location accurately represents x's position in `[d, u)`
-/
theorem inbetween_spec (Hx : d ≤ x ∧ x < u) :
    ⦃⌜d ≤ x ∧ x < u⌝⦄
    inbetween_loc d u x
    ⦃⇓result => ⌜inbetween d u x result⌝⦄ := by
  intro _
  unfold inbetween_loc
  by_cases hx : x > d
  · -- Inexact case: d < x < u and l = compare x mid
    have hdx : d < x := hx
    have hxu : x < u := Hx.2
    simp [wp, PostCond.noThrow, Id.run, hx]
    refine inbetween.inbetween_Inexact (l := compare x ((d + u) / 2)) ?hb ?hc
    · exact ⟨hdx, hxu⟩
    · rfl
  · -- Exact case: x ≤ d and d ≤ x, hence x = d
    have hxd : x ≤ d := le_of_not_gt hx
    have hxeq : x = d := le_antisymm hxd Hx.1
    simp [wp, PostCond.noThrow, Id.run, hx]
    exact inbetween.inbetween_Exact hxeq

/-- Determine uniqueness of location

    Two valid locations for the same point must be equal
-/
def inbetween_unique_check (l l' : Location) : Id Bool :=
  pure (l == l')

/-- Specification: Location is unique

    If x has two valid locations in `[d, u)`, they must be identical
-/
theorem inbetween_unique (l l' : Location)
    (Hl : inbetween d u x l) (Hl' : inbetween d u x l') :
    ⦃⌜inbetween d u x l ∧ inbetween d u x l'⌝⦄
    inbetween_unique_check l l'
    ⦃⇓result => ⌜result = true⌝⦄ := by
  -- Use Triple.pure to discharge the Hoare triple for a pure computation
  apply Std.Do.Triple.pure (m := Id) (a := (l == l'))
  intro _
  -- Prove locations must be equal, then conclude by rewriting to `true`
  have hEq : l = l' := by
    cases Hl with
    | inbetween_Exact hxd =>
        cases Hl' with
        | inbetween_Exact _ =>
            rfl
        | inbetween_Inexact _ hbounds _ =>
            -- Contradiction: d < x but x = d
            have : False :=
              (lt_irrefl _)
                ((by simpa [hxd] using hbounds.1) : d < d)
            cases this
    | inbetween_Inexact ord hbounds hcmp =>
        have hxgt : d < x := hbounds.1
        cases Hl' with
        | inbetween_Exact hxeq =>
            -- Contradiction: d < x but x = d
            have : False :=
              (lt_irrefl _)
                ((by simpa [hxeq] using hxgt) : d < d)
            cases this
        | inbetween_Inexact ord' _ hcmp' =>
            -- Both inexact: compare is deterministic, so the orderings agree
            have hord : ord = ord' := by
              simpa [hcmp] using hcmp'
            simpa [hord]
  -- Turn equality into boolean equality for the BEq derived from DecidableEq
  simp [hEq, BEq.rfl]

end BasicOperations

section Properties

variable (d u x : ℝ)
variable (l : Location)
variable (Hdu : d < u)

/-- Extract bounds from inbetween property

    Returns whether x is within the interval bounds
-/
def inbetween_bounds_check (h : inbetween d u x l) : Id Bool :=
  sorry

/-- Specification: Bounds are satisfied

    Any x with a valid location satisfies d ≤ x < u
-/
theorem inbetween_bounds (h : inbetween d u x l) (Hdu : d < u) :
    ⦃⌜inbetween d u x l⌝⦄
    inbetween_bounds_check d u x l h
    ⦃⇓result => ⌜d ≤ x ∧ x < u⌝⦄ := by
  sorry

/-- Check bounds for non-exact locations

    For inexact locations, x is strictly between bounds
-/
def inbetween_bounds_not_Eq_check (h : inbetween d u x l)
    (hl : l ≠ Location.loc_Exact) : Id Bool :=
  sorry

/-- Specification: Strict bounds for inexact locations

    Non-exact locations guarantee strict inequalities
-/
theorem inbetween_bounds_not_Eq (h : inbetween d u x l)
    (hl : l ≠ Location.loc_Exact) :
    ⦃⌜inbetween d u x l ∧ l ≠ Location.loc_Exact⌝⦄
    inbetween_bounds_not_Eq_check d u x l h hl
    ⦃⇓result => ⌜d < x ∧ x < u⌝⦄ := by
  sorry

/-- Compare distances for inexact location

    Returns the ordering based on distances from boundaries
-/
def inbetween_distance_inexact_compute (ord : Ordering) : Id Ordering :=
  sorry

/-- Specification: Distance comparison for inexact locations

    The ordering reflects relative distances from interval endpoints
-/
theorem inbetween_distance_inexact (ord : Ordering)
    (h : inbetween d u x (Location.loc_Inexact ord)) :
    ⦃⌜inbetween d u x (Location.loc_Inexact ord)⌝⦄
    inbetween_distance_inexact_compute ord
    ⦃⇓result => ⌜compare (x - d) (u - x) = result⌝⦄ := by
  sorry

/-- Compute absolute distance comparison

    Uses absolute values for distance comparison
-/
def inbetween_distance_inexact_abs_compute (ord : Ordering) : Id Ordering :=
  sorry

/-- Specification: Absolute distance comparison

    The ordering reflects absolute distances from boundaries
-/
theorem inbetween_distance_inexact_abs (ord : Ordering)
    (h : inbetween d u x (Location.loc_Inexact ord)) :
    ⦃⌜inbetween d u x (Location.loc_Inexact ord)⌝⦄
    inbetween_distance_inexact_abs_compute ord
    ⦃⇓result => ⌜compare (|d - x|) (|u - x|) = result⌝⦄ := by
  sorry

/-- Construct a witness for location existence

    Produces an x value that has the given location in `[d, u)`
-/
noncomputable def inbetween_ex_witness (d u : ℝ) (l : Location) (Hdu : d < u) : Id ℝ :=
  -- Choose a witness depending on the desired ordering:
  --  - Exact: pick the lower bound d
  --  - Inexact Lt/Eq/Gt: pick a point at 1/4, 1/2, or 3/4 within (d, u)
  pure (match l with
  | Location.loc_Exact => d
  | Location.loc_Inexact ord =>
      let w := match ord with
        | Ordering.lt => (1 : ℝ) / 4
        | Ordering.eq => (2 : ℝ) / 4
        | Ordering.gt => (3 : ℝ) / 4
      d + w * (u - d))

/-- Specification: Location existence

    For any valid interval and location, there exists a corresponding point
-/
theorem inbetween_ex (d u : ℝ) (l : Location) (Hdu : d < u) :
    ⦃⌜d < u⌝⦄
    inbetween_ex_witness d u l Hdu
    ⦃⇓x => ⌜inbetween d u x l⌝⦄ := by
  sorry
  -- classical
  -- -- Rewrite the command to a `pure` and use the pure triple rule.
  -- intro _
  -- -- Reduce the triple on a pure computation to its postcondition goal.
  -- simp [inbetween_ex_witness, wp, PostCond.noThrow, Id.run]
  -- -- Prove the postcondition for the chosen witness by cases on `l`.
  -- cases l with
  -- | loc_Exact =>
  --     exact inbetween.inbetween_Exact rfl
  -- | loc_Inexact ord =>
  --     -- witness x = d + w * (u - d), with w depending on `ord`
  --     set w : ℝ := match ord with
  --       | Ordering.lt => (1 : ℝ) / 4
  --       | Ordering.eq => (2 : ℝ) / 4
  --       | Ordering.gt => (3 : ℝ) / 4
  --     have hpos : 0 < u - d := sub_pos.mpr Hdu
  --     have hw01 : 0 < w ∧ w < 1 := by
  --       unfold w
  --       cases ord <;> constructor <;> norm_num
  --     have hxgt : d < d + w * (u - d) := by
  --       have : 0 < w * (u - d) := mul_pos (show 0 < w from hw01.1) hpos
  --       simpa using (add_lt_add_left this d)
  --     have hxlt : d + w * (u - d) < u := by
  --       have : w * (u - d) < (u - d) := by
  --         simpa using (mul_lt_mul_of_pos_right hw01.2 hpos)
  --       have : d + w * (u - d) < d + (u - d) := add_lt_add_left this d
  --       simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  --     refine inbetween.inbetween_Inexact (l := ord) ?hb ?hc
  --     · -- supply the explicit point for clarity
  --       have : (fun x => d < x ∧ x < u) (d + w * (u - d)) := And.intro hxgt hxlt
  --       simpa using this
  --     · set m := ((d + u) / 2) with hm
  --       have hm_as_d_plus : m = d + (u - d) / 2 := by
  --         have : (d + u) / 2 = d + (u - d) / 2 := by ring
  --         simpa [hm] using this
  --       -- Compare the chosen point with the midpoint
  --       cases ord with
  --       | lt =>
  --           have hw : w = (1 : ℝ) / 4 := by unfold w; simp
  --           have hxlt' : d + w * (u - d) < m := by
  --             have hstep : d + (1 / 4 : ℝ) * (u - d) < d + (u - d) / 2 := by
  --               have : (1 / 4 : ℝ) * (u - d) < (u - d) / 2 := by
  --                 have : (1 / 4 : ℝ) < (1 / 2 : ℝ) := by norm_num
  --                 have := mul_lt_mul_of_pos_right this hpos
  --                 simpa [one_div, mul_comm] using this
  --               simpa using add_lt_add_left this d
  --             have : d + w * (u - d) = d + (1 / 4 : ℝ) * (u - d) := by simpa [hw]
  --             simpa [this, hm_as_d_plus, one_div] using hstep
  --           -- conclude with the appropriate ordering
  --           have : compare (d + w * (u - d)) m = Ordering.lt := by
  --             simp [compare, hxlt']
  --           simpa [this]
  --       | eq =>
  --           have hw : w = (1 : ℝ) / 2 := by unfold w; simp
  --           have hxeq' : d + w * (u - d) = m := by
  --             have : d + (1 / 2 : ℝ) * (u - d) = d + (u - d) / 2 := by ring
  --             have : d + w * (u - d) = d + (1 / 2 : ℝ) * (u - d) := by simpa [hw]
  --             simpa [this, hm_as_d_plus, one_div]
  --           have : compare (d + w * (u - d)) m = Ordering.eq := by
  --             simp [compare, hxeq']
  --           simpa [this]
  --       | gt =>
  --           have hw : w = (3 : ℝ) / 4 := by unfold w; simp
  --           have hxgt' : m < d + w * (u - d) := by
  --             have hstep : d + (u - d) / 2 < d + (3 / 4 : ℝ) * (u - d) := by
  --               have : (1 / 2 : ℝ) * (u - d) < (3 / 4 : ℝ) * (u - d) := by
  --                 have : (1 / 2 : ℝ) < (3 / 4 : ℝ) := by norm_num
  --                 simpa [one_div] using (mul_lt_mul_of_pos_right this hpos)
  --               simpa using add_lt_add_left this d
  --             have : d + (3 / 4 : ℝ) * (u - d) = d + w * (u - d) := by simpa [hw]
  --             simpa [this, hm_as_d_plus, one_div]
  --           have hnlt : ¬ d + w * (u - d) < m := not_lt.mpr (le_of_lt hxgt')
  --           have : compare (d + w * (u - d)) m = Ordering.gt := by
  --             simp [compare, hnlt, hxgt']
  --           simpa [this]

end Properties

section SteppingRanges

variable (start step : ℝ)
variable (nb_steps : Int)
variable (Hstep : 0 < step)

/-- Compute ordered steps

    Verifies that consecutive steps are properly ordered
-/
def ordered_steps_check (start step : ℝ) (k : Int) : Id Bool :=
  sorry

/-- Specification: Steps are ordered

    Each step increases by the step size
-/
lemma ordered_steps (k : Int) :
    ⦃⌜0 < step⌝⦄
    ordered_steps_check start step k
    ⦃⇓result => ⌜start + k * step < start + (k + 1) * step⌝⦄ := by
  sorry

/-- Calculate middle of range

    Computes the midpoint of a stepped range
-/
noncomputable def middle_range_calc (start step : ℝ) (k : Int) : Id ℝ :=
  pure (start + (k / 2 * step))

/-- Specification: Middle range calculation

    The midpoint formula is correct for stepped ranges
-/
lemma middle_range (k : Int) :
    ⦃⌜True⌝⦄
    middle_range_calc start step k
    ⦃⇓result => ⌜(start + (start + k * step)) / 2 = result⌝⦄ := by
  sorry

variable (Hnb_steps : 1 < nb_steps)

/-- Compute new location for inexact step

    Determines location in larger interval based on step location
-/
noncomputable def inbetween_step_not_Eq_compute (start step : ℝ) (nb_steps : Int) (x : ℝ) (k : Int) (ord : Ordering) : Id Location :=
  sorry

/-- Specification: Step location transformation

    Location in a step interval determines location in full range
-/
theorem inbetween_step_not_Eq (x : ℝ) (k : Int) (l : Location) (ord : Ordering)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x l)
    (Hk : 0 < k ∧ k < nb_steps)
    (Hord : compare x (start + (nb_steps / 2 * step)) = ord) :
    ⦃⌜inbetween (start + k * step) (start + (k + 1) * step) x l ∧
      0 < k ∧ k < nb_steps ∧
      compare x (start + (nb_steps / 2 * step)) = ord⌝⦄
    inbetween_step_not_Eq_compute start step nb_steps x k ord
    ⦃⇓result => ⌜inbetween start (start + nb_steps * step) x result⌝⦄ := by
  sorry

/-- Compute location for low step

    Determines location when in lower half of range
-/
def inbetween_step_Lo_compute : Id Location :=
  pure (Location.loc_Inexact Ordering.lt)

/-- Specification: Low step location

    Points in lower steps map to less-than ordering
-/
theorem inbetween_step_Lo (x : ℝ) (k : Int) (l : Location)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x l)
    (Hk1 : 0 < k) (Hk2 : 2 * k + 1 < nb_steps) :
    ⦃⌜inbetween (start + k * step) (start + (k + 1) * step) x l ∧
      0 < k ∧ 2 * k + 1 < nb_steps⌝⦄
    inbetween_step_Lo_compute
    ⦃⇓result => ⌜inbetween start (start + nb_steps * step) x result⌝⦄ := by
  sorry

/-- Compute location for high step

    Determines location when in upper half of range
-/
def inbetween_step_Hi_compute : Id Location :=
  pure (Location.loc_Inexact Ordering.gt)

/-- Specification: High step location

    Points in upper steps map to greater-than ordering
-/
theorem inbetween_step_Hi (x : ℝ) (k : Int) (l : Location)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x l)
    (Hk1 : nb_steps < 2 * k) (Hk2 : k < nb_steps) :
    ⦃⌜inbetween (start + k * step) (start + (k + 1) * step) x l ∧
      nb_steps < 2 * k ∧ k < nb_steps⌝⦄
    inbetween_step_Hi_compute
    ⦃⇓result => ⌜inbetween start (start + nb_steps * step) x result⌝⦄ := by
  sorry

/-- New location computation for even steps

    Determines location based on even number of steps
-/
noncomputable def new_location_even (nb_steps k : Int) (l : Location) : Id Location :=
  pure (if k = 0 then
    match l with
    | Location.loc_Exact => l
    | _ => Location.loc_Inexact Ordering.lt
  else
    Location.loc_Inexact
    (match compare (2 * k) nb_steps with
    | Ordering.lt => Ordering.lt
    | Ordering.eq => match l with
      | Location.loc_Exact => Ordering.eq
      | _ => Ordering.gt
    | Ordering.gt => Ordering.gt))

/-- Specification: Even step location is correct

    The computed location for even steps preserves interval properties
-/
theorem new_location_even_correct (He : nb_steps % 2 = 0) (x : ℝ) (k : Int) (l : Location)
    (Hk : 0 ≤ k ∧ k < nb_steps)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x l) :
    ⦃⌜nb_steps % 2 = 0 ∧ 0 ≤ k ∧ k < nb_steps ∧
      inbetween (start + k * step) (start + (k + 1) * step) x l⌝⦄
    new_location_even nb_steps k l
    ⦃⇓result => ⌜inbetween start (start + nb_steps * step) x result⌝⦄ := by
  sorry

/-- New location computation for odd steps

    Determines location based on odd number of steps
-/
noncomputable def new_location_odd (nb_steps k : Int) (l : Location) : Id Location :=
  pure (if k = 0 then
    match l with
    | Location.loc_Exact => l
    | _ => Location.loc_Inexact Ordering.lt
  else
    Location.loc_Inexact
    (match compare (2 * k + 1) nb_steps with
    | Ordering.lt => Ordering.lt
    | Ordering.eq => match l with
      | Location.loc_Inexact ord => ord
      | Location.loc_Exact => Ordering.lt
    | Ordering.gt => Ordering.gt))

/-- Specification: Odd step location is correct

    The computed location for odd steps preserves interval properties
-/
theorem new_location_odd_correct (Ho : nb_steps % 2 = 1) (x : ℝ) (k : Int) (l : Location)
    (Hk : 0 ≤ k ∧ k < nb_steps)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x l) :
    ⦃⌜nb_steps % 2 = 1 ∧ 0 ≤ k ∧ k < nb_steps ∧
      inbetween (start + k * step) (start + (k + 1) * step) x l⌝⦄
    new_location_odd nb_steps k l
    ⦃⇓result => ⌜inbetween start (start + nb_steps * step) x result⌝⦄ := by
  sorry

/-- New location computation

    Main entry point choosing between even and odd step logic
-/
noncomputable def new_location (nb_steps k : Int) (l : Location) : Id Location :=
  if nb_steps % 2 = 0 then
    new_location_even nb_steps k l
  else
    new_location_odd nb_steps k l

/-- Specification: New location is correct

    The computed location accurately represents position in full range
-/
theorem new_location_correct (x : ℝ) (k : Int) (l : Location)
    (Hk : 0 ≤ k ∧ k < nb_steps)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x l) :
    ⦃⌜0 ≤ k ∧ k < nb_steps ∧
      inbetween (start + k * step) (start + (k + 1) * step) x l⌝⦄
    new_location nb_steps k l
    ⦃⇓result => ⌜inbetween start (start + nb_steps * step) x result⌝⦄ := by
  sorry

end SteppingRanges

/-- Helper for float location -/
def inbetween_float (beta : Int) (m e : Int) (x : ℝ) (l : Location) : Prop :=
  inbetween ((Defs.F2R (Defs.FlocqFloat.mk m e : Defs.FlocqFloat beta)).run)
            ((Defs.F2R (Defs.FlocqFloat.mk (m + 1) e : Defs.FlocqFloat beta)).run) x l

/- Additional theorems mirroring Coq counterparts that were missing in Lean. -/

section ExtraCoqTheorems

variable {d u x : ℝ}

-- Step and parity auxiliary results
theorem inbetween_step_Lo_not_Eq
    (start step : ℝ) (nb_steps : Int)
    (Hstep : 0 < step)
    (x : ℝ) (l : Location)
    (Hx : inbetween start (start + step) x l)
    (Hl : l ≠ Location.loc_Exact) :
    inbetween start (start + nb_steps * step) x (Location.loc_Inexact Ordering.lt) := by
  sorry

lemma middle_odd
    (start step : ℝ) (k nb_steps : Int)
    (Hk : 2 * k + 1 = nb_steps) :
    (start + k * step + (start + (k + 1) * step)) / 2
      = start + (nb_steps / 2) * step := by
  sorry

theorem inbetween_step_any_Mi_odd
    (start step : ℝ) (nb_steps : Int)
    (x : ℝ) (k : Int) (l : Ordering)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x (Location.loc_Inexact l))
    (Hk : 2 * k + 1 = nb_steps) :
    inbetween start (start + nb_steps * step) x (Location.loc_Inexact l) := by
  sorry

theorem inbetween_step_Lo_Mi_Eq_odd
    (start step : ℝ) (nb_steps : Int)
    (x : ℝ) (k : Int)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x Location.loc_Exact)
    (Hk : 2 * k + 1 = nb_steps) :
    inbetween start (start + nb_steps * step) x (Location.loc_Inexact Ordering.lt) := by
  sorry

theorem inbetween_step_Hi_Mi_even
    (start step : ℝ) (nb_steps : Int)
    (x : ℝ) (k : Int) (l : Location)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x l)
    (Hl : l ≠ Location.loc_Exact)
    (Hk : 2 * k = nb_steps) :
    inbetween start (start + nb_steps * step) x (Location.loc_Inexact Ordering.gt) := by
  sorry

theorem inbetween_step_Mi_Mi_even
    (start step : ℝ) (nb_steps : Int)
    (x : ℝ) (k : Int)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x Location.loc_Exact)
    (Hk : 2 * k = nb_steps) :
    inbetween start (start + nb_steps * step) x (Location.loc_Inexact Ordering.eq) := by
  sorry

-- Compatibility under translation and scaling
theorem inbetween_plus_compat (x d u : ℝ) (l : Location) (t : ℝ) :
    inbetween d u x l → inbetween (d + t) (u + t) (x + t) l := by
  intro _; sorry

theorem inbetween_plus_reg (x d u : ℝ) (l : Location) (t : ℝ) :
    inbetween (d + t) (u + t) (x + t) l → inbetween d u x l := by
  intro _; sorry

theorem inbetween_mult_compat (x d u : ℝ) (l : Location) (s : ℝ)
    (Hs : 0 < s) :
    inbetween d u x l → inbetween (x * s) (d * s) (u * s) l := by
  intro _; sorry

theorem inbetween_mult_reg (x d u : ℝ) (l : Location) (s : ℝ)
    (Hs : 0 < s) :
    inbetween (x * s) (d * s) (u * s) l → inbetween x d u l := by
  intro _; sorry

-- Specialization to consecutive floats
variable (beta : Int)

theorem inbetween_float_bounds
    (x : ℝ) (m e : Int) (l : Location)
    (H : inbetween_float beta m e x l) :
    ((Defs.F2R (Defs.FlocqFloat.mk m e : Defs.FlocqFloat beta)).run ≤ x ∧
     x < (Defs.F2R (Defs.FlocqFloat.mk (m + 1) e : Defs.FlocqFloat beta)).run) := by
  sorry

theorem inbetween_float_new_location
    (x : ℝ) (m e : Int) (l : Location) (k : Int)
    (Hk : 0 < k)
    (Hx : inbetween_float beta m e x l) :
    inbetween_float beta (m / (beta ^ Int.natAbs k)) (e + k)
      x (Id.run (new_location (nb_steps := beta ^ Int.natAbs k)
                               (k := (m % (beta ^ Int.natAbs k))) l)) := by
  sorry

theorem inbetween_float_new_location_single
    (x : ℝ) (m e : Int) (l : Location)
    (Hx : inbetween_float beta m e x l) :
    inbetween_float beta (m / beta) (e + 1) x
      (Id.run (new_location (nb_steps := beta) (k := (m % beta)) l)) := by
  sorry

theorem inbetween_float_ex
    (m e : Int) (l : Location) :
    ∃ x : ℝ, inbetween_float beta m e x l := by
  sorry

theorem inbetween_float_unique
    (x : ℝ) (e m : Int) (l : Location) (m' : Int) (l' : Location)
    (H : inbetween_float beta m e x l)
    (H' : inbetween_float beta m' e x l') :
    m = m' ∧ l = l' := by
  sorry

end ExtraCoqTheorems

end FloatSpec.Calc.Bracket
