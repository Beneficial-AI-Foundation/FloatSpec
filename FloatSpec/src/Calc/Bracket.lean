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
import Mathlib.Tactic
import Std.Do.Triple
import Std.Tactic.Do
import FloatSpec.src.SimprocWP

set_option maxRecDepth 4096

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

-- Helpers to decode `compare` results back into equalities/inequalities
private lemma compare_eq_lt_real {a b : ℝ}
    (h : compare a b = Ordering.lt) : a < b := by
  classical
  unfold compare at h
  by_cases hlt : a < b
  · exact hlt
  · have hnotlt : ¬ a < b := hlt
    by_cases hgt : a > b
    · -- Then the code would be gt, contradiction
      have : Ordering.gt = Ordering.lt := by simpa [hnotlt, hgt] using h
      cases this
    · -- Then a = b, contradiction
      have heq : a = b := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hnotlt)
      have : Ordering.eq = Ordering.lt := by simpa [hnotlt, hgt, heq] using h
      cases this

private lemma compare_eq_eq_real {a b : ℝ}
    (h : compare a b = Ordering.eq) : a = b := by
  classical
  unfold compare at h
  by_cases hlt : a < b
  · -- Then result would be lt, contradiction
    have : Ordering.lt = Ordering.eq := by simpa [hlt] using h.symm
    cases this
  · have hnotlt : ¬ a < b := hlt
    by_cases hgt : a > b
    · -- Then result would be gt, contradiction
      have : Ordering.gt = Ordering.eq := by simpa [hnotlt, hgt] using h
      cases this
    · -- Neither lt nor gt ⇒ equality
      exact le_antisymm (le_of_not_gt hgt) (le_of_not_gt hnotlt)

private lemma compare_eq_gt_real {a b : ℝ}
    (h : compare a b = Ordering.gt) : b < a := by
  classical
  unfold compare at h
  by_cases hlt : a < b
  · -- Then result would be lt, contradiction
    have : Ordering.lt = Ordering.gt := by simpa [hlt] using h.symm
    cases this
  · have hnotlt : ¬ a < b := hlt
    by_cases hgt : a > b
    · -- Desired
      simpa using hgt
    · -- Then equality, contradiction with gt
      have heq : a = b := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hnotlt)
      have : Ordering.eq = Ordering.gt := by simpa [hnotlt, hgt, heq] using h
      cases this

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
noncomputable def inbetween_loc : Location :=
  (if x > d then
    Location.loc_Inexact (compare x ((d + u) / 2))
  else
    Location.loc_Exact)

/-- Specification: Location determination is correct

    The computed location accurately represents x's position in `[d, u)`
-/
@[spec]
theorem inbetween_spec (Hx : d ≤ x ∧ x < u) :
    ⦃⌜d ≤ x ∧ x < u⌝⦄
    (pure (inbetween_loc d u x) : Id Location)
    ⦃⇓result => ⌜inbetween d u x result⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold inbetween_loc
  by_cases hx : x > d
  · -- Inexact case: d < x < u and l = compare x mid
    have hdx : d < x := hx
    have hxu : x < u := Hx.2
    simp [hx]
    refine inbetween.inbetween_Inexact (l := compare x ((d + u) / 2)) ?hb ?hc
    · exact ⟨hdx, hxu⟩
    · rfl
  · -- Exact case: x ≤ d and d ≤ x, hence x = d
    have hxd : x ≤ d := le_of_not_gt hx
    have hxeq : x = d := le_antisymm hxd Hx.1
    simp [hx]
    exact inbetween.inbetween_Exact hxeq

/-- Determine uniqueness of location

    Two valid locations for the same point must be equal
-/
def inbetween_unique_check (l l' : Location) : Bool :=
  (l == l')

/-- Specification: Location is unique

    If x has two valid locations in `[d, u)`, they must be identical
-/
theorem inbetween_unique (l l' : Location)
    (Hl : inbetween d u x l) (Hl' : inbetween d u x l') :
    ⦃⌜inbetween d u x l ∧ inbetween d u x l'⌝⦄
    (pure (inbetween_unique_check l l') : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, inbetween_unique_check]
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
def inbetween_bounds_check (h : inbetween d u x l) : Unit :=
  -- Computation carries no data; theorem provides the bounds.
  ()

/-- Specification: Bounds are satisfied

    Any x with a valid location satisfies d ≤ x < u
-/
theorem inbetween_bounds (h : inbetween d u x l) (Hdu : d < u) :
    ⦃⌜inbetween d u x l⌝⦄
    (pure (inbetween_bounds_check d u x l h) : Id Unit)
    ⦃⇓result => ⌜d ≤ x ∧ x < u⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, inbetween_bounds_check]
  -- Discharge the bounds from the inbetween hypothesis
  cases h with
  | inbetween_Exact hxeq =>
      -- From x = d and d < u, we get d ≤ x and x < u
      refine And.intro ?hle ?hlt
      · simpa [hxeq]
      · simpa [hxeq] using Hdu
  | inbetween_Inexact _ hbounds _ =>
      -- Already have strict bounds, weaken left to ≤
      exact And.intro (le_of_lt hbounds.1) hbounds.2

/-- Check bounds for non-exact locations

    For inexact locations, x is strictly between bounds
-/
def inbetween_bounds_not_Eq_check (h : inbetween d u x l)
    (hl : l ≠ Location.loc_Exact) : Unit :=
  -- Computation carries no data; theorem provides the strict bounds.
  ()

/-- Specification: Strict bounds for inexact locations

    Non-exact locations guarantee strict inequalities
-/
theorem inbetween_bounds_not_Eq (h : inbetween d u x l)
    (hl : l ≠ Location.loc_Exact) :
    ⦃⌜inbetween d u x l ∧ l ≠ Location.loc_Exact⌝⦄
    (pure (inbetween_bounds_not_Eq_check d u x l h hl) : Id Unit)
    ⦃⇓result => ⌜d < x ∧ x < u⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, inbetween_bounds_not_Eq_check]
  -- Use the inbetween hypothesis and non-exactness to derive strict bounds
  cases h with
  | inbetween_Exact hxeq =>
      -- Contradiction: location is exact but assumed non-exact
      have : False := by
        -- In this branch, `l` is definitionally `loc_Exact`.
        exact hl rfl
      cases this
  | inbetween_Inexact _ hbounds _ =>
      exact And.intro hbounds.1 hbounds.2

/-- Compare distances for inexact location

    Returns the ordering based on distances from boundaries
-/
def inbetween_distance_inexact_compute (ord : Ordering) : Ordering :=
  -- For inexact locations, the result ordering is exactly `compare x mid`.
  -- The compute function just returns the provided ordering parameter.
  ord

/-- Specification: Distance comparison for inexact locations

    The ordering reflects relative distances from interval endpoints
-/
theorem inbetween_distance_inexact (ord : Ordering)
    (h : inbetween d u x (Location.loc_Inexact ord)) :
    ⦃⌜inbetween d u x (Location.loc_Inexact ord)⌝⦄
    (pure (inbetween_distance_inexact_compute ord) : Id Ordering)
    ⦃⇓result => ⌜compare (x - d) (u - x) = result⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, inbetween_distance_inexact_compute]
  -- Extract facts from the inexact-location hypothesis
  cases h with
  | inbetween_Inexact _ _ hc =>
      -- Show that comparing distances is the same as comparing to the midpoint
      have h1 : compare (x - d) (u - x) =
          compare ((x - d) - (u - x)) 0 :=
        compare_sub_zero_real (a := x - d) (b := u - x)
      have hlin : ((x - d) - (u - x)) = 2 * (x - (d + u) / 2) := by
        ring
      have h2pos : (0 : ℝ) < 2 := by
        norm_num
      have h2 : compare (2 * (x - (d + u) / 2)) 0 =
          compare (x - (d + u) / 2) 0 := by
        simpa using
          compare_mul_pos_right_zero (t := (x - (d + u) / 2)) (c := (2 : ℝ)) h2pos
      have h3 : compare (x - (d + u) / 2) 0 =
          compare x ((d + u) / 2) :=
        (compare_sub_zero_real (a := x) (b := (d + u) / 2)).symm
      have hcmp_mid : compare (x - d) (u - x) = compare x ((d + u) / 2) := by
        calc
          compare (x - d) (u - x)
              = compare ((x - d) - (u - x)) 0 := h1
          _   = compare (2 * (x - (d + u) / 2)) 0 := by simpa [hlin]
          _   = compare (x - (d + u) / 2) 0 := h2
          _   = compare x ((d + u) / 2) := h3
      have : compare (x - d) (u - x) = ord := by
        simpa [hcmp_mid] using hc
      exact this

/-- Compute absolute distance comparison

    Uses absolute values for distance comparison
-/
def inbetween_distance_inexact_abs_compute (ord : Ordering) : Ordering :=
  ord

/-- Specification: Absolute distance comparison

    The ordering reflects absolute distances from boundaries
-/
theorem inbetween_distance_inexact_abs (ord : Ordering)
    (h : inbetween d u x (Location.loc_Inexact ord)) :
    ⦃⌜inbetween d u x (Location.loc_Inexact ord)⌝⦄
    (pure (inbetween_distance_inexact_abs_compute ord) : Id Ordering)
    ⦃⇓result => ⌜compare (|d - x|) (|u - x|) = result⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, inbetween_distance_inexact_abs_compute]
  -- Use the inexact-location hypothesis to rewrite absolute values
  cases h with
  | inbetween_Inexact _ hbounds hcmp =>
      have hxgt : 0 < x - d := sub_pos.mpr hbounds.1
      have hugt : 0 < u - x := sub_pos.mpr hbounds.2
      have hxge : 0 ≤ x - d := le_of_lt hxgt
      have huge : 0 ≤ u - x := le_of_lt hugt
      have habs_d : |d - x| = x - d := by
        -- |d - x| = |x - d| and x - d ≥ 0 in the inexact case
        simpa [abs_sub_comm] using (abs_of_nonneg hxge)
      have habs_u : |u - x| = u - x := by
        simpa using (abs_of_nonneg huge)
      -- Reduce to the midpoint comparison as in the non-absolute case
      have h1 : compare (x - d) (u - x) =
          compare ((x - d) - (u - x)) 0 :=
        compare_sub_zero_real (a := x - d) (b := u - x)
      have hlin : ((x - d) - (u - x)) = 2 * (x - (d + u) / 2) := by
        ring
      have h2pos : (0 : ℝ) < 2 := by
        norm_num
      have h2 : compare (2 * (x - (d + u) / 2)) 0 =
          compare (x - (d + u) / 2) 0 := by
        simpa using
          compare_mul_pos_right_zero (t := (x - (d + u) / 2)) (c := (2 : ℝ)) h2pos
      have h3 : compare (x - (d + u) / 2) 0 =
          compare x ((d + u) / 2) :=
        (compare_sub_zero_real (a := x) (b := (d + u) / 2)).symm
      have hcmp_mid : compare (x - d) (u - x) = compare x ((d + u) / 2) := by
        calc
          compare (x - d) (u - x)
              = compare ((x - d) - (u - x)) 0 := h1
          _   = compare (2 * (x - (d + u) / 2)) 0 := by simpa [hlin]
          _   = compare (x - (d + u) / 2) 0 := h2
          _   = compare x ((d + u) / 2) := h3
      -- Conclude by rewriting absolutes and using the stored comparison
      have : compare (|d - x|) (|u - x|) = compare (x - d) (u - x) := by
        simpa [habs_d, habs_u]
      simpa [this, hcmp_mid] using hcmp

/-- Construct a witness for location existence

    Produces an x value that has the given location in `[d, u)`
-/
noncomputable def inbetween_ex_witness (d u : ℝ) (l : Location) (Hdu : d < u) : ℝ :=
  -- Choose a witness depending on the desired ordering:
  --  - Exact: pick the lower bound d
  --  - Inexact Lt/Eq/Gt: pick a point at 1/4, 1/2, or 3/4 within (d, u)
  match l with
  | Location.loc_Exact => d
  | Location.loc_Inexact ord =>
      let w := match ord with
        | Ordering.lt => (1 : ℝ) / 4
        | Ordering.eq => (2 : ℝ) / 4
        | Ordering.gt => (3 : ℝ) / 4
      d + w * (u - d)

/-- Specification: Location existence

    For any valid interval and location, there exists a corresponding point
-/
theorem inbetween_ex (d u : ℝ) (l : Location) (Hdu : d < u) :
    ⦃⌜d < u⌝⦄
    (pure (inbetween_ex_witness d u l Hdu) : Id ℝ)
    ⦃⇓x => ⌜inbetween d u x l⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Now prove the postcondition on the concrete returned value.
  cases l with
  | loc_Exact =>
      -- The witness is `d`, which is exactly at the lower bound.
      simp [inbetween_ex_witness]
      exact inbetween.inbetween_Exact rfl
  | loc_Inexact ord =>
      -- The witness is `x = d + w * (u - d)` with `w ∈ {1/4, 1/2, 3/4}`.
      -- Define `w` first so we can rewrite the returned value to use `w`.
      set w : ℝ := match ord with
        | Ordering.lt => (1 : ℝ) / 4
        | Ordering.eq => (2 : ℝ) / 4
        | Ordering.gt => (3 : ℝ) / 4
      -- Now simplify the returned value; keep `w` abstract to avoid notation churn.
      simp [inbetween_ex_witness]
      have hpos : 0 < u - d := sub_pos.mpr Hdu
      have hw01 : 0 < w ∧ w < 1 := by
        unfold w
        cases ord <;> constructor <;> norm_num
      have hxgt : d < d + w * (u - d) := by
        have : 0 < w * (u - d) := mul_pos (show 0 < w from hw01.1) hpos
        simpa using (add_lt_add_left this d)
      have hxlt : d + w * (u - d) < u := by
        have : w * (u - d) < (1 : ℝ) * (u - d) := by
          simpa using (mul_lt_mul_of_pos_right hw01.2 hpos)
        have : d + w * (u - d) < d + (1 : ℝ) * (u - d) := add_lt_add_right this d
        simpa [one_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      refine inbetween.inbetween_Inexact (l := ord) ?hb ?hc
      · -- Normalize the witness expression to match the constructor arguments.
        -- The returned point is exactly `d + w * (u - d)` by construction.
        exact And.intro (by simpa [w] using hxgt)
                            (by simpa [w] using hxlt)
      · -- Show the comparison with the midpoint matches the requested ordering.
        set m := ((d + u) / 2) with hm
        have hm_as_d_plus : m = d + (u - d) / 2 := by
          have : (d + u) / 2 = d + (u - d) / 2 := by ring
          simpa [hm] using this
        -- Decide according to `ord`.
        cases ord with
        | lt =>
            have hw : w = (1 : ℝ) / 4 := by unfold w; simp
            have hxlt' : d + w * (u - d) < m := by
              have hcoef : (1 / 4 : ℝ) < (1 / 2 : ℝ) := by norm_num
              have : (1 / 4 : ℝ) * (u - d) < (1 / 2 : ℝ) * (u - d) :=
                mul_lt_mul_of_pos_right hcoef hpos
              have : d + (1 / 4 : ℝ) * (u - d) < d + (1 / 2 : ℝ) * (u - d) :=
                add_lt_add_right this d
              simpa [hw, hm_as_d_plus, one_div, mul_comm] using this
            have hcmp : compare (d + w * (u - d)) m = Ordering.lt := by
              simp [compare, hxlt']
            -- Rewrite goal's coefficient from the `match` using `w`.
            simpa [w] using hcmp
        | eq =>
            -- In the `eq` branch, the weight is `w = 2/4` by construction.
            have hw2 : w = (2 : ℝ) / 4 := by unfold w; simp
            -- Show that this point is exactly the midpoint `m`.
            have hxeq2 : d + w * (u - d) = m := by
              have hv24 : (2 : ℝ) / 4 = (1 : ℝ) / 2 := by norm_num
              -- turn `(2/4)*(u-d)` into `(u-d)/2`
              have : (2 : ℝ) / 4 * (u - d) = (u - d) / 2 := by
                simpa [hv24, one_div, mul_comm] using (mul_one_div (u - d) (2 : ℝ))
              -- assemble the pieces
              simpa [hw2, this, hm_as_d_plus]
            have hcmp2 : compare (d + w * (u - d)) m = Ordering.eq := by
              simpa [compare, hxeq2]
            -- Rewrite to match the goal's `match`-based coefficient form via `w`.
            simpa [w] using hcmp2
        | gt =>
            have hw : w = (3 : ℝ) / 4 := by unfold w; simp
            have hxgt' : m < d + w * (u - d) := by
              have hcoef : (1 / 2 : ℝ) < (3 / 4 : ℝ) := by norm_num
              have : (1 / 2 : ℝ) * (u - d) < (3 / 4 : ℝ) * (u - d) :=
                mul_lt_mul_of_pos_right hcoef hpos
              have : d + (1 / 2 : ℝ) * (u - d) < d + (3 / 4 : ℝ) * (u - d) :=
                add_lt_add_right this d
              simpa [hm_as_d_plus, hw, one_div, mul_comm] using this
            have hnlt : ¬ d + w * (u - d) < m := not_lt.mpr (le_of_lt hxgt')
            have hcmp : compare (d + w * (u - d)) m = Ordering.gt := by
              simp [compare, hnlt, hxgt']
            -- Rewrite goal's coefficient from the `match` using `w`.
            simpa [w] using hcmp

end Properties

section SteppingRanges

variable (start step : ℝ)
variable (nb_steps : Int)
variable (Hstep : 0 < step)

/-- Compute ordered steps

    Verifies that consecutive steps are properly ordered
-/
def ordered_steps_check (start step : ℝ) (k : Int) : Unit :=
  -- Computation carries no data; theorem proves the strict inequality.
  ()

/-- Specification: Steps are ordered

    Each step increases by the step size
-/
lemma ordered_steps (k : Int) :
    ⦃⌜0 < step⌝⦄
    (pure (ordered_steps_check start step k) : Id Unit)
    ⦃⇓result => ⌜start + k * step < start + (k + 1) * step⌝⦄ := by
  intro hstep
  simp only [wp, PostCond.noThrow, pure, ordered_steps_check]
  -- Show that adding a positive `step` strictly increases the value.
  have hl : start + k * step < start + k * step + step := by
    simpa using (add_lt_add_left hstep (start + k * step))
  -- Rewrite `(k + 1) * step` as `k * step + step`.
  simpa [Int.cast_add, Int.cast_ofNat, add_mul, one_mul]
    using hl

/-- Calculate middle of range

    Computes the midpoint of a stepped range
-/
noncomputable def middle_range_calc (start step : ℝ) (k : Int) : ℝ :=
  -- Return the midpoint of the two consecutive stepped points explicitly.
  (start + (start + k * step)) / 2

/-- Specification: Middle range calculation

    The midpoint formula is correct for stepped ranges
-/
lemma middle_range (k : Int) :
    ⦃⌜True⌝⦄
    (pure (middle_range_calc start step k) : Id ℝ)
    ⦃⇓result => ⌜(start + (start + k * step)) / 2 = result⌝⦄ := by
  -- For a pure computation, the post-condition holds by reflexivity.
  apply Std.Do.Triple.pure (m := Id)
  intro _
  simp [middle_range_calc]

variable (Hnb_steps : 1 < nb_steps)

/-- Compute new location for inexact step

    Determines location in larger interval based on step location
-/
noncomputable def inbetween_step_not_Eq_compute (start step : ℝ) (nb_steps : Int) (x : ℝ) (k : Int) (ord : Ordering) : Location :=
  -- For the global interval, we keep the same inexact ordering `ord`.
  Location.loc_Inexact ord

/-- Specification: Step location transformation

    Location in a step interval determines location in full range
-/
theorem inbetween_step_not_Eq (x : ℝ) (k : Int) (l : Location) (ord : Ordering)
    (Hstep : 0 < step)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x l)
    (Hk : 0 < k ∧ k < nb_steps)
    (Hord : compare x (start + (nb_steps / 2 * step)) = ord) :
    ⦃⌜inbetween (start + k * step) (start + (k + 1) * step) x l ∧
      0 < k ∧ k < nb_steps ∧
      compare x (start + (nb_steps / 2 * step)) = ord⌝⦄
    (pure (inbetween_step_not_Eq_compute start step nb_steps x k ord) : Id Location)
    ⦃⇓result => ⌜inbetween start (start + nb_steps * step) x result⌝⦄ := by
  -- Discharge the Hoare triple for a pure computation
  apply Std.Do.Triple.pure (m := Id)
  intro hpre
  -- Unpack the precondition pieces
  rcases hpre with ⟨Hx', hkpos, hklt, hcmp⟩
  have Hx := Hx'
  -- We return an inexact location with ordering `ord` for the global interval
  dsimp [inbetween_step_not_Eq_compute]
  -- Show the strict global bounds and the midpoint comparison
  refine inbetween.inbetween_Inexact (l := ord) ?hbounds ?hord
  · -- Bounds: start < x < start + nb_steps * step
    -- First, `start < start + k * step` since `k > 0` and `step > 0`.
    have hkposR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
    have hsteppos : 0 < step := Hstep
    have hpos_add : start < start + (k * step) := by
      have hz : 0 < (k : ℝ) * step := mul_pos hkposR hsteppos
      simpa using (add_lt_add_left hz start)
    -- Next, deduce `start < x` from the step-local location `Hx`.
    have hx_gt_start : start < x := by
      cases Hx with
      | inbetween_Exact hxeq =>
          -- x = start + k * step with k > 0 and step > 0
          simpa [hxeq] using hpos_add
      | inbetween_Inexact _ hbounds _ =>
          -- start < start + k * step < x
          exact lt_trans hpos_add hbounds.1
    -- For the upper bound, use k + 1 ≤ nb_steps since k < nb_steps (integers)
    have hle_succ : k + 1 ≤ nb_steps := by
      -- `k + 1 ≤ nb_steps` ↔ `k < nb_steps`
      exact (Int.add_one_le_iff.mpr hklt)
    have hle_succR : (k + 1 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast hle_succ
    have hstep_nonneg : 0 ≤ step := le_of_lt hsteppos
    have hmul_le : (k + 1 : ℝ) * step ≤ (nb_steps : ℝ) * step :=
      mul_le_mul_of_nonneg_right hle_succR hstep_nonneg
    -- From local upper bound x < start + (k + 1) * step and monotonicity, get global bound
    have hx_lt_step_succ : x < start + (k + 1) * step := by
      cases Hx with
      | inbetween_Exact hxeq =>
          -- x = start + k * step; x < start + (k + 1) * step since step > 0
          have : start + k * step < start + k * step + step := by
            simpa using (add_lt_add_left hsteppos (start + k * step))
          simpa [hxeq, add_mul, one_mul, Int.cast_add, Int.cast_ofNat]
            using this
      | inbetween_Inexact _ hbounds _ => exact hbounds.2
    have hx_lt_global : x < start + nb_steps * step := by
      -- Rewrite `(k + 1) * step ≤ nb_steps * step` inside a larger sum with `start`
      have : start + ((k + 1 : ℝ) * step) ≤ start + (nb_steps : ℝ) * step :=
        add_le_add_right hmul_le start
      exact lt_of_lt_of_le hx_lt_step_succ this
    exact ⟨hx_gt_start, hx_lt_global⟩
  · -- Midpoint comparison: show global midpoint equals `start + (nb_steps/2 * step)`
    have hmid_eq : (start + (start + nb_steps * step)) / 2 =
        start + (nb_steps / 2 * step) := by
      -- Algebraic normalization
      ring
    -- Use the provided comparison at this midpoint
    simpa [hmid_eq] using hcmp

/-- Compute location for low step

    Determines location when in lower half of range
-/
def inbetween_step_Lo_compute : Location :=
  (Location.loc_Inexact Ordering.lt)

/-- Specification: Low step location

    Points in lower steps map to less-than ordering
-/
theorem inbetween_step_Lo (x : ℝ) (k : Int) (l : Location)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x l)
    (Hk1 : 0 < k) (Hk2 : 2 * k + 1 < nb_steps) (Hstep : 0 < step) :
    ⦃⌜inbetween (start + k * step) (start + (k + 1) * step) x l ∧
      0 < k ∧ 2 * k + 1 < nb_steps⌝⦄
    (pure inbetween_step_Lo_compute : Id Location)
    ⦃⇓result => ⌜inbetween start (start + nb_steps * step) x result⌝⦄ := by
  -- Discharge the Hoare triple for a pure computation
  apply Std.Do.Triple.pure (m := Id)
  intro hpre
  rcases hpre with ⟨Hx', hk1, hk2⟩
  -- The computation returns an inexact location with ordering `lt`.
  dsimp [inbetween_step_Lo_compute]
  -- We show global strict bounds and that x is left of the global midpoint.
  refine inbetween.inbetween_Inexact (l := Ordering.lt) ?hbounds ?hcmp
  · -- Global bounds: start < x < start + nb_steps * step
    -- First, start < start + k * step since k > 0 and step > 0.
    have hkposR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hsteppos : 0 < step := Hstep
    have hz : 0 < (k : ℝ) * step := mul_pos hkposR hsteppos
    have hpos_add : start < start + (k * step) := by
      simpa using (add_lt_add_left hz start)
    -- Deduce start < x from the step-local location `Hx'`.
    have hx_gt_start : start < x := by
      cases Hx' with
      | inbetween_Exact hxeq =>
          simpa [hxeq] using hpos_add
      | inbetween_Inexact _ hbounds _ =>
          exact lt_trans hpos_add hbounds.1
    -- For the global upper bound, use k + 1 ≤ nb_steps since 2*k+1 < nb_steps
    have hle_succ : k + 1 ≤ nb_steps := by
      -- From 2*k + 1 < nb_steps, we derive 2*k + 2 ≤ nb_steps, hence k + 1 ≤ nb_steps/??
      -- Here we only need k + 1 ≤ nb_steps.
      -- Since k < 2*k + 1, transitivity gives k < nb_steps and thus k + 1 ≤ nb_steps.
      have hk0 : 0 ≤ k := le_of_lt hk1
      have hk_le_2k : k ≤ 2 * k := by
        -- k ≤ k + k = 2*k
        have := add_le_add_left hk0 k
        simpa [two_mul] using this
      have h2k_lt : 2 * k < 2 * k + 1 := by
        exact Int.lt_add_one_iff.mpr (le_refl _)
      have hk_lt_2k1 : k < 2 * k + 1 := lt_of_le_of_lt hk_le_2k h2k_lt
      have hk_lt_nb : k < nb_steps := lt_trans hk_lt_2k1 hk2
      exact Int.add_one_le_iff.mpr hk_lt_nb
    have hle_succR : (k + 1 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast hle_succ
    have hstep_nonneg : 0 ≤ step := le_of_lt hsteppos
    have hmul_le : (k + 1 : ℝ) * step ≤ (nb_steps : ℝ) * step :=
      mul_le_mul_of_nonneg_right hle_succR hstep_nonneg
    -- From local upper bound x < start + (k + 1) * step and monotonicity, get global bound
    have hx_lt_step_succ : x < start + (k + 1) * step := by
      cases Hx' with
      | inbetween_Exact hxeq =>
          -- x = start + k * step; then x < start + (k + 1) * step since step > 0
          have : start + k * step < start + k * step + step := by
            simpa using (add_lt_add_left hsteppos (start + k * step))
          simpa [hxeq, add_mul, one_mul, Int.cast_add, Int.cast_ofNat]
            using this
      | inbetween_Inexact _ hbounds _ => exact hbounds.2
    have hx_lt_global : x < start + nb_steps * step := by
      have : start + ((k + 1 : ℝ) * step) ≤ start + (nb_steps : ℝ) * step :=
        add_le_add_right hmul_le start
      exact lt_of_lt_of_le hx_lt_step_succ this
    exact ⟨hx_gt_start, hx_lt_global⟩
  · -- Midpoint comparison: show x is strictly less than the global midpoint
    -- First show start + (k+1)*step ≤ (start + (start + nb_steps * step)) / 2
    have two_pos : 0 < (2 : ℝ) := by norm_num
    have h2leInt : 2 * (k + 1) ≤ nb_steps := by
      -- From 2*k + 1 < nb_steps, we get 2*k + 2 ≤ nb_steps, i.e., 2*(k+1) ≤ nb_steps
      have h := Int.add_one_le_iff.mpr hk2
      simpa [two_mul, add_comm, add_left_comm, add_assoc] using h
    have h2leR : (2 : ℝ) * (k + 1 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast h2leInt
    have hmul : (2 : ℝ) * ((k + 1 : ℝ) * step) ≤ (nb_steps : ℝ) * step := by
      -- regroup factors on the left to use distributivity later
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_right h2leR (le_of_lt Hstep))
    have h2 : 2 * (start + (k + 1) * step) ≤ start + (start + nb_steps * step) := by
      calc
        2 * (start + (k + 1) * step)
            = 2 * start + 2 * ((k + 1 : ℝ) * step) := by ring
        _   ≤ 2 * start + (nb_steps : ℝ) * step := by
              exact add_le_add_right hmul (2 * start)
        _   = start + (start + nb_steps * step) := by ring
    have h2' : (start + (k + 1) * step) * 2 ≤ start + (start + nb_steps * step) := by
      simpa [mul_comm] using h2
    have hmid_upper : start + (k + 1) * step ≤ (start + (start + nb_steps * step)) / 2 := by
      -- Use le_div_iff₀: a ≤ b / 2  ↔  2*a ≤ b for 2 > 0
      simpa using ((le_div_iff₀ two_pos).mpr h2')
    -- From local upper bound, deduce x < the global midpoint written as average
    have hx_lt_step_succ : x < start + (k + 1) * step := by
      cases Hx' with
      | inbetween_Exact hxeq =>
          have : start + k * step < start + k * step + step := by
            simpa using (add_lt_add_left Hstep (start + k * step))
          simpa [hxeq, add_mul, one_mul, Int.cast_add, Int.cast_ofNat] using this
      | inbetween_Inexact _ hbounds _ => exact hbounds.2
    have hx_lt_mid_avg : x < (start + (start + nb_steps * step)) / 2 :=
      lt_of_lt_of_le hx_lt_step_succ hmid_upper
    -- Rewrite the midpoint in the desired "nb_steps/2" form
    have hmid_eq : (start + (start + nb_steps * step)) / 2 =
        start + (nb_steps / 2 * step) := by
      ring
    have hxlt_final : x < start + (nb_steps / 2 * step) := by
      simpa [hmid_eq] using hx_lt_mid_avg
    -- Conclude the comparison is Ordering.lt for the midpoint
    have hcmp' : compare x (start + (nb_steps / 2 * step)) = Ordering.lt := by
      simp [compare, hxlt_final]
    -- Rewrite to the canonical midpoint `(start + (start + nb_steps * step)) / 2`
    simpa [hmid_eq] using hcmp'

/-- Compute location for high step

    Determines location when in upper half of range
-/
def inbetween_step_Hi_compute : Location :=
  (Location.loc_Inexact Ordering.gt)

/-- Specification: High step location

    Points in upper steps map to greater-than ordering
-/
theorem inbetween_step_Hi (x : ℝ) (k : Int) (l : Location)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x l)
    (Hk1 : nb_steps < 2 * k) (Hk2 : k < nb_steps) (Hstep : 0 < step) :
    ⦃⌜inbetween (start + k * step) (start + (k + 1) * step) x l ∧
      nb_steps < 2 * k ∧ k < nb_steps⌝⦄
    (pure inbetween_step_Hi_compute : Id Location)
    ⦃⇓result => ⌜inbetween start (start + nb_steps * step) x result⌝⦄ := by
  -- Discharge the Hoare triple for a pure computation
  apply Std.Do.Triple.pure (m := Id)
  intro hpre
  rcases hpre with ⟨Hx', hk1, hk2⟩
  -- Return an inexact location with Ordering.gt
  dsimp [inbetween_step_Hi_compute]
  refine inbetween.inbetween_Inexact (l := Ordering.gt) ?hbounds ?hcmp
  · -- Global bounds: start < x < start + nb_steps * step
    -- From hk1 and hk2, deduce 0 < k
    have hkpos : 0 < k := by
      -- k < nb_steps < 2*k ⇒ k < 2*k ⇒ 0 < k
      have hklt2k : k < 2 * k := lt_trans hk2 hk1
      have := sub_lt_sub_right hklt2k k
      simpa [sub_self, two_mul] using this
    -- Convert to real numbers
    have hkposR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
    have hsteppos : 0 < step := Hstep
    -- start < start + k*step
    have hstart_lt_step : start < start + k * step := by
      have hz : 0 < (k : ℝ) * step := mul_pos hkposR hsteppos
      simpa using (add_lt_add_left hz start)
    -- start < x from local inbetween information
    have hx_gt_start : start < x := by
      cases Hx' with
      | inbetween_Exact hxeq => simpa [hxeq] using hstart_lt_step
      | inbetween_Inexact _ hbounds _ =>
          exact lt_trans hstart_lt_step hbounds.1
    -- Upper bound: x < start + nb_steps * step using k+1 ≤ nb_steps
    have hle_succ : k + 1 ≤ nb_steps := Int.add_one_le_iff.mpr hk2
    have hle_succR : (k + 1 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast hle_succ
    have hstep_nonneg : 0 ≤ step := le_of_lt hsteppos
    have hmul_le : (k + 1 : ℝ) * step ≤ (nb_steps : ℝ) * step :=
      mul_le_mul_of_nonneg_right hle_succR hstep_nonneg
    have hx_lt_step_succ : x < start + (k + 1) * step := by
      cases Hx' with
      | inbetween_Exact hxeq =>
          have : start + k * step < start + k * step + step := by
            simpa using (add_lt_add_left hsteppos (start + k * step))
          simpa [hxeq, add_mul, one_mul, Int.cast_add, Int.cast_ofNat] using this
      | inbetween_Inexact _ hbounds _ => exact hbounds.2
    have hx_lt_global : x < start + nb_steps * step := by
      have : start + ((k + 1 : ℝ) * step) ≤ start + (nb_steps : ℝ) * step :=
        add_le_add_right hmul_le start
      exact lt_of_lt_of_le hx_lt_step_succ this
    exact ⟨hx_gt_start, hx_lt_global⟩
  · -- Midpoint comparison: x is strictly greater than the global midpoint
    -- From nb_steps < 2*k and step > 0, derive that
    -- (start + (start + nb_steps*step)) / 2 < start + k*step
    have hsteppos : 0 < step := Hstep
    have h1R : (nb_steps : ℝ) < (2 : ℝ) * (k : ℝ) := by exact_mod_cast hk1
    have hmul : (nb_steps : ℝ) * step < (2 : ℝ) * ((k : ℝ) * step) := by
      -- Multiply by positive `step` on the right
      simpa [mul_assoc] using (mul_lt_mul_of_pos_right h1R hsteppos)
    have hsum : start + (start + nb_steps * step) < 2 * (start + k * step) := by
      -- Rearrange both sides to align with the midpoint expression
      calc
        start + (start + nb_steps * step)
            = start + start + (nb_steps : ℝ) * step := by ring
        _ < start + start + (2 : ℝ) * ((k : ℝ) * step) := by
              exact add_lt_add_right hmul (start + start)
        _ = 2 * (start + k * step) := by ring
    -- Divide the strict inequality by 2 > 0
    have two_pos : 0 < (2 : ℝ) := by norm_num
    have hmid_lt_step : (start + (start + nb_steps * step)) / 2 < start + k * step := by
      -- Multiply by 1/2 instead of dividing, for convenience
      have := mul_lt_mul_of_pos_left hsum (by norm_num : 0 < (1 / 2 : ℝ))
      simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using this
    -- From local inbetween, x > start + k*step
    -- We only need a non-strict inequality `start + k*step ≤ x` to chain with `hmid_lt_step`.
    have hx_ge_step : start + k * step ≤ x := by
      cases Hx' with
      | inbetween_Exact hxeq => simpa [hxeq]
      | inbetween_Inexact _ hbounds _ => exact le_of_lt hbounds.1
    -- Chain inequalities to conclude midpoint < x
    have hmid_lt_x : (start + (start + nb_steps * step)) / 2 < x :=
      lt_of_lt_of_le hmid_lt_step hx_ge_step
    -- Turn this into the required comparison result
    have hcmp_avg : compare x ((start + (start + nb_steps * step)) / 2) = Ordering.gt := by
      simp [compare, not_lt.mpr (le_of_lt hmid_lt_x), hmid_lt_x]
    -- Finally, present the comparison with the canonical midpoint expression
    -- `(start + (start + nb_steps * step)) / 2 = start + (nb_steps / 2 * step)`
    have hmid_eq : (start + (start + nb_steps * step)) / 2 =
        start + (nb_steps / 2 * step) := by ring
    simpa [hmid_eq] using hcmp_avg

/-- New location computation for even steps

    Determines location based on even number of steps
-/
noncomputable def new_location_even (nb_steps k : Int) (l : Location) : Location :=
  -- Use explicit integer inequalities instead of generic `compare` to ease reasoning.
  if hkz : k = 0 then
    match l with
    | Location.loc_Exact => l
    | _ => Location.loc_Inexact Ordering.lt
  else
    if hlt : 2 * k < nb_steps then
      Location.loc_Inexact Ordering.lt
    else if heq : 2 * k = nb_steps then
      match l with
      | Location.loc_Exact => Location.loc_Inexact Ordering.eq
      | _ => Location.loc_Inexact Ordering.gt
    else
      Location.loc_Inexact Ordering.gt

/-- Specification: Even step location is correct

    The computed location for even steps preserves interval properties
-/
theorem new_location_even_correct (He : nb_steps % 2 = 0) (x : ℝ) (k : Int) (l : Location)
    (Hk : 0 ≤ k ∧ k < nb_steps) (Hstep : 0 < step)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x l) :
    ⦃⌜nb_steps % 2 = 0 ∧ 0 ≤ k ∧ k < nb_steps ∧
      inbetween (start + k * step) (start + (k + 1) * step) x l⌝⦄
    (pure (new_location_even nb_steps k l) : Id Location)
    ⦃⇓result => ⌜inbetween start (start + nb_steps * step) x result⌝⦄ := by
  -- Pure computation proof
  apply Std.Do.Triple.pure (m := Id)
  intro hpre
  rcases hpre with ⟨He', hk0, hklt, Hx'⟩
  dsimp [new_location_even]
  by_cases hkz : k = 0
  · -- k = 0 branch
    simp [hkz]
    cases Hx' with
    | inbetween_Exact hxeq =>
        -- Here l is definitionally loc_Exact and the result is `l`.
        have : x = start := by simpa [hkz, add_mul, one_mul] using hxeq
        exact inbetween.inbetween_Exact this
    | inbetween_Inexact _ hbounds _ =>
        -- Result is `loc_Inexact lt`
        refine inbetween.inbetween_Inexact (l := Ordering.lt) ?hb ?hc
        · -- Global bounds
          have hx_gt : start < x := by simpa [hkz, add_mul, one_mul] using hbounds.1
          -- From hklt with k = 0, nb_steps > 0
          have hnbpos : (0 : Int) < nb_steps := by simpa [hkz] using hklt
          have hstep_nonneg : 0 ≤ step := le_of_lt Hstep
          have hx_lt_step : x < start + (1 : ℝ) * step := by
            simpa [hkz, add_mul, one_mul, Int.cast_add, Int.cast_ofNat] using hbounds.2
          have hone_le_nb : (1 : ℝ) ≤ (nb_steps : ℝ) := by
            have : (1 : Int) ≤ nb_steps := Int.add_one_le_iff.mpr hnbpos
            exact_mod_cast this
          have hstep_le : (1 : ℝ) * step ≤ (nb_steps : ℝ) * step :=
            mul_le_mul_of_nonneg_right hone_le_nb hstep_nonneg
          have hx_lt_global : x < start + nb_steps * step :=
            lt_of_lt_of_le hx_lt_step (by simpa [one_mul] using add_le_add_left hstep_le start)
          exact And.intro hx_gt hx_lt_global
        · -- Compare with global midpoint: x < midpoint
          -- From evenness and k=0<nb_steps, we get nb_steps ≥ 2 ⇒ nb_steps/2 ≥ 1.
          have hnbpos : (0 : Int) < nb_steps := by simpa [hkz] using hklt
          have hdecomp2 : 2 * (nb_steps / 2) = nb_steps := by
            -- Standard even decomposition using zero remainder
            have h := Int.mul_ediv_add_emod nb_steps 2
            -- h : 2 * (nb_steps / 2) + nb_steps % 2 = nb_steps
            -- eliminate remainder using He'
            simpa [He'] using h
          -- Show nb_steps / 2 ≥ 1 by contradiction using positivity of nb_steps.
          have hhalf_ge1 : (1 : Int) ≤ nb_steps / 2 := by
            -- From nb_steps > 0 and evenness, we know 2 * (nb_steps / 2) = nb_steps > 0
            have hpos2 : 0 < 2 * (nb_steps / 2) := by
              -- multiply both sides of hdecomp2 by positivity preserves > 0
              simpa [hdecomp2] using hnbpos
            -- If nb_steps / 2 ≤ 0 then 2 * (nb_steps / 2) ≤ 0, contradicting positivity
            have h2nonneg : 0 ≤ (2 : Int) := by decide
            have hpos : 0 < nb_steps / 2 := by
              by_contra hnonpos
              have hmle : nb_steps / 2 ≤ 0 := le_of_not_gt hnonpos
              have hmul_le : 2 * (nb_steps / 2) ≤ 2 * 0 :=
                Int.mul_le_mul_of_nonneg_left hmle h2nonneg
              have hle0 : 2 * (nb_steps / 2) ≤ 0 := by simpa using hmul_le
              -- Contradiction with strict positivity
              exact (not_le_of_gt (by simpa using hpos2)) hle0
            exact Int.add_one_le_iff.mpr hpos
          -- Monotonicity with nonnegative `step` lifts this to reals
          have hstep_nonneg : 0 ≤ step := le_of_lt Hstep
          have hone_le_halfR : (1 : ℝ) ≤ ((nb_steps / 2 : Int) : ℝ) := by exact_mod_cast hhalf_ge1
          have hstep_le : (1 : ℝ) * step ≤ ((nb_steps / 2 : Int) : ℝ) * step :=
            mul_le_mul_of_nonneg_right hone_le_halfR hstep_nonneg
          have hx_lt_step : x < start + (1 : ℝ) * step := by
            simpa [hkz, add_mul, one_mul, Int.cast_add, Int.cast_ofNat] using hbounds.2
          have hx_lt_mid1 : x < start + ((nb_steps / 2 : Int) : ℝ) * step :=
            lt_of_lt_of_le hx_lt_step (by simpa [one_mul] using add_le_add_left hstep_le start)
          -- Normalize the midpoint form and conclude
          have hmid_eq : (start + (start + nb_steps * step)) / 2 =
              start + ((nb_steps / 2 : Int) : ℝ) * step := by
            -- First express the average using a real factor 1/2
            have hbase : (start + (start + nb_steps * step)) / 2 =
                start + ((nb_steps : ℝ) * step) * (1 / 2) := by
              ring
            -- Use evenness to rewrite (nb_steps : ℝ) = 2 * (nb_steps/2)
            have hnb_evenZ : 2 * (nb_steps / 2) = nb_steps := by
              -- Using the standard equality: 2 * (n / 2) + n % 2 = n
              have h := Int.mul_ediv_add_emod nb_steps 2
              -- with He', remainder vanishes, rearrange to remove + 0
              simpa [He'] using h
            have hnb_evenR : (nb_steps : ℝ) = 2 * ((nb_steps / 2 : Int) : ℝ) := by
              -- Cast the integer equality to reals in the desired orientation
              simpa using (congrArg (fun n : Int => (n : ℝ)) hnb_evenZ.symm)
            -- Finish the algebra in ℝ
            calc
              (start + (start + nb_steps * step)) / 2
                  = start + ((nb_steps : ℝ) * step) * (1 / 2) := hbase
              _ = start + ((nb_steps : ℝ) * (1 / 2)) * step := by ring
              _ = start + ((2 * ((nb_steps / 2 : Int) : ℝ)) * (1 / 2)) * step := by
                    simpa [hnb_evenR]
              _ = start + (((2 : ℝ) * (1 / 2)) * ((nb_steps / 2 : Int) : ℝ)) * step := by ring
              _ = start + (1 * ((nb_steps / 2 : Int) : ℝ)) * step := by norm_num
              _ = start + ↑(nb_steps / 2) * step := by simp
          have : compare x (start + ((nb_steps / 2 : Int) : ℝ) * step) = Ordering.lt := by
            have hx_lt_mid' : x < start + ((nb_steps / 2 : Int) : ℝ) * step := by simpa using hx_lt_mid1
            simp [compare, hx_lt_mid']
          simpa [hmid_eq] using this
  · -- k ≠ 0 branch
    have hkpos : 0 < k := lt_of_le_of_ne hk0 (Ne.symm hkz)
    by_cases hlt : 2 * k < nb_steps
    · -- Lower half: result is `loc_Inexact lt`
      -- Reduce the pure computation for this branch
      simp [hkz, hlt]
      -- Strengthen to 2*k + 1 < nb_steps using evenness. Write nb_steps = 2 * n
      have hdecomp : nb_steps = 2 * (nb_steps / 2) := by
        -- From evenness: nb_steps = 2 * (nb_steps / 2)
        -- using `mul_ediv_add_emod` and `He' : nb_steps % 2 = 0`.
        have h := Int.mul_ediv_add_emod nb_steps 2
        -- h: (2 : Int) * (nb_steps / 2) + nb_steps % 2 = nb_steps
        -- eliminate remainder using He'
        have : 2 * (nb_steps / 2) = nb_steps := by
          -- from h and He', rearrange
          -- 2*(nb_steps/2) + 0 = nb_steps ⇒ 2*(nb_steps/2) = nb_steps
          simpa [He'] using h
        -- convert to the desired orientation
        simpa [mul_comm] using this.symm
      have hk_lt_half : k < nb_steps / 2 := by
        -- From 2*k < nb_steps and evenness nb_steps = 2*(nb_steps/2)
        have h2 : 2 * k < nb_steps := hlt
        -- rewrite RHS using equality, avoiding `simp` loops
        -- `nb_steps = 2 * (nb_steps / 2)`
        have : 2 * (nb_steps / 2) = nb_steps := by simpa using hdecomp.symm
        have h2' : 2 * k < 2 * (nb_steps / 2) := by simpa [this]
          using h2
        exact lt_of_mul_lt_mul_left h2' (by decide : (0 : Int) ≤ 2)
      have hk1_le_half : k + 1 ≤ nb_steps / 2 := Int.add_one_le_iff.mpr hk_lt_half
      have h2k1_le_nb : 2 * (k + 1) ≤ nb_steps := by
        -- multiply by 2 on both sides and rewrite using hdecomp
        have hmul : 2 * (k + 1) ≤ 2 * (nb_steps / 2) :=
          Int.mul_le_mul_of_nonneg_left hk1_le_half (by decide : 0 ≤ (2 : Int))
        -- convert the RHS using evenness of nb_steps
        -- `Int.ediv_add_emod` together with `He'` gives `nb_steps = (nb_steps / 2) * 2`.
        -- rewrite to put the factor 2 on the left of the product
        have hdecomp' : 2 * (nb_steps / 2) = nb_steps := by simpa using hdecomp.symm
        simpa [hdecomp'] using hmul
      -- Prove global strict bounds and x left of the global midpoint, as in `inbetween_step_Lo` proof
      refine inbetween.inbetween_Inexact (l := Ordering.lt) ?hb1 ?hc1
      · -- Bounds: start < x < start + nb_steps * step
        -- start < start + k*step since k > 0 and step > 0
        have hkposR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
        have hz : 0 < (k : ℝ) * step := mul_pos hkposR Hstep
        have hpos_add : start < start + (k * step) := by simpa using (add_lt_add_left hz start)
        -- Deduce start < x from the step-local location `Hx'`.
        have hx_gt_start : start < x := by
          cases Hx' with
          | inbetween_Exact hxeq => simpa [hxeq] using hpos_add
          | inbetween_Inexact _ hbounds _ => exact lt_trans hpos_add hbounds.1
        -- For the global upper bound, use k + 1 ≤ nb_steps
        -- From k < nb_steps we have k+1 ≤ nb_steps
        have hle_succ : k + 1 ≤ nb_steps := Int.add_one_le_iff.mpr hklt
        have hle_succR : (k + 1 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast hle_succ
        have hmul_le : (k + 1 : ℝ) * step ≤ (nb_steps : ℝ) * step :=
          mul_le_mul_of_nonneg_right hle_succR (le_of_lt Hstep)
        have hx_lt_step_succ : x < start + (k + 1) * step := by
          cases Hx' with
          | inbetween_Exact hxeq =>
              have : start + k * step < start + k * step + step := by
                simpa using (add_lt_add_left Hstep (start + k * step))
              simpa [hxeq, add_mul, one_mul, Int.cast_add, Int.cast_ofNat] using this
          | inbetween_Inexact _ hbounds _ => exact hbounds.2
        have hx_lt_global : x < start + nb_steps * step := by
          have : start + ((k + 1 : ℝ) * step) ≤ start + (nb_steps : ℝ) * step :=
            add_le_add_right hmul_le start
          exact lt_of_lt_of_le hx_lt_step_succ this
        exact And.intro hx_gt_start hx_lt_global
      · -- Midpoint comparison: x is strictly less than the global midpoint
        -- From h2k1_le_nb and step > 0, derive start + (k+1)*step ≤ midpoint
        have two_pos : 0 < (2 : ℝ) := by norm_num
        have h2leR : (2 : ℝ) * ((k + 1 : ℝ)) ≤ (nb_steps : ℝ) := by
          exact_mod_cast h2k1_le_nb
        have hmul : (2 : ℝ) * ((k + 1 : ℝ) * step) ≤ (nb_steps : ℝ) * step := by
          simpa [mul_assoc] using (mul_le_mul_of_nonneg_right h2leR (le_of_lt Hstep))
        have h2 : 2 * (start + (k + 1) * step) ≤ start + (start + nb_steps * step) := by
          calc
            2 * (start + (k + 1) * step) = 2 * start + 2 * ((k + 1 : ℝ) * step) := by ring
            _ ≤ 2 * start + (nb_steps : ℝ) * step := by exact add_le_add_right hmul (2 * start)
            _ = start + (start + nb_steps * step) := by ring
        -- Use the form produced by `le_div_iff₀` to avoid reordering mismatches
        have hmid_upper' : start + step * (k + 1) ≤ (start + (start + step * (nb_steps : ℝ))) / 2 := by
          have hdiv := (le_div_iff₀ two_pos).mpr (by simpa [mul_comm] using h2)
          simpa using hdiv
        have hx_lt_step_succ : x < start + (k + 1) * step := by
          cases Hx' with
          | inbetween_Exact hxeq =>
              have : start + k * step < start + k * step + step := by
                simpa using (add_lt_add_left Hstep (start + k * step))
              simpa [hxeq, add_mul, one_mul, Int.cast_add, Int.cast_ofNat] using this
          | inbetween_Inexact _ hbounds _ => exact hbounds.2
        -- Align `hx_lt_step_succ` to the same multiplication order as `hmid_upper'`
        have hx_lt_step_succ' : x < start + step * (k + 1) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hx_lt_step_succ
        have hx_lt_mid_avg : x < (start + (start + nb_steps * step)) / 2 := by
          -- also align the RHS form
          have : (start + (start + nb_steps * step)) = (start + (start + step * (nb_steps : ℝ))) := by ring
          simpa [this] using (lt_of_lt_of_le hx_lt_step_succ' hmid_upper')
        -- Normalize the midpoint form and conclude via the definition of `compare`
        have hmid_eq : (start + (start + nb_steps * step)) / 2 = start + (nb_steps / 2 * step) := by ring
        have : compare x ((start + (start + nb_steps * step)) / 2) = Ordering.lt := by
          classical
          simpa [compare, hx_lt_mid_avg]
        simpa [hmid_eq] using this
    · have hgt_or_eq : nb_steps ≤ 2 * k := le_of_not_lt hlt
      by_cases heq : 2 * k = nb_steps
      · -- Middle case: result depends on local exactness
        simp [hkz, hlt, heq]
        -- Midpoint identity using `heq : 2*k = nb_steps` (cast to ℝ).
        have heqR : (nb_steps : ℝ) = (2 : ℝ) * (k : ℝ) := by exact_mod_cast heq.symm
        have hmid_eqR : (start + (start + nb_steps * step)) / 2 = start + k * step := by
          calc
            (start + (start + nb_steps * step)) / 2
                = (start + (start + ((nb_steps : ℝ) * step))) / 2 := by simp
            _   = (start + (start + ((2 : ℝ) * (k : ℝ) * step))) / 2 := by
                    simpa [heqR]
            _   = start + k * step := by ring
        -- Bounds helpers common to both subcases
        have hx_ge_left : start + k * step ≤ x := by
          cases Hx' with
          | inbetween_Exact hxeq => simpa [hxeq]
          | inbetween_Inexact _ hbounds _ => exact le_of_lt hbounds.1
        have hx_gt_start : start < x := by
          -- k ≠ 0 and step > 0 ⇒ start < start + k*step ≤ x
          have hkposR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
          have : start < start + k * step := by
            have : 0 < (k : ℝ) * step := mul_pos hkposR Hstep
            simpa using (add_lt_add_left this start)
          exact lt_of_lt_of_le this hx_ge_left
        -- Subcases by local exactness
        cases Hx' with
        | inbetween_Exact hxeq =>
            -- Result is eq
            refine inbetween.inbetween_Inexact (l := Ordering.eq) ?hb2 ?hc2
            · -- Global upper bound from hklt
              have hkltR : (k : ℝ) < (nb_steps : ℝ) := by exact_mod_cast hklt
              have hx_lt_global : x < start + nb_steps * step := by
                have : start + k * step < start + (nb_steps : ℝ) * step := by
                  simpa [mul_comm, mul_left_comm, mul_assoc] using add_lt_add_left (mul_lt_mul_of_pos_right hkltR Hstep) start
                simpa [hxeq] using this
              exact And.intro hx_gt_start hx_lt_global
            · -- x equals the midpoint
              have : x = start + k * step := hxeq
              have : x = (start + (start + nb_steps * step)) / 2 := by simpa [hmid_eqR]
                using this
              simp [compare, this]
        | inbetween_Inexact _ hbounds _ =>
            -- Result is gt
            refine inbetween.inbetween_Inexact (l := Ordering.gt) ?hb3 ?hc3
            · -- Use x < start + (k+1)*step and (k+1) ≤ nb_steps
              have hle_succ : k + 1 ≤ nb_steps := Int.add_one_le_iff.mpr hklt
              have hle_succR : (k + 1 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast hle_succ
              have hmul_le : (k + 1 : ℝ) * step ≤ (nb_steps : ℝ) * step :=
                mul_le_mul_of_nonneg_right hle_succR (le_of_lt Hstep)
              have hx_lt_step_succ : x < start + (k + 1) * step := hbounds.2
              have hx_lt_global : x < start + nb_steps * step := by
                have : start + ((k + 1 : ℝ) * step) ≤ start + (nb_steps : ℝ) * step :=
                  add_le_add_right hmul_le start
                exact lt_of_lt_of_le hx_lt_step_succ this
              exact And.intro hx_gt_start hx_lt_global
            · -- x strictly greater than the midpoint (which equals start + k*step)
              have hx_gt_step : start + k * step < x := hbounds.1
              have : (start + (start + nb_steps * step)) / 2 < x := by
                simpa [hmid_eqR] using hx_gt_step
              simp [compare, not_lt.mpr (le_of_lt this), this]
      · -- Greater than: result is `loc_Inexact gt`
        have hgt : nb_steps < 2 * k := lt_of_le_of_ne hgt_or_eq (Ne.symm heq)
        simp [hkz, hlt, heq, hgt]
        -- Prove global strict bounds and x right of the global midpoint, as in `inbetween_step_Hi` proof
        refine inbetween.inbetween_Inexact (l := Ordering.gt) ?hb4 ?hc4
        · -- Bounds
          -- From hklt and hkpos, start < x as before
          have hkposR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
          have hstart_lt_step : start < start + k * step := by
            have : 0 < (k : ℝ) * step := mul_pos hkposR Hstep
            simpa using (add_lt_add_left this start)
          have hx_gt_start : start < x := by
            cases Hx' with
            | inbetween_Exact hxeq => simpa [hxeq] using hstart_lt_step
            | inbetween_Inexact _ hbounds _ => exact lt_trans hstart_lt_step hbounds.1
          -- Upper bound from k+1 ≤ nb_steps
          have hle_succ : k + 1 ≤ nb_steps := Int.add_one_le_iff.mpr hklt
          have hle_succR : (k + 1 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast hle_succ
          have hmul_le : (k + 1 : ℝ) * step ≤ (nb_steps : ℝ) * step :=
            mul_le_mul_of_nonneg_right hle_succR (le_of_lt Hstep)
          have hx_lt_step_succ : x < start + (k + 1) * step := by
            cases Hx' with
            | inbetween_Exact hxeq =>
                have : start + k * step < start + k * step + step := by
                  simpa using (add_lt_add_left Hstep (start + k * step))
                simpa [hxeq, add_mul, one_mul, Int.cast_add, Int.cast_ofNat] using this
            | inbetween_Inexact _ hbounds _ => exact hbounds.2
          have hx_lt_global : x < start + nb_steps * step := by
            have : start + ((k + 1 : ℝ) * step) ≤ start + (nb_steps : ℝ) * step :=
              add_le_add_right hmul_le start
            exact lt_of_lt_of_le hx_lt_step_succ this
          exact And.intro hx_gt_start hx_lt_global
        · -- Midpoint comparison: x strictly greater than midpoint
          have h1R : (nb_steps : ℝ) < (2 : ℝ) * (k : ℝ) := by exact_mod_cast hgt
          have hmul : (nb_steps : ℝ) * step < (2 : ℝ) * ((k : ℝ) * step) := by
            simpa [mul_assoc] using (mul_lt_mul_of_pos_right h1R Hstep)
          have hsum : start + (start + nb_steps * step) < 2 * (start + k * step) := by
            calc
              start + (start + nb_steps * step) = start + start + (nb_steps : ℝ) * step := by ring
              _ < start + start + (2 : ℝ) * ((k : ℝ) * step) := by exact add_lt_add_right hmul (start + start)
              _ = 2 * (start + k * step) := by ring
          have two_pos : 0 < (2 : ℝ) := by norm_num
          have hmid_lt_step : (start + (start + nb_steps * step)) / 2 < start + k * step := by
            have := mul_lt_mul_of_pos_left hsum (by norm_num : 0 < (1 / 2 : ℝ))
            simpa [one_div, mul_comm, mul_left_comm, mul_assoc]
          -- From local inbetween, start + k*step ≤ x
          have hx_ge_step : start + k * step ≤ x := by
            cases Hx' with
            | inbetween_Exact hxeq => simpa [hxeq]
            | inbetween_Inexact _ hbounds _ => exact le_of_lt hbounds.1
          have hmid_lt_x : (start + (start + nb_steps * step)) / 2 < x := lt_of_lt_of_le hmid_lt_step hx_ge_step
          have hcmp_avg : compare x ((start + (start + nb_steps * step)) / 2) = Ordering.gt := by
            simp [compare, not_lt.mpr (le_of_lt hmid_lt_x), hmid_lt_x]
          have hmid_eq : (start + (start + nb_steps * step)) / 2 = start + (nb_steps / 2 * step) := by ring
          simpa [hmid_eq] using hcmp_avg

/-- New location computation for odd steps

    Determines location based on odd number of steps
-/
noncomputable def new_location_odd (nb_steps k : Int) (l : Location) : Location :=
  -- Use explicit integer comparisons instead of a generic `compare` to ease reasoning.
  if hkz : k = 0 then
    match l with
    | Location.loc_Exact => l
    | Location.loc_Inexact ord =>
        if nb_steps = 1 then Location.loc_Inexact ord
        else Location.loc_Inexact Ordering.lt
  else
    if hlt : 2 * k + 1 < nb_steps then
      Location.loc_Inexact Ordering.lt
    else if heq : 2 * k + 1 = nb_steps then
      match l with
      | Location.loc_Inexact ord => Location.loc_Inexact ord
      | Location.loc_Exact => Location.loc_Inexact Ordering.lt
    else
      Location.loc_Inexact Ordering.gt

/-- Specification: Odd step location is correct

    The computed location for odd steps preserves interval properties
-/
theorem new_location_odd_correct (Ho : nb_steps % 2 = 1) (x : ℝ) (k : Int) (l : Location)
    (Hk : 0 ≤ k ∧ k < nb_steps) (Hstep : 0 < step)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x l) :
    ⦃⌜nb_steps % 2 = 1 ∧ 0 ≤ k ∧ k < nb_steps ∧
      inbetween (start + k * step) (start + (k + 1) * step) x l⌝⦄
    (pure (new_location_odd nb_steps k l) : Id Location)
    ⦃⇓result => ⌜inbetween start (start + nb_steps * step) x result⌝⦄ := by
  -- Pure computation proof
  apply Std.Do.Triple.pure (m := Id)
  intro hpre
  rcases hpre with ⟨Ho', hk0, hklt, Hx'⟩
  dsimp [new_location_odd]
  -- Use section-level `Hstep` for monotonicity/strictness
  have hstep_pos : 0 < step := Hstep
  have hstep_nonneg : 0 ≤ step := le_of_lt hstep_pos
  by_cases hkz : k = 0
  · -- k = 0 branch
    simp [hkz]
    -- From hklt with k=0, nb_steps > 0
    have hnbpos : (0 : Int) < nb_steps := by simpa [hkz] using hklt
    cases Hx' with
    | inbetween_Exact hxeq =>
        -- Result equals `l = loc_Exact`, show x = start
        have : x = start := by simpa [hkz, add_mul, one_mul] using hxeq
        exact inbetween.inbetween_Exact this
    | inbetween_Inexact ord hbounds hcmp =>
        -- Two subcases on nb_steps = 1 or nb_steps ≥ 3 (since odd and > 0)
        by_cases hnb1 : nb_steps = 1
        · -- Preserve local ordering when the whole range is a single step
          simp [hnb1]
          -- Bounds: start < x < start + nb_steps * step (here nb_steps = 1)
          have hx_gt : start < x := by
            simpa [hkz, add_mul, one_mul] using hbounds.1
          have hx_lt_step : x < start + step := by
            -- Upper bound from the local step interval with k = 0
            simpa [hkz, add_mul, one_mul, Int.cast_add, Int.cast_ofNat] using hbounds.2
          have hx_lt_global : x < start + nb_steps * step := by
            simpa [hnb1, one_mul, Int.cast_one] using hx_lt_step
          -- Midpoint: global midpoint equals the local-step midpoint under k = 0 and nb_steps = 1
          have hmid_eq_glob :
              (start + (start + nb_steps * step)) / 2 =
              (start + (start + (k + 1) * step)) / 2 := by
            simp [hnb1, hkz, add_mul, one_mul, Int.cast_add, Int.cast_ofNat, Int.cast_one]
          have hcmp_glob : compare x ((start + (start + nb_steps * step)) / 2) = ord := by
            -- Rewrite the comparison from the local-step midpoint form to the global midpoint
            have : compare x ((start + (start + (k + 1) * step)) / 2) = ord := by
              -- From local inbetween midpoint
              have hmid_eq_local :
                  (start + (start + (k + 1) * step)) / 2 =
                  (start + k * step + (start + (k + 1) * step)) / 2 := by
                simp [hkz, add_assoc, add_comm, add_left_comm]
              simpa [hmid_eq_local] using hcmp
            simpa [hmid_eq_glob] using this
          -- Goal simplifies with nb_steps = 1, so rewrite the midpoint accordingly
          exact inbetween.inbetween_Inexact (l := ord)
            ⟨hx_gt, by simpa [hnb1, one_mul, Int.cast_one] using hx_lt_step⟩
            (by simpa [hnb1, one_mul, Int.cast_one] using hcmp_glob)
        · -- nb_steps ≠ 1 and positive ⇒ 2 ≤ nb_steps
          have hone_le_nb : (1 : Int) ≤ nb_steps := Int.add_one_le_iff.mpr hnbpos
          have h1lt : (1 : Int) < nb_steps := lt_of_le_of_ne hone_le_nb (Ne.symm hnb1)
          have htwo_le_nb : (2 : Int) ≤ nb_steps := Int.add_one_le_iff.mpr h1lt
          -- Local upper bound gives x < start + step
          have hx_lt_step : x < start + (1 : ℝ) * step := by
            simpa [hkz, add_mul, one_mul, Int.cast_add, Int.cast_ofNat] using hbounds.2
          -- Show start + step ≤ global midpoint using 2*step ≤ nb_steps*step
          have htwo_le_nbR : (2 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast htwo_le_nb
          have hstep_le : (2 : ℝ) * step ≤ (nb_steps : ℝ) * step :=
            mul_le_mul_of_nonneg_right htwo_le_nbR hstep_nonneg
          have hsum_le : 2 * (start + (1 : ℝ) * step) ≤ start + (start + nb_steps * step) := by
            -- Rearrange target inequality by multiplying both sides by 2 > 0
            -- Start from `2*step ≤ nb_steps*step` and add `2*start` to both sides.
            have : 2 * start + 2 * ((1 : ℝ) * step) ≤ 2 * start + (nb_steps : ℝ) * step := by
              simpa [two_mul] using add_le_add_left hstep_le (2 * start)
            -- Now fold back the left-hand side into `2*(start + 1*step)`
            simpa [two_mul, one_mul, add_left_comm, add_assoc] using this
          have hx_lt_mid : x < (start + (start + nb_steps * step)) / 2 := by
            have := (mul_le_mul_of_nonneg_left hsum_le (by norm_num : 0 ≤ (1 / 2 : ℝ)))
            have hmid_ge_step : start + (1 : ℝ) * step ≤ (start + (start + nb_steps * step)) / 2 := by
              simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using this
            exact lt_of_lt_of_le hx_lt_step hmid_ge_step
          -- Comparison and global bounds
          have hcmp : compare x ((start + (start + nb_steps * step)) / 2) = Ordering.lt := by
            simp [compare, hx_lt_mid]
          have hx_gt_start : start < x := by simpa [hkz, add_mul, one_mul] using hbounds.1
          have hone_le_nbR : (1 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast hone_le_nb
          have hstep_le1 : (1 : ℝ) * step ≤ (nb_steps : ℝ) * step :=
            mul_le_mul_of_nonneg_right hone_le_nbR hstep_nonneg
          have hx_lt_global : x < start + nb_steps * step :=
            lt_of_lt_of_le hx_lt_step (by simpa [one_mul] using add_le_add_left hstep_le1 start)
          have hres : inbetween start (start + nb_steps * step) x (Location.loc_Inexact Ordering.lt) :=
            inbetween.inbetween_Inexact (l := Ordering.lt)
              ⟨hx_gt_start, hx_lt_global⟩ hcmp
          -- The function returns `loc_Inexact lt` when `k = 0`, `l` inexact, and `nb_steps ≠ 1`.
          simpa [new_location_odd, hkz, hnb1]
            using hres
  · -- k ≠ 0 branch
    have hkpos : 0 < k := lt_of_le_of_ne hk0 (Ne.symm hkz)
    -- Decide by comparison of 2*k + 1 with nb_steps
    -- Work on the real-valued comparison to extract inequalities/equalities.
    set c := compare ((2 : ℝ) * (k : ℝ) + 1) (nb_steps : ℝ) with hc
    cases hcmp : compare (2 * k + 1) nb_steps with
    | lt =>
        -- Result is lt; show x left of global midpoint
        -- From integer comparison, also have the real comparison is lt
        have hcmpR : compare ((2 : ℝ) * (k : ℝ) + 1) (nb_steps : ℝ) = Ordering.lt := by
          -- Cast the integer comparison to reals
          simpa [two_mul, Int.cast_add, Int.cast_mul, Int.cast_ofNat] using hcmp
        -- Integer inequality form and simplify the program's computed result
        have h2k1 : 2 * k + 1 < nb_steps := by
          have : (2 * (k : ℝ) + 1 : ℝ) < (nb_steps : ℝ) :=
            compare_eq_lt_real (a := (2 * (k : ℝ) + 1)) (b := (nb_steps : ℝ))
              (by simpa [two_mul, Int.cast_add, Int.cast_mul, Int.cast_ofNat] using hcmp)
          exact_mod_cast this
        -- We will later show global bounds and the midpoint comparison implies `lt`.
        -- After establishing bounds below, we will conclude by simplifying the program branch
        -- that selects `Location.loc_Inexact Ordering.lt` under `2*k+1 < nb_steps`.
        -- Use integer inequality to derive k + 1 ≤ nb_steps / 2 (for odd nb_steps)
        -- We can mimic the argument from `inbetween_step_Lo` to show x < midpoint
        -- First, obtain an upper bound towards (k+1) ≤ nb_steps
        have hk1le : k + 1 ≤ nb_steps := by
          -- From `k < nb_steps` we have `k + 1 ≤ nb_steps`
          exact Int.add_one_le_iff.mpr hklt
        -- From local upper bound x < start + (k+1)*step and monotonicity, get x < global midpoint
        have hx_lt_step_succ : x < start + (k + 1) * step := by
          cases Hx' with
          | inbetween_Exact hxeq =>
              have : start + k * step < start + k * step + step := by
                simpa using (add_lt_add_left hstep_pos (start + k * step))
              simpa [hxeq, add_mul, one_mul, Int.cast_add, Int.cast_ofNat] using this
          | inbetween_Inexact _ hbounds _ => exact hbounds.2
        -- Show midpoint lies ≥ start + (k+1)*step using nb_steps odd and (2*k+1) < nb_steps
        -- Average form equality
        have hmid_eq : (start + (start + nb_steps * step)) / 2
              = start + ((nb_steps : ℝ) * step) * (1 / 2) := by ring
        -- Using step positivity and integer inequality, we can bound
        have hle_nb : (k + 1 : ℝ) ≤ (nb_steps : ℝ) / 2 := by
          -- From `2*k + 1 < nb_steps`, we get `2*(k+1) ≤ nb_steps` on integers
          have hk1 : 2 * (k + 1) ≤ nb_steps := by
            have : 2 * k + 1 < nb_steps := h2k1
            have hk1' : 2 * k + 1 + 1 ≤ nb_steps := Int.add_one_le_iff.mpr this
            -- Normalize to `2*(k+1)`
            simpa [two_mul, add_comm, add_left_comm, add_assoc] using hk1'
          -- Cast to reals and divide both sides by 2 using multiplication by 1/2 ≥ 0
          have htwo_leR : (2 : ℝ) * (k + 1 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast hk1
          have hmul := mul_le_mul_of_nonneg_left htwo_leR (by norm_num : 0 ≤ (1 / 2 : ℝ))
          -- Simplify `(1/2)*((2)*(k+1))` to `k+1` and `(1/2)*nb_steps` to `nb_steps/2`
          simpa [one_div, mul_assoc, mul_left_comm, mul_comm] using hmul
        have hx_lt_mid : x < (start + (start + nb_steps * step)) / 2 := by
          -- start + (k+1)*step ≤ start + ((nb_steps : ℝ)/2)*step ≤ midpoint in `hmid_eq` form
          have hmul_le : (k + 1 : ℝ) * step ≤ ((nb_steps : ℝ) / 2) * step :=
            mul_le_mul_of_nonneg_right hle_nb hstep_nonneg
          have : start + (k + 1 : ℝ) * step ≤ start + ((nb_steps : ℝ) / 2) * step :=
            add_le_add_right hmul_le start
          -- And ((nb_steps:ℝ)/2)*step ≤ midpoint since midpoint = start + ((nb_steps:ℝ)*step)/2
          have hmid_alt : (start + (start + nb_steps * step)) / 2 =
              start + ((nb_steps : ℝ) / 2) * step := by ring
          exact lt_of_lt_of_le hx_lt_step_succ (by simpa [hmid_alt] using this)
        have hcmp : compare x ((start + (start + nb_steps * step)) / 2) = Ordering.lt := by
          simp [compare, hx_lt_mid]
        -- Global bounds
        have hkposR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
        have hstart_lt_step : start < start + k * step := by
          have : 0 < (k : ℝ) * step := mul_pos hkposR hstep_pos
          simpa using (add_lt_add_left this start)
        have hx_gt_start : start < x := by
          cases Hx' with
          | inbetween_Exact hxeq => simpa [hxeq] using hstart_lt_step
          | inbetween_Inexact _ hbounds _ => exact lt_trans hstart_lt_step hbounds.1
        have hle_succ : k + 1 ≤ nb_steps := Int.add_one_le_iff.mpr hklt
        have hle_succR : (k + 1 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast hle_succ
        have hmul_le' : (k + 1 : ℝ) * step ≤ (nb_steps : ℝ) * step :=
          mul_le_mul_of_nonneg_right hle_succR hstep_nonneg
        have hx_lt_global : x < start + nb_steps * step := by
          have : start + ((k + 1 : ℝ) * step) ≤ start + (nb_steps : ℝ) * step :=
            add_le_add_right hmul_le' start
          exact lt_of_lt_of_le hx_lt_step_succ this
        -- Conclude, matching the computed program result for this branch
        simpa [new_location_odd, hkz, h2k1]
          using (inbetween.inbetween_Inexact (l := Ordering.lt)
            ⟨hx_gt_start, hx_lt_global⟩ hcmp)
    | eq =>
        -- Result depends on `l`: preserve local ordering if inexact; otherwise `lt`
        -- For the equality case, the real comparison is also eq
        have hcmpR : compare ((2 : ℝ) * (k : ℝ) + 1) (nb_steps : ℝ) = Ordering.eq := by
          simpa [Int.cast_add, Int.cast_mul, Int.cast_ofNat] using hcmp
        -- Simplify the computed result for this branch
        have heqR' : (2 : ℝ) * (k : ℝ) + 1 = (nb_steps : ℝ) :=
          compare_eq_eq_real (a := (2 : ℝ) * (k : ℝ) + 1) (b := (nb_steps : ℝ)) hcmpR
        have heq : 2 * k + 1 = nb_steps := by
          have heqRcast : ((2 * k + 1 : Int) : ℝ) = (nb_steps : ℝ) := by
            simpa [Int.cast_add, Int.cast_mul, Int.cast_ofNat] using heqR'
          exact_mod_cast heqRcast
        have hlt_false : ¬ (2 * k + 1 < nb_steps) := by
          simpa [heq] using (lt_irrefl (2 * k + 1))
        simp [new_location_odd, hkz, hlt_false, heq]
        -- Extract equalities from the real comparison equality
        -- First as a real equality in the convenient algebraic form
        have heqR' : (2 : ℝ) * (k : ℝ) + 1 = (nb_steps : ℝ) :=
          compare_eq_eq_real (a := (2 : ℝ) * (k : ℝ) + 1) (b := (nb_steps : ℝ)) hcmpR
        -- Also as an integer equality for later monotonicity arguments (reuse `heq` above)
        -- Midpoint equality: global midpoint equals local step midpoint
        have hmid_eq : (start + (start + nb_steps * step)) / 2
              = ((start + k * step) + (start + (k + 1) * step)) / 2 := by
          -- Rewrite `nb_steps` using `2*k + 1` and simplify
          have : (nb_steps : ℝ) = (2 : ℝ) * (k : ℝ) + 1 := by simpa using heqR'.symm
          calc
            (start + (start + nb_steps * step)) / 2
                = (start + (start + (((2 : ℝ) * (k : ℝ) + 1) * step))) / 2 := by simpa [this]
            _ = (start + (start + ((2 : ℝ) * (k : ℝ)) * step + (1 : ℝ) * step)) / 2 := by ring
            _ = ((start + k * step) + (start + (k + 1) * step)) / 2 := by ring
        -- Prove per form of `l`
        cases Hx' with
        | inbetween_Exact hxeq =>
            -- x = start + k*step is strictly less than the step midpoint,
            -- which coincides with the global midpoint in this branch.
            have hx_lt_mid : x < (start + (start + nb_steps * step)) / 2 := by
              -- Show `a < (a+b)/2` for `a = start + k*step` and `b = start + (k+1)*step`.
              have hlt : start + k * step < start + (k + 1) * step := by
                have : start + k * step < start + k * step + step := by
                  simpa using (add_lt_add_left hstep_pos (start + k * step))
                simpa [add_mul, one_mul, Int.cast_add, Int.cast_ofNat] using this
              have : 2 * (start + k * step) < (start + k * step) + (start + (k + 1) * step) := by
                simpa [two_mul] using add_lt_add_left hlt (start + k * step)
              have := (mul_lt_mul_of_pos_left this (by norm_num : 0 < (1 / 2 : ℝ)))
              have : start + k * step < (start + k * step + (start + (k + 1) * step)) / 2 := by
                simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using this
              -- Rewrite with `x` and the global midpoint equality.
              simpa [hxeq, hmid_eq]
            -- Also record the local upper bound to lift to global later
            have hx_lt_step_succ : x < start + (k + 1) * step := by
              have : start + k * step < start + k * step + step := by
                simpa using (add_lt_add_left hstep_pos (start + k * step))
              simpa [hxeq, add_mul, one_mul, Int.cast_add, Int.cast_ofNat] using this
            have hcmp : compare x ((start + (start + nb_steps * step)) / 2) = Ordering.lt := by
              simp [compare, hx_lt_mid]
            -- Global bounds as usual
            have hkposR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
            have hstart_lt_step : start < start + k * step := by
              have : 0 < (k : ℝ) * step := mul_pos hkposR hstep_pos
              simpa using (add_lt_add_left this start)
            have hx_gt_start : start < x := by simpa [hxeq] using hstart_lt_step
            have hle_succ : k + 1 ≤ nb_steps := by
              -- From `heq : 2*k + 1 = nb_steps` and `0 ≤ k`, we get `k+1 ≤ 2*k+1 = nb_steps`.
              have hk0le : 0 ≤ k := le_of_lt hkpos
              have hk_le_2k : k ≤ 2 * k := by
                have : (1 : Int) ≤ 2 := by decide
                simpa [one_mul] using (Int.mul_le_mul_of_nonneg_right this hk0le)
              have : k + 1 ≤ 2 * k + 1 := add_le_add_left hk_le_2k 1
              simpa [heq] using this
            have hle_succR : (k + 1 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast hle_succ
            have hmul_le : (k + 1 : ℝ) * step ≤ (nb_steps : ℝ) * step :=
              mul_le_mul_of_nonneg_right hle_succR hstep_nonneg
            have hx_lt_global : x < start + nb_steps * step := by
              have hle : start + ((k + 1 : ℝ) * step) ≤ start + (nb_steps : ℝ) * step :=
                add_le_add_right hmul_le start
              exact lt_of_lt_of_le (by simpa [hxeq] using hx_lt_step_succ) hle
            -- Evaluate the program in this branch: `¬ (2*k+1 < nb_steps)` and `2*k+1 = nb_steps`.
            have hlt_false : ¬ (2 * k + 1 < nb_steps) := by
              simpa [heq] using (lt_irrefl (2 * k + 1))
            -- Now simplify the computed location and conclude.
            simpa [new_location_odd, hkz, hlt_false, heq] using
              (inbetween.inbetween_Inexact (l := Ordering.lt)
                ⟨hx_gt_start, hx_lt_global⟩ hcmp)
        | inbetween_Inexact ord hbounds hcmp_local =>
            -- Local and global midpoints coincide; preserve `ord`
            have hcmp' : compare x ((start + (start + nb_steps * step)) / 2) = ord := by
              -- Local midpoint equals global midpoint in this branch
              have hmid_eq' : (start + (start + nb_steps * step)) / 2
                    = ((start + k * step) + (start + (k + 1) * step)) / 2 := by
                -- Same algebra as above
                have : (nb_steps : ℝ) = (2 : ℝ) * (k : ℝ) + 1 := by
                  -- Cast `heq : 2*k + 1 = nb_steps` to reals in the right orientation
                  have hR : ((2 * k + 1 : Int) : ℝ) = (nb_steps : ℝ) := by
                    simpa [Int.cast_add, Int.cast_mul, Int.cast_ofNat] using
                      congrArg (fun z : Int => (z : ℝ)) heq
                  -- Reassociating matches `(2:ℝ)*(k:ℝ) + 1`
                  simpa [two_mul] using hR.symm
                calc
                  (start + (start + nb_steps * step)) / 2
                      = (start + (start + (((2 : ℝ) * (k : ℝ) + 1) * step))) / 2 := by
                          simpa [this]
                  _ = (start + (start + ((2 : ℝ) * (k : ℝ)) * step + (1 : ℝ) * step)) / 2 := by
                          ring
                  _ = ((start + k * step) + (start + (k + 1) * step)) / 2 := by
                          ring
              simpa [hmid_eq'] using hcmp_local
            -- Bounds
            have hkposR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
            have hstart_lt_step : start < start + k * step := by
              have : 0 < (k : ℝ) * step := mul_pos hkposR hstep_pos
              simpa using (add_lt_add_left this start)
            -- Lower bound from local interval
            have hx_gt_start : start < x := by
              -- In this branch, we already have strict local bounds `hbounds`.
              -- Combine `start < start + k*step` with `start + k*step < x`.
              exact lt_trans hstart_lt_step hbounds.1
            have hle_succ : k + 1 ≤ nb_steps := by
              -- From `heq : 2*k + 1 = nb_steps` and `0 ≤ k`, we get `k+1 ≤ 2*k+1`.
              have hk0le : 0 ≤ k := le_of_lt hkpos
              have hk_le_2k : k ≤ 2 * k := by
                -- Multiply the inequality `1 ≤ 2` by the nonnegative `k` on the right.
                have : (1 : Int) ≤ 2 := by decide
                simpa [one_mul] using (mul_le_mul_of_nonneg_right this hk0le)
              have : k + 1 ≤ 2 * k + 1 := add_le_add_left hk_le_2k 1
              simpa [heq] using this
            have hle_succR : (k + 1 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast hle_succ
            have hmul_le : (k + 1 : ℝ) * step ≤ (nb_steps : ℝ) * step :=
              mul_le_mul_of_nonneg_right hle_succR hstep_nonneg
            have hx_lt_step_succ : x < start + (k + 1) * step := by
              -- Directly from the local strict upper bound `hbounds.2`.
              exact hbounds.2
            have hx_lt_global : x < start + nb_steps * step := by
              have : start + ((k + 1 : ℝ) * step) ≤ start + (nb_steps : ℝ) * step :=
                add_le_add_right hmul_le start
              exact lt_of_lt_of_le hx_lt_step_succ this
            -- Evaluate the program in this branch: `¬ (2*k+1 < nb_steps)` and `2*k+1 = nb_steps`.
            have hlt_false : ¬ (2 * k + 1 < nb_steps) := by
              simpa [heq] using (lt_irrefl (2 * k + 1))
            -- Now simplify the computed location and conclude.
            simpa [new_location_odd, hkz, hlt_false, heq] using
              (inbetween.inbetween_Inexact (l := ord)
                ⟨hx_gt_start, hx_lt_global⟩ hcmp')
    | gt =>
        -- Result is gt; mirror `inbetween_step_Hi` reasoning
        -- From `¬ (2*k+1 < nb_steps)` and `¬ (2*k+1 = nb_steps)`, derive `nb_steps < 2*k+1`.
        have hle2k1 : nb_steps ≤ 2 * k + 1 := by
          -- From `hcmp : compare (2*k+1) nb_steps = gt`, get the real inequality
          have hcmpR :
              compare ((2 : ℝ) * (k : ℝ) + 1) (nb_steps : ℝ) = Ordering.gt := by
            simpa [two_mul, Int.cast_add, Int.cast_mul, Int.cast_ofNat] using hcmp
          have hltR : (nb_steps : ℝ) < ((2 : ℝ) * (k : ℝ) + 1) :=
            compare_eq_gt_real (a := ((2 : ℝ) * (k : ℝ) + 1)) (b := (nb_steps : ℝ)) hcmpR
          -- Cast back to integers and weaken to `≤`
          have : nb_steps < 2 * k + 1 := by exact_mod_cast hltR
          exact le_of_lt this
        have hne : nb_steps ≠ 2 * k + 1 := by
          -- Derive strict real inequality from the `gt` comparison, contradict equality.
          intro heq
          have hcmpR :
              compare ((2 : ℝ) * (k : ℝ) + 1) (nb_steps : ℝ) = Ordering.gt := by
            simpa [two_mul, Int.cast_add, Int.cast_mul, Int.cast_ofNat] using hcmp
          have hxlt : (nb_steps : ℝ) < ((2 : ℝ) * (k : ℝ) + 1) :=
            compare_eq_gt_real (a := ((2 : ℝ) * (k : ℝ) + 1)) (b := (nb_steps : ℝ)) hcmpR
          have heqR : (nb_steps : ℝ) = ((2 : ℝ) * (k : ℝ) + 1) := by
            simpa [Int.cast_add, Int.cast_mul, Int.cast_ofNat, eq_comm] using
              congrArg (fun t : Int => (t : ℝ)) heq
          exact (lt_irrefl (nb_steps : ℝ)) (by simpa [heqR] using hxlt)
        have hgt : nb_steps < 2 * k + 1 := lt_of_le_of_ne hle2k1 hne
        -- Strengthen to `nb_steps < 2*k` using `Int.le_of_lt_add_one` and `2*k < 2*k+1`
        have hk1' : nb_steps < 2 * k := by
          -- From `nb_steps < 2*k + 1`, obtain `nb_steps ≤ 2*k`.
          have hle2k : nb_steps ≤ 2 * k := (Int.lt_add_one_iff.mp hgt)
          -- Also, oddness of `nb_steps` forbids equality with `2*k`.
          have hneq2k : nb_steps ≠ 2 * k := by
            intro heq2k
            -- Then `2 ∣ nb_steps`, hence `nb_steps % 2 = 0`, contradicting `Ho`.
            have hdiv : (2 : Int) ∣ nb_steps := ⟨k, by simpa [heq2k, two_mul]⟩
            have hmod0 : nb_steps % 2 = 0 := Int.emod_eq_zero_of_dvd hdiv
            have : (0 : Int) = 1 := by simpa [hmod0] using Ho
            exact (by decide : (0 : Int) ≠ 1) this
          exact lt_of_le_of_ne hle2k hneq2k
        -- Now reuse the earlier `inbetween_step_Hi` style proof
        -- Global bounds
        have hkposR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
        have hstart_lt_step : start < start + k * step := by
          have : 0 < (k : ℝ) * step := mul_pos hkposR hstep_pos
          simpa using (add_lt_add_left this start)
        have hx_gt_start : start < x := by
          cases Hx' with
          | inbetween_Exact hxeq => simpa [hxeq] using hstart_lt_step
          | inbetween_Inexact _ hbounds _ => exact lt_trans hstart_lt_step hbounds.1
        -- Upper bound using k+1 ≤ nb_steps
        have hle_succ : k + 1 ≤ nb_steps := Int.add_one_le_iff.mpr hklt
        have hle_succR : (k + 1 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast hle_succ
        have hmul_le : (k + 1 : ℝ) * step ≤ (nb_steps : ℝ) * step :=
          mul_le_mul_of_nonneg_right hle_succR hstep_nonneg
        have hx_lt_step_succ : x < start + (k + 1) * step := by
          cases Hx' with
          | inbetween_Exact hxeq =>
              have : start + k * step < start + k * step + step := by
                simpa using (add_lt_add_left hstep_pos (start + k * step))
              simpa [hxeq, add_mul, one_mul, Int.cast_add, Int.cast_ofNat] using this
          | inbetween_Inexact _ hbounds _ => exact hbounds.2
        have hx_lt_global : x < start + nb_steps * step := by
          have : start + ((k + 1 : ℝ) * step) ≤ start + (nb_steps : ℝ) * step :=
            add_le_add_right hmul_le start
          exact lt_of_lt_of_le hx_lt_step_succ this
        -- Midpoint comparison: x > midpoint
        have h1R : (nb_steps : ℝ) < (2 : ℝ) * (k : ℝ) := by exact_mod_cast hk1'
        have hmul' : (nb_steps : ℝ) * step < (2 : ℝ) * ((k : ℝ) * step) := by
          simpa [mul_assoc] using (mul_lt_mul_of_pos_right h1R hstep_pos)
        have hsum : start + (start + nb_steps * step) < 2 * (start + k * step) := by
          calc
            start + (start + nb_steps * step)
                = start + start + (nb_steps : ℝ) * step := by ring
            _ < start + start + (2 : ℝ) * ((k : ℝ) * step) := by exact add_lt_add_right hmul' (start + start)
            _ = 2 * (start + k * step) := by ring
        have hmid_lt_step : (start + (start + nb_steps * step)) / 2 < start + k * step := by
          have := mul_lt_mul_of_pos_left hsum (by norm_num : 0 < (1 / 2 : ℝ))
          simpa [one_div, mul_comm, mul_left_comm, mul_assoc]
        -- From local inbetween, start + k*step ≤ x
        have hx_ge_step : start + k * step ≤ x := by
          cases Hx' with
          | inbetween_Exact hxeq => simpa [hxeq]
          | inbetween_Inexact _ hbounds _ => exact le_of_lt hbounds.1
        have hmid_lt_x : (start + (start + nb_steps * step)) / 2 < x :=
          lt_of_lt_of_le hmid_lt_step hx_ge_step
        have hcmp : compare x ((start + (start + nb_steps * step)) / 2) = Ordering.gt := by
          simp [compare, not_lt.mpr (le_of_lt hmid_lt_x), hmid_lt_x]
        -- Reduce goal to expect `Location.loc_Inexact Ordering.gt`
        -- Evaluate the program: here `¬ (2*k+1 < nb_steps)` and `¬ (2*k+1 = nb_steps)`.
        have hlt_false : ¬ (2 * k + 1 < nb_steps) := by
          exact not_lt.mpr hle2k1
        have heq_false : ¬ (2 * k + 1 = nb_steps) := by
          simpa [eq_comm] using hne
        -- Conclude after simplifying the computed location.
        simpa [new_location_odd, hkz, hlt_false, heq_false] using
          (inbetween.inbetween_Inexact (l := Ordering.gt)
            ⟨hx_gt_start, hx_lt_global⟩ hcmp)

/-- New location computation

    Main entry point choosing between even and odd step logic
-/
noncomputable def new_location (nb_steps k : Int) (l : Location) : Location :=
  if nb_steps % 2 = 0 then
    new_location_even nb_steps k l
  else
    new_location_odd nb_steps k l

/-- Specification: New location is correct

    The computed location accurately represents position in full range
-/
theorem new_location_correct (x : ℝ) (k : Int) (l : Location)
    (Hk : 0 ≤ k ∧ k < nb_steps)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x l)
    (Hstep : 0 < step) :
    ⦃⌜0 ≤ k ∧ k < nb_steps ∧
      inbetween (start + k * step) (start + (k + 1) * step) x l⌝⦄
    (pure (new_location nb_steps k l) : Id Location)
    ⦃⇓result => ⌜inbetween start (start + nb_steps * step) x result⌝⦄ := by
  -- Split on parity and reuse the corresponding correctness lemmas
  by_cases He : nb_steps % 2 = 0
  · -- Even number of steps: reduce to `new_location_even_correct`
    -- After rewriting the program, we can feed the strengthened precondition.
    intro hpre
    have hpre' : nb_steps % 2 = 0 ∧ 0 ≤ k ∧ k < nb_steps ∧
        inbetween (start + k * step) (start + (k + 1) * step) x l := by
      exact And.intro He ⟨hpre.1, hpre.2.1, hpre.2.2⟩
    -- Apply the specialized correctness theorem
    have htrip :=
      (new_location_even_correct (start := start) (step := step)
        (nb_steps := nb_steps) (x := x) (k := k) (l := l)
        (He := He) (Hk := Hk) (Hstep := Hstep) (Hx := Hx))
    -- Run it with the strengthened precondition
    have := htrip hpre'
    -- Normalize the program being analyzed
    simpa [new_location, He]
  · -- Odd number of steps: obtain `% 2 = 1` and reduce to `new_location_odd_correct`
    -- From `¬%2=0`, `Int.emod_two_eq_zero_or_one` gives `%2=1`.
    have Ho : nb_steps % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one nb_steps with h0 | h1
      · exact (False.elim (He h0))
      · exact h1
    intro hpre
    have hpre' : nb_steps % 2 = 1 ∧ 0 ≤ k ∧ k < nb_steps ∧
        inbetween (start + k * step) (start + (k + 1) * step) x l := by
      exact And.intro Ho ⟨hpre.1, hpre.2.1, hpre.2.2⟩
    -- Apply the specialized correctness theorem for odd parity
    have htrip :=
      (new_location_odd_correct (start := start) (step := step)
        (nb_steps := nb_steps) (x := x) (k := k) (l := l)
        (Ho := Ho) (Hk := Hk) (Hstep := Hstep) (Hx := Hx))
    have := htrip hpre'
    simpa [new_location, He]

end SteppingRanges

/-- Helper for float location -/
def inbetween_float (beta : Int) (m e : Int) (x : ℝ) (l : Location) : Prop :=
  inbetween ((Defs.F2R (Defs.FlocqFloat.mk m e : Defs.FlocqFloat beta)))
            ((Defs.F2R (Defs.FlocqFloat.mk (m + 1) e : Defs.FlocqFloat beta))) x l

/- Additional theorems mirroring Coq counterparts that were missing in Lean. -/

section ExtraCoqTheorems

variable {d u x : ℝ}

-- Step and parity auxiliary results
theorem inbetween_step_Lo_not_Eq
    (start step : ℝ) (nb_steps : Int)
    (Hstep : 0 < step)
    (Hnb : 1 < nb_steps)
    (x : ℝ) (l : Location)
    (Hx : inbetween start (start + step) x l)
    (Hl : l ≠ Location.loc_Exact) :
    inbetween start (start + nb_steps * step) x (Location.loc_Inexact Ordering.lt) := by
  -- Extract strict local bounds from the non-exact location
  have hx_gt_start : start < x := by
    cases Hx with
    | inbetween_Exact hxeq => exact (False.elim (Hl rfl))
    | inbetween_Inexact _ hbounds _ => exact hbounds.1
  have hx_lt_step : x < start + step := by
    cases Hx with
    | inbetween_Exact hxeq => exact (False.elim (Hl rfl))
    | inbetween_Inexact _ hbounds _ => exact hbounds.2
  -- Since nb_steps ≥ 2 and step > 0, we have step < nb_steps * step
  have htwo_le_nb : (2 : Int) ≤ nb_steps := by
    -- 2 ≤ nb_steps ↔ 1 < nb_steps
    exact Int.add_one_le_iff.mpr Hnb
  have htwo_le_nbR : (2 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast htwo_le_nb
  have hstep_nonneg : 0 ≤ step := le_of_lt Hstep
  have hmul_mono : (2 : ℝ) * step ≤ (nb_steps : ℝ) * step :=
    mul_le_mul_of_nonneg_right htwo_le_nbR hstep_nonneg
  -- Rather than use the previous attempt, directly bound the midpoint to the right of start+step
  -- Show that the global midpoint is to the right of start + step
  have two_pos : 0 < (2 : ℝ) := by norm_num
  have h2_le_nbR : (2 : ℝ) ≤ (nb_steps : ℝ) := htwo_le_nbR
  have hmid_ge_step : start + step ≤ (start + (start + nb_steps * step)) / 2 := by
    -- 2*(start + step) ≤ start + (start + nb_steps*step)
    have hineq : 2 * (start + step) ≤ start + (start + nb_steps * step) := by
      have : 2 * step ≤ (nb_steps : ℝ) * step := hmul_mono
      -- add 2*start to both sides
      have := add_le_add_left this (2 * start)
      simpa [two_mul, add_comm, add_left_comm, add_assoc] using this
    -- divide by 2 (>0)
    simpa using ((le_div_iff₀ two_pos).mpr (by simpa [mul_comm] using hineq))
  -- Chain inequalities: x < start + step ≤ midpoint ⇒ x < midpoint
  have hx_lt_mid : x < (start + (start + nb_steps * step)) / 2 :=
    lt_of_lt_of_le hx_lt_step hmid_ge_step
  -- Conclude with inexact location and comparison to midpoint
  refine inbetween.inbetween_Inexact (l := Ordering.lt) ?hb ?hc
  · -- global strict bounds
    have hx_lt_global : x < start + nb_steps * step := by
      -- x < start + step < start + nb_steps * step
      have hstep_lt_nb : start + step < start + nb_steps * step := by
        -- From 1 < nb_steps and step > 0, multiply inequality by step
        have : (1 : ℝ) < (nb_steps : ℝ) := by exact_mod_cast Hnb
        have : (1 : ℝ) * step < (nb_steps : ℝ) * step := mul_lt_mul_of_pos_right this Hstep
        simpa [one_mul] using (add_lt_add_left this start)
      exact lt_trans hx_lt_step hstep_lt_nb
    exact ⟨hx_gt_start, hx_lt_global⟩
  · -- comparison with midpoint is Lt since x < midpoint
    simp [compare, hx_lt_mid]

lemma middle_odd
    (start step : ℝ) (k nb_steps : Int)
    (Hk : 2 * k + 1 = nb_steps) :
  (start + k * step + (start + (k + 1) * step)) / 2
      = start + ((nb_steps : ℝ) / 2) * step := by
  -- Work in reals; rewrite `nb_steps` using the odd decomposition
  classical
  -- Cast the integer identity to reals
  have hnbR : (nb_steps : ℝ) = ((2 * k + 1 : Int) : ℝ) := by
    simpa [Hk, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  -- Set the right-hand side core expression for readability
  set B : ℝ := start + ((nb_steps : ℝ) / 2) * step
  -- Show equality by clearing the division: compare numerators
  have hnum : start + k * step + (start + (k + 1) * step) = 2 * B := by
    calc
      start + k * step + (start + (k + 1) * step)
          = 2 * start + (2 * (k : ℝ) + 1) * step := by ring
      _ = 2 * start + (nb_steps : ℝ) * step := by
            simpa [hnbR]
      _ = 2 * (start + ((nb_steps : ℝ) / 2) * step) := by ring
  -- Divide by 2 on both sides
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  calc
    (start + k * step + (start + (k + 1) * step)) / 2
        = (2 * B) / 2 := by simpa [hnum]
    _ = (B * 2) / 2 := by simpa [mul_comm]
    _ = B := by
          simpa [h2ne] using (mul_div_cancel' (a := B) (b := (2 : ℝ)) h2ne)
  -- Replace `B` with its definition
  all_goals
    simpa [B]

theorem inbetween_step_any_Mi_odd
    (start step : ℝ) (nb_steps : Int)
    (x : ℝ) (k : Int) (l : Ordering)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x (Location.loc_Inexact l))
    (Hk : 2 * k + 1 = nb_steps)
    (Hnb : 1 < nb_steps) :
    inbetween start (start + nb_steps * step) x (Location.loc_Inexact l) := by
  -- Extract strict local bounds and local midpoint comparison
  cases Hx with
  | inbetween_Inexact _ hbounds hcmpLocal =>
      -- From local strict bounds, deduce step > 0
      have hstep_pos : 0 < step := by
        -- start + k*step < x and x < start + (k+1)*step ⇒ start + k*step < start + (k+1)*step
        have hx_lt_succR : x < start + ((k + 1 : Int) : ℝ) * step := by
          simpa [Int.cast_add, Int.cast_ofNat, add_mul, one_mul] using hbounds.2
        have hlt_endpoints : start + (k : ℝ) * step < start + ((k + 1 : Int) : ℝ) * step :=
          lt_trans hbounds.1 hx_lt_succR
        -- cancel the same left term `start`
        have hlt_mul : (k : ℝ) * step < ((k + 1 : Int) : ℝ) * step :=
          (add_lt_add_iff_left (a := start)).mp hlt_endpoints
        -- rewrite RHS to k*step + step
        have hlt_add : (k : ℝ) * step < (k : ℝ) * step + step := by
          simpa [Int.cast_add, Int.cast_ofNat, add_mul, one_mul]
            using hlt_mul
        -- a < a + b ⇒ 0 < b
        have : (k : ℝ) * step + 0 < (k : ℝ) * step + step := by simpa using hlt_add
        exact lt_of_add_lt_add_left this
      have hstep_nonneg : 0 ≤ step := le_of_lt hstep_pos
      -- From nb_steps = 2*k + 1 and 1 < nb_steps, get k > 0 (hence k ≥ 0)
      have hkposZ : (0 : Int) < k := by
        -- 1 < 2*k + 1 by rewriting `nb_steps`
        have : 1 < 2 * k + 1 := by simpa [Hk] using Hnb
        -- subtract 1: 0 < 2*k
        have h2k_pos : 0 < 2 * k := by simpa using (sub_lt_sub_right this 1)
        -- if k ≤ 0 then 2*k ≤ 0, contradiction with h2k_pos
        by_contra hk_nonpos
        have hk_le : k ≤ 0 := le_of_not_gt hk_nonpos
        have two_k_le_zero : 2 * k ≤ 0 := by
          have := add_le_add hk_le hk_le
          simpa [two_mul] using this
        exact (not_le_of_gt h2k_pos) two_k_le_zero
      have hkposR : 0 < (k : ℝ) := by exact_mod_cast hkposZ
      -- Global lower bound: start < x
      have hx_gt_start : start < x := by
        -- If k ≥ 0 and step ≥ 0 then start ≤ start + k*step; combine with local lower bound
        have hk_nonnegR : 0 ≤ (k : ℝ) := le_of_lt hkposR
        have hkstep_nonneg : 0 ≤ (k : ℝ) * step := mul_nonneg hk_nonnegR hstep_nonneg
        have : start ≤ start + (k : ℝ) * step := by simpa using add_le_add_left hkstep_nonneg start
        exact lt_of_le_of_lt this hbounds.1
      -- Global upper bound: x < start + nb_steps * step
      have hx_lt_global : x < start + (nb_steps : ℝ) * step := by
        -- From local: x < start + (k+1)*step, and (k+1) ≤ nb_steps
        have hx_lt_succ : x < start + ((k + 1 : Int) : ℝ) * step := by
          simpa [Int.cast_add, Int.cast_ofNat, add_mul, one_mul] using hbounds.2
        -- Show (k+1) ≤ nb_steps as reals using k ≥ 0
        have hk_nonnegR : 0 ≤ (k : ℝ) := le_of_lt hkposR
        have hcoef_le : (k : ℝ) + 1 ≤ (2 : ℝ) * (k : ℝ) + 1 := by
          -- k ≤ 2k when k ≥ 0, then add 1 to both sides
          have hk_le_2k : (k : ℝ) ≤ (k : ℝ) + (k : ℝ) :=
            le_add_of_nonneg_right hk_nonnegR
          simpa [two_mul] using add_le_add_right hk_le_2k 1
        have hcoef_le' : ((k + 1 : Int) : ℝ) ≤ (nb_steps : ℝ) := by
          -- rewrite nb_steps using Hk and casts
          have : (k : ℝ) + 1 ≤ (2 : ℝ) * (k : ℝ) + 1 := hcoef_le
          have : (k : ℝ) + 1 ≤ ((2 * k + 1 : Int) : ℝ) := by
            simpa [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
              using this
          simpa [Hk]
            using this
        have hmul_le : ((k + 1 : Int) : ℝ) * step ≤ (nb_steps : ℝ) * step :=
          mul_le_mul_of_nonneg_right hcoef_le' hstep_nonneg
        exact lt_of_lt_of_le hx_lt_succ (by simpa using add_le_add_left hmul_le start)
      -- Midpoint comparison: rewrite local midpoint to global midpoint using odd decomposition
      have hmid_eq :
          (start + k * step + (start + (k + 1) * step)) / 2
            = start + ((nb_steps : ℝ) / 2) * step :=
        middle_odd start step k nb_steps Hk
      have hcmp_global : compare x (start + ((nb_steps : ℝ) / 2) * step) = l := by
        -- rewrite the local midpoint into the global midpoint
        simpa [hmid_eq] using hcmpLocal
      -- Align with the exact midpoint shape used in `inbetween`
      have hmid_global_shape :
          (start + (start + (nb_steps : ℝ) * step)) / 2
            = start + ((nb_steps : ℝ) / 2) * step := by
        ring
      -- Conclude with inexact global location
      exact
        inbetween.inbetween_Inexact (l := l)
          ⟨hx_gt_start, hx_lt_global⟩
          (by simpa [hmid_global_shape] using hcmp_global)

theorem inbetween_step_Lo_Mi_Eq_odd
    (start step : ℝ) (nb_steps : Int)
    (x : ℝ) (k : Int)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x Location.loc_Exact)
    (Hk : 2 * k + 1 = nb_steps)
    (Hstep : 0 < step) (Hnb : 1 < nb_steps) :
    inbetween start (start + nb_steps * step) x (Location.loc_Inexact Ordering.lt) := by
  -- From exact local location, get x = start + k*step
  cases Hx with
  | inbetween_Exact hxeq =>
      -- Show k > 0 using nb_steps = 2*k + 1 and 1 < nb_steps
      have hkposZ : (0 : Int) < k := by
        have : 1 < 2 * k + 1 := by simpa [Hk] using Hnb
        have h2k_pos : 0 < 2 * k := by
          simpa using (sub_lt_sub_right this 1)
        by_contra hk_nonpos
        have hk_le : k ≤ 0 := le_of_not_gt hk_nonpos
        have two_k_le_zero : 2 * k ≤ 0 := by
          have := add_le_add hk_le hk_le
          simpa [two_mul] using this
        exact (not_le_of_gt h2k_pos) two_k_le_zero
      have hkposR : 0 < (k : ℝ) := by exact_mod_cast hkposZ
      have hstep_nonneg : 0 ≤ step := le_of_lt Hstep
      -- Global lower bound: start < x
      have hx_gt_start : start < x := by
        have : 0 < (k : ℝ) * step := mul_pos hkposR Hstep
        have : start < start + (k : ℝ) * step := by simpa using (add_lt_add_left this start)
        simpa [hxeq] using this
      -- Local upper bound implies x < start + (k+1)*step
      have hx_lt_step_succ : x < start + (k + 1) * step := by
        have : start + k * step < start + k * step + step := by
          simpa using (add_lt_add_left Hstep (start + k * step))
        simpa [hxeq, add_mul, one_mul, Int.cast_add, Int.cast_ofNat] using this
      -- Compare coefficients: k + 1 ≤ nb_steps (since nb_steps = 2*k + 1 and k ≥ 0)
      have hk_nonneg : 0 ≤ k := le_of_lt hkposZ
      have hk_le_2k : k ≤ 2 * k := by
        -- k ≤ k + k = 2*k using k ≥ 0
        have := add_le_add_left hk_nonneg k
        simpa [two_mul] using this
      have hcoef_le : k + 1 ≤ 2 * k + 1 := add_le_add_left hk_le_2k 1
      have hcoef_leR : ((k + 1 : Int) : ℝ) ≤ (nb_steps : ℝ) := by
        have : ((k + 1 : Int) : ℝ) ≤ ((2 * k + 1 : Int) : ℝ) := by exact_mod_cast hcoef_le
        simpa [Hk] using this
      -- Monotonicity with nonnegative step lifts to scaled inequality
      -- Also record the version `(↑k + 1) ≤ ↑nb_steps` for convenient rewriting
      have hle_succR' : (k : ℝ) + 1 ≤ (nb_steps : ℝ) := by
        simpa [Int.cast_add, Int.cast_ofNat] using hcoef_leR
      have hmul_le : ((k : ℝ) + 1) * step ≤ (nb_steps : ℝ) * step :=
        mul_le_mul_of_nonneg_right hle_succR' hstep_nonneg
      -- Global upper bound
      have hx_lt_global : x < start + nb_steps * step := by
        have : start + (((k : ℝ) + 1) * step) ≤ start + (nb_steps : ℝ) * step :=
          add_le_add_right hmul_le start
        exact lt_of_lt_of_le hx_lt_step_succ this
      -- Midpoint comparison: x is left of the global midpoint
      -- First express the global midpoint in the "nb_steps/2" form
      have hmid_global_shape :
          (start + (start + (nb_steps : ℝ) * step)) / 2
            = start + ((nb_steps : ℝ) / 2) * step := by
        ring
      -- And relate it to the local step midpoint using the odd decomposition
      have hmid_local :
          (start + k * step + (start + (k + 1) * step)) / 2
            = start + ((nb_steps : ℝ) / 2) * step :=
        middle_odd start step k nb_steps Hk
      -- Show x (= start + k*step) is strictly less than the local midpoint
      have hx_lt_mid_local : x < (start + ((nb_steps : ℝ) / 2) * step) := by
        -- Let a := start + k*step, b := start + (k+1)*step, and note a < b.
        have hlt_ab : start + k * step < start + (k + 1) * step := by
          simpa [hxeq] using hx_lt_step_succ
        -- Then (a + a) / 2 < (a + b) / 2 since division by 2 preserves order.
        have hsum_lt : (start + k * step) + (start + k * step)
                          < (start + k * step) + (start + (k + 1) * step) :=
          add_lt_add_right hlt_ab (start + k * step)
        have hdiv_lt :
            ((start + k * step) + (start + k * step)) / 2
              < ((start + k * step) + (start + (k + 1) * step)) / 2 := by
          exact (div_lt_div_of_pos_right hsum_lt (by norm_num : (0 : ℝ) < 2))
        -- But (a + a)/2 = a; rewrite and conclude, then map to the global midpoint.
        have : start + k * step
            < (start + k * step + (start + (k + 1) * step)) / 2 := by
          simpa [two_mul] using hdiv_lt
        simpa [hxeq, hmid_local] using this
      -- The comparison to the canonical global midpoint
      have hcmp : compare x ((start + (start + nb_steps * step)) / 2) = Ordering.lt := by
        -- Rewrite midpoint and use `hx_lt_mid_local`
        have : compare x (start + ((nb_steps : ℝ) / 2) * step) = Ordering.lt := by
          simp [compare, hx_lt_mid_local]
        simpa [hmid_global_shape] using this
      -- Conclude with inexact global location and established bounds
      exact inbetween.inbetween_Inexact (l := Ordering.lt)
        ⟨hx_gt_start, hx_lt_global⟩ hcmp

theorem inbetween_step_Hi_Mi_even
    (start step : ℝ) (nb_steps : Int)
    (x : ℝ) (k : Int) (l : Location)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x l)
    (Hl : l ≠ Location.loc_Exact)
    (Hk : 2 * k = nb_steps) (Hstep : 0 < step) (Hnb : 1 < nb_steps) :
    inbetween start (start + nb_steps * step) x (Location.loc_Inexact Ordering.gt) := by
  -- From non-exact local location, extract strict local bounds
  have hbounds : (start + k * step) < x ∧ x < (start + (k + 1) * step) := by
    cases Hx with
    | inbetween_Exact hxeq => exact (False.elim (Hl rfl))
    | inbetween_Inexact _ h _ => exact h
  -- From parity/equality nb_steps = 2*k and nb_steps > 1, deduce k ≥ 1
  have hkposZ : (0 : Int) < k := by
    -- Since 1 < 2*k, we get k ≥ 1 hence 0 < k
    have h1lt2k : (1 : Int) < 2 * k := by simpa [Hk] using Hnb
    -- If k ≤ 0, then 2*k ≤ 0, contradicting 1 < 2*k
    by_contra hk_nonpos
    have hk_le : k ≤ 0 := le_of_not_gt hk_nonpos
    have two_k_le_zero : 2 * k ≤ 0 := by
      -- 2*k = k + k ≤ 0 + 0
      have := add_le_add hk_le hk_le
      simpa [two_mul] using this
    -- Strengthen 2*k ≤ 0 to 2*k ≤ 1 then contradict 1 < 2*k
    have two_k_le_one : 2 * k ≤ 1 := le_trans two_k_le_zero (by decide : (0 : Int) ≤ 1)
    exact (not_le_of_gt h1lt2k) two_k_le_one
  have hk_nonneg : 0 ≤ k := le_of_lt hkposZ
  -- Monotonicity facts with step > 0 in reals
  have hstep_nonneg : 0 ≤ step := le_of_lt Hstep
  -- Lower global bound: start < x, via start ≤ start + k*step and local strictness
  have hx_gt_start : start < x := by
    -- 0 ≤ k and step ≥ 0 imply start ≤ start + k*step
    have hstart_le_step : start ≤ start + k * step := by
      -- Use that (k : ℝ) ≥ 0 and step ≥ 0
      have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_nonneg
      have hprod : (0 : ℝ) ≤ (k : ℝ) * step := mul_nonneg hkR hstep_nonneg
      have := add_le_add_left hprod start
      simpa using this
    exact lt_of_le_of_lt hstart_le_step hbounds.1
  -- Upper global bound: x < start + nb_steps * step using k+1 ≤ nb_steps and step ≥ 0
  have hk1_le_2k : k + 1 ≤ 2 * k := by
    -- Using k < 2*k (since k > 0), turn strict into succ ≤
    have hk_lt_2k : k < 2 * k := by
      simpa [two_mul] using add_lt_add_left hkposZ k
    exact Int.add_one_le_iff.mpr hk_lt_2k
  have hcoef_le : ((k + 1 : Int) : ℝ) ≤ (nb_steps : ℝ) := by
    -- Cast inequality k+1 ≤ 2k and rewrite 2k as nb_steps
    have : ((k + 1 : Int) : ℝ) ≤ ((2 * k : Int) : ℝ) := by exact_mod_cast hk1_le_2k
    simpa [Hk] using this
  have hmul_le : ((k + 1 : Int) : ℝ) * step ≤ (nb_steps : ℝ) * step :=
    mul_le_mul_of_nonneg_right hcoef_le hstep_nonneg
  have hmul_le' : ((k : ℝ) + 1) * step ≤ (nb_steps : ℝ) * step := by
    simpa [Int.cast_add, Int.cast_ofNat, add_mul, one_mul] using hmul_le
  have hx_lt_global : x < start + nb_steps * step := by
    -- local upper bound then monotonicity to global
    have hx_lt_succ : x < start + ((k : ℝ) + 1) * step := by
      simpa [Int.cast_add, Int.cast_ofNat, add_mul, one_mul] using hbounds.2
    have : start + (((k : ℝ) + 1) * step) ≤ start + (nb_steps : ℝ) * step :=
      add_le_add_right hmul_le' start
    exact lt_of_lt_of_le hx_lt_succ this
  -- Midpoint comparison: even case midpoint equals start + k*step
  have hmid_global_shape :
      (start + (start + (nb_steps : ℝ) * step)) / 2
        = start + ((nb_steps : ℝ) / 2) * step := by
    ring
  have hnb_even_mid : start + ((nb_steps : ℝ) / 2) * step = start + k * step := by
    -- Use 2*k = nb_steps
    have : ((nb_steps : ℝ) / 2) = (k : ℝ) := by
      have hnbR : (nb_steps : ℝ) = ((2 * k : Int) : ℝ) := by
        simpa [Int.cast_mul, Int.cast_ofNat] using congrArg (fun z : Int => (z : ℝ)) Hk.symm
      -- (2*k)/2 = k
      have h2ne : (2 : ℝ) ≠ 0 := by norm_num
      calc
        (nb_steps : ℝ) / 2 = (((2 * k : Int) : ℝ)) / 2 := by simpa [hnbR]
        _ = ((2 : ℝ) * (k : ℝ)) / 2 := by simp [Int.cast_mul, Int.cast_ofNat]
        _ = (k : ℝ) := by
              simpa [h2ne] using (mul_div_cancel' (a := (k : ℝ)) (b := (2 : ℝ)) h2ne)
    simpa [this]
  have hmid_eq_local :
      (start + (start + nb_steps * step)) / 2 = start + k * step := by
    simpa [hmid_global_shape, hnb_even_mid]
  -- Therefore, x is to the right of the global midpoint
  have hcmp : compare x ((start + (start + nb_steps * step)) / 2) = Ordering.gt := by
    -- Since x > start + k*step and midpoint equals that value
    have hx_gt_mid : (start + k * step) < x := hbounds.1
    have : compare x (start + k * step) = Ordering.gt := by
      have : (start + k * step) < x := hx_gt_mid
      -- Convert strict inequality to compare = gt
      have hxgt : (start + k * step) < x := this
      -- unfold compare on gt case
      have : x > start + k * step := by simpa [gt_iff_lt] using hxgt
      -- Now `simp` on compare using gt
      simpa [compare, not_lt.mpr (le_of_lt this), this]
    -- Rewrite midpoint to local form
    simpa [hmid_eq_local]
      using this
  -- Conclude with inexact global location and bounds
  exact inbetween.inbetween_Inexact (l := Ordering.gt) ⟨hx_gt_start, hx_lt_global⟩ hcmp

theorem inbetween_step_Mi_Mi_even
    (start step : ℝ) (nb_steps : Int)
    (x : ℝ) (k : Int)
    (Hx : inbetween (start + k * step) (start + (k + 1) * step) x Location.loc_Exact)
    (Hk : 2 * k = nb_steps) (Hstep : 0 < step) (Hnb : 1 < nb_steps) :
    inbetween start (start + nb_steps * step) x (Location.loc_Inexact Ordering.eq) := by
  -- Use the provided step positivity and nb_steps lower bound.
  have hstep_pos : 0 < step := Hstep
  have hnb_pos : 1 < nb_steps := Hnb
  -- From parity `nb_steps = 2*k` and `1 < nb_steps`, deduce `0 < k`.
  have hk_pos : (0 : Int) < k := by
    -- If k ≤ 0 then 2*k ≤ 0, contradicting 1 < 2*k = nb_steps.
    have h1lt2k : (1 : Int) < 2 * k := by simpa [Hk] using hnb_pos
    by_contra hk_nonpos
    have hk_le : k ≤ 0 := le_of_not_gt hk_nonpos
    have two_k_le_zero : 2 * k ≤ 0 := by
      -- 2*k = k + k ≤ 0 + 0
      have := add_le_add hk_le hk_le
      simpa [two_mul] using this
    -- Strengthen 2*k ≤ 0 to 2*k ≤ 1 then contradict 1 < 2*k
    have two_k_le_one : 2 * k ≤ 1 := le_trans two_k_le_zero (by decide : (0 : Int) ≤ 1)
    exact (not_le_of_gt h1lt2k) two_k_le_one
  -- Extract x as the left endpoint from local exactness.
  cases Hx with
  | inbetween_Exact hxeq =>
      -- Strict global lower bound: start < x since k > 0 and step > 0.
      have hkposR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
      have hx_gt_start : start < x := by
        have : 0 < (k : ℝ) * step := mul_pos hkposR hstep_pos
        have : start < start + (k : ℝ) * step := by simpa using (add_lt_add_left this start)
        simpa [hxeq]
          using this
      -- Local strict upper bound: x < start + (k+1)*step since step > 0.
      have hx_lt_step_succ : x < start + (k + 1) * step := by
        have : start + k * step < start + k * step + step := by
          simpa using (add_lt_add_left hstep_pos (start + k * step))
        simpa [hxeq, add_mul, one_mul, Int.cast_add, Int.cast_ofNat] using this
      -- From k+1 ≤ nb_steps (using k > 0 and nb_steps = 2*k), deduce global upper bound.
      have hk1_le_2k : k + 1 ≤ 2 * k := by
        -- Since k < 2*k for k > 0, strengthen to k+1 ≤ 2*k.
        have hk_lt_2k : k < 2 * k := by
          simpa [two_mul] using add_lt_add_left hk_pos k
        exact Int.add_one_le_iff.mpr hk_lt_2k
      have hle_succ : k + 1 ≤ nb_steps := by simpa [Hk] using hk1_le_2k
      have hle_succR : (k + 1 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast hle_succ
      have hstep_nonneg : 0 ≤ step := le_of_lt hstep_pos
      have hmul_le : (k + 1 : ℝ) * step ≤ (nb_steps : ℝ) * step :=
        mul_le_mul_of_nonneg_right hle_succR hstep_nonneg
      have hx_lt_global : x < start + nb_steps * step := by
        have : start + ((k + 1 : ℝ) * step) ≤ start + (nb_steps : ℝ) * step :=
          add_le_add_right hmul_le start
        exact lt_of_lt_of_le hx_lt_step_succ this
      -- Midpoint equality for even case: global midpoint equals `start + k*step`.
      -- Cast integer equality `2*k = nb_steps` to reals in a convenient orientation.
      have heqR' : (nb_steps : ℝ) = (((2 * k : Int) : ℝ)) := by
        simpa using congrArg (fun z : Int => (z : ℝ)) Hk.symm
      have hmid_eqR : (start + (start + nb_steps * step)) / 2 = start + k * step := by
        calc
          (start + (start + nb_steps * step)) / 2
              = (start + (start + ((nb_steps : ℝ) * step))) / 2 := by simp
          _   = (start + (start + ((((2 * k : Int) : ℝ)) * step))) / 2 := by
                  simpa [heqR']
          _   = (start + (start + ((2 : ℝ) * (k : ℝ) * step))) / 2 := by
                  simp [Int.cast_mul, Int.cast_ofNat]
          _   = start + k * step := by ring
      -- Therefore comparison to midpoint yields Ordering.eq.
      have hcmp : compare x ((start + (start + nb_steps * step)) / 2) = Ordering.eq := by
        have : x = start + k * step := hxeq
        have : x = (start + (start + nb_steps * step)) / 2 := by
          simpa [hmid_eqR] using this
        -- Reduce to `compare x x`.
        classical
        simpa [compare, this]
      -- Conclude with global inexact equality location.
      exact inbetween.inbetween_Inexact (l := Ordering.eq)
        ⟨hx_gt_start, hx_lt_global⟩ hcmp
  -- No other constructor matches since local location is exact.

-- Compatibility under translation and scaling
theorem inbetween_plus_compat (x d u : ℝ) (l : Location) (t : ℝ) :
    inbetween d u x l → inbetween (d + t) (u + t) (x + t) l := by
  intro h
  cases h with
  | inbetween_Exact hxeq =>
      -- Translate an exact location by t
      have : x + t = d + t := by simpa [hxeq]
      exact inbetween.inbetween_Exact this
  | inbetween_Inexact ord hbounds hcmp =>
      -- Translate strict bounds and midpoint comparison by t
      refine inbetween.inbetween_Inexact (l := ord) ?hb ?hc
      · -- Bounds: add t preserves strict inequalities
        exact ⟨add_lt_add_left hbounds.1 t, add_lt_add_left hbounds.2 t⟩
      · -- Midpoint: ((d+t)+(u+t))/2 = (d+u)/2 + t
        have hmid_eq : ((d + t) + (u + t)) / 2 = (d + u) / 2 + t := by
          ring
        -- Addition by t preserves the compare outcome
        have h1 := compare_sub_zero_real (a := x + t) (b := (d + u) / 2 + t)
        have h2 := compare_sub_zero_real (a := x) (b := (d + u) / 2)
        have hsub : (x + t) - ((d + u) / 2 + t) = x - (d + u) / 2 := by
          ring
        have hA : compare (x + t) ((d + u) / 2 + t) = compare (x - (d + u) / 2) 0 := by
          simpa [hsub] using h1
        have hB : compare x ((d + u) / 2) = compare (x - (d + u) / 2) 0 := by
          simpa using h2
        -- From hcmp and hB, rewrite to the zero-form expected by hA
        have hC : compare (x - (d + u) / 2) 0 = ord := by
          simpa using (hB.symm ▸ hcmp)
        -- Conclude by transitivity and the stored comparison value
        have htrans : compare (x + t) ((d + u) / 2 + t) = ord := by
          simpa using hA.trans hC
        -- Present result under the rewritten midpoint
        simpa [hmid_eq] using htrans

theorem inbetween_plus_reg (x d u : ℝ) (l : Location) (t : ℝ) :
    inbetween (d + t) (u + t) (x + t) l → inbetween d u x l := by
  intro h
  cases h with
  | inbetween_Exact hxeq =>
      -- Cancel the translation by subtracting t on both sides
      have : x = d := by simpa using congrArg (fun z => z - t) hxeq
      exact inbetween.inbetween_Exact this
  | inbetween_Inexact ord hbounds hcmp =>
      -- Remove translation from bounds and midpoint comparison
      refine inbetween.inbetween_Inexact (l := ord) ?hb ?hc
      · -- Bounds: (d+t) < (x+t) and (x+t) < (u+t) imply d < x and x < u
        have hx1 : d < x := (add_lt_add_iff_right t).mp hbounds.1
        have hx2 : x < u := (add_lt_add_iff_right t).mp hbounds.2
        exact ⟨hx1, hx2⟩
      · -- Midpoint: translate compare back using zero-form
        -- Rewrite the midpoint of translated endpoints
        have hmid_eq : ((d + t) + (u + t)) / 2 = (d + u) / 2 + t := by ring
        -- Move compares to zero-form on both sides
        have hmida := compare_sub_zero_real (a := x + t) (b := (d + u) / 2 + t)
        have hmidb := compare_sub_zero_real (a := x) (b := (d + u) / 2)
        have hsub : (x + t) - ((d + u) / 2 + t) = x - (d + u) / 2 := by ring
        -- From hcmp on translated values, deduce zero-form equality
        have hz : compare (x - (d + u) / 2) 0 = ord := by
          -- Start from the given comparison and convert to zero-form
          have hcmp' : compare (x + t) ((d + u) / 2 + t) = ord := by
            simpa [hmid_eq] using hcmp
          -- Use hmida to switch to zero-form, then simplify the subtraction
          have : compare ((x + t) - ((d + u) / 2 + t)) 0 = ord :=
            (Eq.symm hmida).trans hcmp'
          simpa [hsub] using this
        -- Convert back from zero-form to the desired compare x ((d+u)/2)
        have : compare x ((d + u) / 2) = ord := by
          -- hmidb : compare x mid = compare (x - mid) 0
          -- hz    : compare (x - mid) 0 = ord
          -- hence compare x mid = ord
          exact hmidb.trans hz
        simpa using this

theorem inbetween_mult_compat (d u x : ℝ) (l : Location) (s : ℝ)
    (Hs : 0 < s) :
    inbetween d u x l → inbetween (d * s) (u * s) (x * s) l := by
  intro h
  have hspos : 0 < s := Hs
  cases h with
  | inbetween_Exact hxeq =>
      -- Exact point scales exactly
      have : (x * s) = (d * s) := by simpa [hxeq]
      exact inbetween.inbetween_Exact this
  | inbetween_Inexact ord hbounds hcmp =>
      -- Multiply strict bounds by s > 0 preserves ordering
      refine inbetween.inbetween_Inexact (l := ord) ?hb ?hc
      · have hxgt : d * s < x * s := by
          simpa [mul_comm] using mul_lt_mul_of_pos_right hbounds.1 hspos
        have hxlt : x * s < u * s := by
          simpa [mul_comm] using mul_lt_mul_of_pos_right hbounds.2 hspos
        exact ⟨by simpa [mul_comm] using hxgt, by simpa [mul_comm] using hxlt⟩
      · -- Midpoint after scaling by s: ((d*s)+(u*s))/2 = ((d+u)/2)*s
        have hmid_eq : ((d * s) + (u * s)) / 2 = ((d + u) / 2) * s := by ring
        -- Zero-form for both compares
        have hmida := compare_sub_zero_real (a := x * s) (b := ((d + u) / 2) * s)
        have hmidb := compare_sub_zero_real (a := x) (b := (d + u) / 2)
        -- Express subtraction as factoring s
        have hsub : (x * s) - (((d + u) / 2) * s) = s * (x - (d + u) / 2) := by ring
        -- From hcmp, get zero-form then cancel s using positivity
        have hz0 : compare (x - (d + u) / 2) 0 = ord := by
          -- hmidb : compare x mid = compare (x - mid) 0
          -- so rewrite hcmp to zero-form
          simpa using (hmidb ▸ hcmp)
        have hscale : compare (s * (x - (d + u) / 2)) 0 = ord := by
          -- From compare (x - mid) 0 = ord, scale t by positive s keeps compare
          have hmul := compare_mul_pos_right_zero (t := (x - (d + u) / 2)) (c := s) hspos
          -- hmul : compare (s*t) 0 = compare t 0
          -- thus compare (s*t) 0 = ord
          simpa using hmul.trans hz0
        -- Back to non-zero form for scaled terms
        have hscale' : compare ((x * s) - (((d + u) / 2) * s)) 0 = ord := by
          simpa [hsub] using hscale
        have : compare (x * s) (((d + u) / 2) * s) = ord := by
          exact (hmida.trans hscale')
        -- Rewrite midpoint to canonical `(d*s + u*s)/2`
        simpa [hmid_eq] using this

theorem inbetween_mult_reg (d u x : ℝ) (l : Location) (s : ℝ)
    (Hs : 0 < s) :
    inbetween (d * s) (u * s) (x * s) l → inbetween d u x l := by
  intro h
  have hspos : 0 < s := Hs
  cases h with
  | inbetween_Exact hxeq =>
      -- Cancel multiplicative factor s > 0
      have : x = d := by
        have hsne : s ≠ 0 := ne_of_gt hspos
        have := congrArg (fun z => z / s) hxeq
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hsne] using this
      exact inbetween.inbetween_Exact this
  | inbetween_Inexact ord hbounds hcmp =>
      -- Cancel s from strict bounds and midpoint comparison
      refine inbetween.inbetween_Inexact (l := ord) ?hb ?hc
      · have h1 : d < x := by
          have := lt_of_mul_lt_mul_right (a := s) hbounds.1 (le_of_lt hspos)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        have h2 : x < u := by
          have := lt_of_mul_lt_mul_right (a := s) hbounds.2 (le_of_lt hspos)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        exact ⟨h1, h2⟩
      · -- Use zero-form compare invariance under positive scaling in reverse
        have hmida := compare_sub_zero_real (a := x * s) (b := ((d + u) / 2) * s)
        -- From hcmp, move to zero-form for scaled terms
        -- First, rewrite the midpoint in `hcmp` to `((d + u) / 2) * s`
        have hcmp' : compare (x * s) (((d + u) / 2) * s) = ord := by
          -- given hcmp with midpoint = (d*s + u*s)/2
          have hmid_eq : ((d * s) + (u * s)) / 2 = ((d + u) / 2) * s := by ring
          simpa [hmid_eq] using hcmp
        have hz0 : compare ((x * s) - (((d + u) / 2) * s)) 0 = ord := by
          -- Switch to zero-form using hmida, then apply hcmp'
          exact (Eq.symm hmida).trans hcmp'
        -- Cancel s using positivity
        have hsub : (x * s) - (((d + u) / 2) * s) = s * (x - (d + u) / 2) := by ring
        have hcancel := compare_mul_pos_right_zero (t := (x - (d + u) / 2)) (c := s) hspos
        have hx0 : compare (x - (d + u) / 2) 0 = ord := by
          -- First rewrite lhs of hz0 to s * (x - mid), then use hcancel to drop s
          have hz0' : compare (s * (x - (d + u) / 2)) 0 = ord := by
            simpa [hsub] using hz0
          -- hcancel: compare (s * t) 0 = compare t 0; rewrite hz0' to drop s
          simpa using (hcancel.symm).trans hz0'
        -- Convert back to the original midpoint compare
        -- Relate the standard and zero-form comparisons at the midpoint
        -- hmidb : compare x mid = compare (x - mid) 0
        have hmidb := (compare_sub_zero_real (a := x) (b := (d + u) / 2))
        have : compare x ((d + u) / 2) = ord := by
          -- hmidb : compare x mid = compare (x - mid) 0
          -- hx0   : compare (x - mid) 0 = ord
          -- hence compare x mid = ord
          simpa using hmidb.trans hx0
        simpa using this

-- Specialization to consecutive floats
variable (beta : Int)

  theorem inbetween_float_bounds
    (x : ℝ) (m e : Int) (l : Location)
    (H : inbetween_float beta m e x l) (hbeta : 1 < beta) :
    ((Defs.F2R (Defs.FlocqFloat.mk m e : Defs.FlocqFloat beta)) ≤ x ∧
     x < (Defs.F2R (Defs.FlocqFloat.mk (m + 1) e : Defs.FlocqFloat beta))) := by
  -- Unfold the float interval and analyze cases
  dsimp [inbetween_float] at H
  cases H with
  | inbetween_Exact hxeq =>
      -- Left bound holds by equality; right bound from positivity of (beta : ℝ) ^ e
      refine And.intro ?hle ?hlt
      · -- d ≤ x by x = d
        simpa [hxeq]
          using (le_of_eq (rfl : (Defs.F2R (Defs.FlocqFloat.mk m e : Defs.FlocqFloat beta))
                                   = (Defs.F2R (Defs.FlocqFloat.mk m e : Defs.FlocqFloat beta))))
      · -- Show F2R(m,e) < F2R(m+1,e)
        -- Let p = (beta : ℝ) ^ e with p > 0 since 1 < beta
        have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
        have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
        have hp_pos : 0 < (beta : ℝ) ^ e := by exact zpow_pos hbpos_real _
        -- m < m+1 over reals
        have hm_lt_real : (m : ℝ) < (m + 1 : ℝ) := by
          have : (m : ℝ) + 0 < (m : ℝ) + 1 := by
            simpa using (add_lt_add_left (show (0 : ℝ) < 1 by norm_num) (m : ℝ))
          simpa [add_comm, add_left_comm, add_assoc] using this
        -- Multiply by positive p on the right
        have hmul : (m : ℝ) * (beta : ℝ) ^ e < (m + 1 : ℝ) * (beta : ℝ) ^ e :=
          mul_lt_mul_of_pos_right hm_lt_real hp_pos
        -- Rewrite to F2R forms
        simpa [FloatSpec.Core.Defs.F2R, hxeq]
          using hmul
  | inbetween_Inexact _ hbounds _ =>
      -- From strict bounds, weaken left to ≤ and keep right strict
      exact And.intro (le_of_lt hbounds.1) hbounds.2

theorem inbetween_float_new_location
    (x : ℝ) (m e : Int) (l : Location) (k : Int)
    (Hk : 0 < k) (hbeta : 1 < beta)
    (Hx : inbetween_float beta m e x l) :
    inbetween_float beta (m / (beta ^ Int.natAbs k)) (e + k)
      x (Id.run (new_location (nb_steps := beta ^ Int.natAbs k)
                               (k := (m % (beta ^ Int.natAbs k))) l)) := by
  -- Abbreviations
  let p : Int := beta ^ Int.natAbs k
  have hp_def : p = beta ^ Int.natAbs k := rfl
  -- Step size in reals
  let b : ℝ := (beta : ℝ)
  let step : ℝ := b ^ e
  -- Positivity of step from 1 < beta
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos_real : 0 < b := by
    -- Cast positivity of `beta : Int` to reals and rewrite to `b`
    have : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
    simpa [b] using this
  have hstep_pos : 0 < step := by
    simpa [b, step] using (zpow_pos hbpos_real e)
  -- Basic arithmetic on division and modulo
  have hdivmodZ : ((m % p) + p * (m / p) = m) := by
    -- Use updated lemma name in Mathlib for `emod`/`ediv` relationship
    simpa [hp_def] using (Int.emod_add_mul_ediv m p)
  have hdivmodR : ((m % p : Int) : ℝ) + (p : ℝ) * ((m / p : Int) : ℝ) = (m : ℝ) := by
    simpa [Int.cast_add, Int.cast_mul] using congrArg (fun t : Int => (t : ℝ)) hdivmodZ
  have hstart_eq : ((m / p : Int) : ℝ) * (p : ℝ) = (m : ℝ) - ((m % p : Int) : ℝ) := by
    have := hdivmodR
    linear_combination (this : ((m % p : Int) : ℝ) + (p : ℝ) * ((m / p : Int) : ℝ) = (m : ℝ))
  -- Prepare local-step interval rephrasing of Hx
  dsimp [inbetween_float] at Hx
  -- Define start in a way convenient for rewriting
  let start : ℝ := ((m / p : Int) : ℝ) * (p : ℝ) * step
  have hstart_alt : start = ((m - (m % p) : Int) : ℝ) * step := by
    unfold start
    have : ((m / p : Int) : ℝ) * (p : ℝ) = (m : ℝ) - ((m % p : Int) : ℝ) := hstart_eq
    calc
      ((m / p : Int) : ℝ) * (p : ℝ) * step
          = ((m : ℝ) - ((m % p : Int) : ℝ)) * step := by simpa [this]
      _   = ((m - (m % p) : Int) : ℝ) * step := by simpa [Int.cast_sub]
  -- Express local k (remainder) and show its bounds for new_location_correct
  have hp_pos : 0 < p := by
    -- From 1 < beta ⇒ 0 < beta, hence p = beta^(|k|) > 0
    have hβpos : 0 < beta := hbpos_int
    simpa [p] using pow_pos hβpos (Int.natAbs k)
  have hk_bounds : 0 ≤ (m % p) ∧ (m % p) < p := by
    have hnonneg : 0 ≤ (m % p) := Int.emod_nonneg _ (ne_of_gt hp_pos)
    have hlt : (m % p) < p := Int.emod_lt_of_pos _ hp_pos
    exact ⟨hnonneg, hlt⟩
  -- Re-express the local interval endpoints as a step inside the global range
  have Hx_local :
      inbetween (start + ((m % p : Int) : ℝ) * step)
                (start + ((↑(m % p) + 1) : ℝ) * step) x l := by
    -- Rewrite using F2R = m * b^e and the div/mod decomposition
    -- Left endpoint: start + r*step = m * b^e
    -- Right endpoint: start + (r+1)*step = (m+1) * b^e
    have hL : start + ((m % p : Int) : ℝ) * step = (m : ℝ) * step := by
      unfold start step
      have : ((m / p : Int) : ℝ) * (p : ℝ) = (m : ℝ) - ((m % p : Int) : ℝ) := hstart_eq
      calc
        ((m / p : Int) : ℝ) * (p : ℝ) * (b ^ e) + ((m % p : Int) : ℝ) * (b ^ e)
            = (((m : ℝ) - ((m % p : Int) : ℝ)) * (b ^ e)) + ((m % p : Int) : ℝ) * (b ^ e) := by simpa [this]
        _   = (m : ℝ) * (b ^ e) := by ring
    have hR : start + ((↑(m % p) + 1) : ℝ) * step = ((m + 1 : Int) : ℝ) * step := by
      unfold start step
      have : ((m / p : Int) : ℝ) * (p : ℝ) = (m : ℝ) - ((m % p : Int) : ℝ) := hstart_eq
      calc
        ((m / p : Int) : ℝ) * (p : ℝ) * (b ^ e)
              + ((↑(m % p) + 1) : ℝ) * (b ^ e)
            = (((m : ℝ) - ((m % p : Int) : ℝ)) * (b ^ e))
                + ((((m % p : Int) : ℝ) + 1) * (b ^ e)) := by
                    simpa [this]
        _   = (((m : ℝ) - ((m % p : Int) : ℝ)) + ((m % p : Int) : ℝ) + 1) * (b ^ e) := by ring
        _   = ((m : ℝ) + 1) * (b ^ e) := by ring
        _   = ((m + 1 : Int) : ℝ) * (b ^ e) := by simpa [Int.cast_add, Int.cast_ofNat]
    -- Now change Hx to this local-step form via rewriting endpoints
    simpa [FloatSpec.Core.Defs.F2R, hL, hR, step]
      using Hx
  -- Apply new_location correctness on the local step
  have htrip :=
    (new_location_correct (start := start) (step := step)
      (nb_steps := p) (x := x) (k := (m % p)) (l := l)
      (Hk := hk_bounds) (Hx := Hx_local) (Hstep := hstep_pos))
  -- Feed the triple its precondition
  have hpostR : inbetween start (start + (p : ℝ) * step) x
      (Id.run (new_location (nb_steps := p) (k := (m % p)) l)) := by
    simpa using htrip ⟨hk_bounds.1, hk_bounds.2, Hx_local⟩
  -- Simplify the program argument and rewrite the global endpoints into the float form
  -- Left global endpoint equals F2R ((m / p) * p, e) using exponent change
  -- We will rewrite the goal endpoints to
  --   start = ((m / p : Int) : ℝ) * (p : ℝ) * step
  -- and start + p*step = (((m / p : Int) : ℝ) * (p : ℝ) + (p : ℝ)) * step
  -- Then convert both to F2R with exponent e and back to exponent e + k.
  -- First, identify the result of running the program
  -- and present the postcondition as an `inbetween` with global bounds
  -- Compute `start + p * step` in a convenient form
  have hglobR : start + (p : ℝ) * step
        = (((m / p : Int) : ℝ) * (p : ℝ) + (p : ℝ)) * step := by
    unfold start step; ring
  -- Use F2R_change_exp to rewrite the target into the `inbetween` over exponent (e+k)
  -- Equality for the left bound
  have hF_left :
      ((Defs.F2R (Defs.FlocqFloat.mk (m / p) (e + k) : Defs.FlocqFloat beta)))
        = (((m / p : Int) : ℝ) * (p : ℝ)) * step := by
    -- Change exponent from e+k to e, multiplying mantissa by p = beta^|k|
    have he : e ≤ e + k := by exact Int.le_add_of_nonneg_right (le_of_lt Hk)
    -- Invoke change-exp on f = (m/p, e+k) toward e'
    have hce := FloatSpec.Core.Float_prop.F2R_change_exp
      (beta := beta) (f := Defs.FlocqFloat.mk (m / p) (e + k)) (e' := e)
      hbeta he
    -- Unfold the right-hand side
    -- (m/p) * beta^( (e+k) - e) = (m/p) * beta^k = (m/p) * p
    have hkabs : ((e + k) - e).natAbs = Int.natAbs k := by
      have : 0 ≤ (e + k) - e := by simpa using (sub_nonneg.mpr he)
      -- toNat equals natAbs on nonnegatives
      simpa [Int.add_comm, Int.add_left_comm, Int.sub_add_cancel] using
        (natAbs_eq_toNat_of_nonneg this)
    -- Evaluate the change-exp equality
    -- Left equals right with mantissa multiplied by beta^|k|
    -- and exponent e
    have :
        (Defs.F2R (Defs.FlocqFloat.mk (m / p) (e + k) : Defs.FlocqFloat beta))
          = (Defs.F2R (Defs.FlocqFloat.mk ((m / p) * beta ^ Int.natAbs k) e : Defs.FlocqFloat beta)) := by
      simpa [hkabs] using hce
    -- Now unfold F2R on the RHS and simplify
    simpa [FloatSpec.Core.Defs.F2R, b, step, p, hp_def, mul_comm, mul_left_comm, mul_assoc]
      using this
  -- Equality for the right bound
  have hF_right :
      ((Defs.F2R (Defs.FlocqFloat.mk ((m / p) + 1) (e + k) : Defs.FlocqFloat beta)))
        = ((((m / p : Int) : ℝ) * (p : ℝ)) + (p : ℝ)) * step := by
    have he : e ≤ e + k := by exact Int.le_add_of_nonneg_right (le_of_lt Hk)
    have hce := FloatSpec.Core.Float_prop.F2R_change_exp
      (beta := beta) (f := Defs.FlocqFloat.mk ((m / p) + 1) (e + k)) (e' := e)
      hbeta he
    have hkabs : ((e + k) - e).natAbs = Int.natAbs k := by
      have : 0 ≤ (e + k) - e := by simpa using (sub_nonneg.mpr he)
      simpa [Int.add_comm, Int.add_left_comm, Int.sub_add_cancel] using
        (natAbs_eq_toNat_of_nonneg this)
    have :
        (Defs.F2R (Defs.FlocqFloat.mk ((m / p) + 1) (e + k) : Defs.FlocqFloat beta))
          = (Defs.F2R (Defs.FlocqFloat.mk (((m / p) + 1) * beta ^ Int.natAbs k) e : Defs.FlocqFloat beta)) := by
      simpa [hkabs] using hce
    -- Unfold and simplify, then rewrite `(a+1)*p = a*p + p`
    have htmp : (((m / p : Int) : ℝ) + 1) * (p : ℝ)
        = (((m / p : Int) : ℝ) * (p : ℝ) + (p : ℝ)) := by ring
    simpa [FloatSpec.Core.Defs.F2R, b, step, p, hp_def, mul_comm, mul_left_comm, mul_assoc,
           Int.cast_add, Int.cast_ofNat, add_comm, add_left_comm, add_assoc, htmp, mul_add]
      using this
  -- Finally, relate the `new_location_correct` postcondition to the desired goal
  -- The Hoare triple gives: inbetween start (start + p*step) x (Id.run (new_location ...))
  -- Rewrite bounds to F2R with exponent e+k and conclude.
  -- Convert the triple result into a plain proposition by running the Id program
  -- and aligning endpoints.
  -- Evaluate the program and use the established equalities
  -- Reduce the goal to the postcondition of `new_location_correct`
  -- Left endpoint: F2R (m/p, e+k)
  -- Right endpoint: F2R (m/p+1, e+k)
  -- Both match `start` and `start + p*step` respectively.
  -- Thus, we can rewrite and apply `hpost`.
  -- Replace the endpoints in the goal
  -- Unfold inbetween_float on the goal side
  dsimp [inbetween_float]
  -- Use the postcondition from `new_location_correct`
  -- The program evaluated here is exactly `new_location p (m % p) l`.
  -- Present the bounds in the same shape as `hpost` and finish.
  -- `hpost` already proves the desired `inbetween` for these bounds, so rewrite them.
  -- Rewrite left bound: F2R with exponent e+k equals `start`
  have hleft' : ((Defs.F2R (Defs.FlocqFloat.mk (m / p) (e + k) : Defs.FlocqFloat beta))) = start := by
    -- From hF_left with `step = b^e` and `start` definition
    simpa [start, step] using hF_left
  -- Rewrite right bound
  have hright' : start + (p : ℝ) * step =
      ((Defs.F2R (Defs.FlocqFloat.mk ((m / p) + 1) (e + k) : Defs.FlocqFloat beta))) := by
    simpa [hglobR] using hF_right.symm
  -- Combine the two to rewrite `(F2R m/p).run + p*step` to `F2R (m/p+1)`
  have hsum :
      ((Defs.F2R (Defs.FlocqFloat.mk (m / p) (e + k) : Defs.FlocqFloat beta)))
        + (p : ℝ) * step
        = ((Defs.F2R (Defs.FlocqFloat.mk ((m / p) + 1) (e + k) : Defs.FlocqFloat beta))) := by
    simpa [hleft'.symm] using hright'
  -- Conclude by rewriting the postcondition in two steps to aid simplification
  have hpostR1 :
      inbetween
        ((Defs.F2R (Defs.FlocqFloat.mk (m / p) (e + k) : Defs.FlocqFloat beta)))
        (((Defs.F2R (Defs.FlocqFloat.mk (m / p) (e + k) : Defs.FlocqFloat beta)))
            + (p : ℝ) * step)
        x (Id.run (new_location (nb_steps := p) (k := (m % p)) l)) := by
    simpa [hleft'.symm, hp_def] using hpostR
  have hpostR2 :
      inbetween
        ((Defs.F2R (Defs.FlocqFloat.mk (m / p) (e + k) : Defs.FlocqFloat beta)))
        ((Defs.F2R (Defs.FlocqFloat.mk ((m / p) + 1) (e + k) : Defs.FlocqFloat beta)))
        x (Id.run (new_location (nb_steps := p) (k := (m % p)) l)) := by
    -- Rewrite the second bound using hsum
    rw [← hsum]
    exact hpostR1
  exact hpostR2

theorem inbetween_float_new_location_single
    (x : ℝ) (m e : Int) (l : Location)
    (hbeta : 1 < beta)
    (Hx : inbetween_float beta m e x l) :
    inbetween_float beta (m / beta) (e + 1) x
      (Id.run (new_location (nb_steps := beta) (k := (m % beta)) l)) := by
  -- Specialize the general step theorem with k = 1 and simplify.
  have hk : (0 : Int) < 1 := by decide
  have :=
    inbetween_float_new_location (beta := beta)
      (x := x) (m := m) (e := e) (l := l) (k := (1 : Int))
      (Hk := hk) (hbeta := hbeta) (Hx := Hx)
  -- Simplify β^|1| = β and m % (β^|1|) = m % β
  simpa [Int.natAbs, Int.natAbs_one, pow_one] using this

theorem inbetween_float_ex
    (m e : Int) (l : Location) (hbeta : 1 < beta) :
    ∃ x : ℝ, inbetween_float beta m e x l := by
  -- Let d and u be the consecutive float bounds around mantissa m
  let d : ℝ := ((Defs.F2R (Defs.FlocqFloat.mk m e : Defs.FlocqFloat beta)))
  let u : ℝ := ((Defs.F2R (Defs.FlocqFloat.mk (m + 1) e : Defs.FlocqFloat beta)))
  -- Show the interval is non-empty using 1 < beta ⇒ (beta : ℝ)^e > 0
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos_real : 0 < ((beta : Int) : ℝ) := by exact_mod_cast hbpos_int
  have hstep_pos : 0 < ((beta : ℝ) ^ e) := zpow_pos hbpos_real _
  have hm_lt_real : (m : ℝ) < (m + 1 : ℝ) := by
    have : (0 : ℝ) < 1 := by norm_num
    simpa [add_comm, add_left_comm, add_assoc]
      using (add_lt_add_left this (m : ℝ))
  have Hdu : d < u := by
    -- Multiply the integer inequality by the positive step
    have : (m : ℝ) * (beta : ℝ) ^ e < (m + 1 : ℝ) * (beta : ℝ) ^ e :=
      mul_lt_mul_of_pos_right hm_lt_real hstep_pos
    -- Rewrite in terms of F2R-based bounds d and u
    simpa [d, u, FloatSpec.Core.Defs.F2R, Int.cast_add, Int.cast_ofNat]
      using this
  -- Use the general existence result on real intervals and instantiate d,u
  -- Obtain a concrete witness x from the pure program
  let x := Id.run (inbetween_ex_witness d u l Hdu)
  -- Turn the Hoare-triple postcondition into a plain proposition
  have hx : inbetween d u x l := by
    -- Apply the triple with the precondition proof Hdu
    have htrip := inbetween_ex d u l Hdu
    simpa using htrip Hdu
  -- Conclude in terms of inbetween_float by unfolding d and u
  refine ⟨x, ?_⟩
  simpa [inbetween_float, d, u]
    using hx

theorem inbetween_float_unique
    (x : ℝ) (e m : Int) (l : Location) (m' : Int) (l' : Location)
    (H : inbetween_float beta m e x l)
    (H' : inbetween_float beta m' e x l')
    (hbeta : 1 < beta) :
    m = m' ∧ l = l' := by
  -- First, show m = m' using bounds and monotonicity of F2R in mantissa
  have Hb :=
    inbetween_float_bounds (beta := beta) (x := x) (m := m) (e := e) (l := l)
      (H := H) (hbeta := hbeta)
  have Hb' :=
    inbetween_float_bounds (beta := beta) (x := x) (m := m') (e := e) (l := l')
      (H := H') (hbeta := hbeta)
  -- From F2R(m,e) ≤ x < F2R(m'+1,e), deduce F2R(m,e) < F2R(m'+1,e)
  have hlt1 :
      ((Defs.F2R (Defs.FlocqFloat.mk m e : Defs.FlocqFloat beta)))
        < ((Defs.F2R (Defs.FlocqFloat.mk (m' + 1) e : Defs.FlocqFloat beta))) :=
    lt_of_le_of_lt Hb.1 Hb'.2
  -- Convert back to integers on mantissas
  have hm_lt : m < m' + 1 :=
    FloatSpec.Core.Float_prop.F2R_lt (beta := beta) (e := e) (m1 := m) (m2 := m' + 1)
      hbeta hlt1
  -- Symmetric inequality gives m' < m + 1
  have hlt2 :
      ((Defs.F2R (Defs.FlocqFloat.mk m' e : Defs.FlocqFloat beta)))
        < ((Defs.F2R (Defs.FlocqFloat.mk (m + 1) e : Defs.FlocqFloat beta))) :=
    lt_of_le_of_lt Hb'.1 Hb.2
  have hm'_lt : m' < m + 1 :=
    FloatSpec.Core.Float_prop.F2R_lt (beta := beta) (e := e) (m1 := m') (m2 := m + 1)
      hbeta hlt2
  -- Use Int.lt_add_one_iff to turn strict < into ≤ and deduce equality
  have hm_le : m ≤ m' := (Int.lt_add_one_iff).1 hm_lt
  have hm'_le : m' ≤ m := (Int.lt_add_one_iff).1 hm'_lt
  have hmeq : m = m' := le_antisymm hm_le hm'_le
  -- With equal mantissas, rewrite H' and use case analysis to show l = l'
  have H'' : inbetween_float beta m e x l' := by
    simpa [inbetween_float, hmeq] using H'
  -- Now both locations are for the same interval; reuse uniqueness by cases
  have hleq : l = l' := by
    -- Unfold the inbetween_float definition for direct case analysis
    dsimp [inbetween_float] at H H''
    cases H with
    | inbetween_Exact hxeq =>
        cases H'' with
        | inbetween_Exact _ =>
            rfl
        | inbetween_Inexact _ hbounds _ =>
            -- Contradiction: left bound says d < x but x = d
            have hcontr :
                ((Defs.F2R (Defs.FlocqFloat.mk m e : Defs.FlocqFloat beta)))
                  < ((Defs.F2R (Defs.FlocqFloat.mk m e : Defs.FlocqFloat beta))) := by
              simpa [hxeq]
                using hbounds.1
            exact (False.elim ((lt_irrefl _) hcontr))
    | inbetween_Inexact ord hbounds hcmp =>
        cases H'' with
        | inbetween_Exact hxeq =>
            -- Contradiction: left bound says d < x but x = d
            have hcontr :
                ((Defs.F2R (Defs.FlocqFloat.mk m e : Defs.FlocqFloat beta)))
                  < ((Defs.F2R (Defs.FlocqFloat.mk m e : Defs.FlocqFloat beta))) := by
              simpa [hxeq]
                using hbounds.1
            exact (False.elim ((lt_irrefl _) hcontr))
        | inbetween_Inexact ord' _ hcmp' =>
            -- Same midpoint, compare is deterministic ⇒ orderings equal
            have hord : ord = ord' := by
              -- Both hcmp and hcmp' have form `compare x mid = _`
              -- Use transitivity: ord = compare x mid = ord'
              have := hcmp.symm.trans hcmp'
              exact this
            simpa [hord]
  exact And.intro hmeq hleq

end ExtraCoqTheorems

end FloatSpec.Calc.Bracket
