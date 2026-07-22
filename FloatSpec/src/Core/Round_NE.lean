/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4, ported from Coq: https://flocq.gitlabpages.inria.fr/

Copyright (C) 2011-2018 Sylvie Boldo
Copyright (C) 2011-2018 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.

Rounding to nearest, ties to even: existence, unicity...
Based on flocq/src/Core/Round_NE.v
-/

import FloatSpec.src.Core.Zaux
import FloatSpecRoles
import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Round_pred
import FloatSpec.src.Core.Generic_fmt
import FloatSpec.src.Core.Float_prop
import FloatSpec.src.Core.Ulp
import FloatSpec.VersoExt
-- import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do
import FloatSpec.src.SimprocWP

open Real
open Std.Do
open FloatSpec.Core.Defs
open FloatSpec.Core.Round_pred
open FloatSpec.Core.Generic_fmt

namespace FloatSpec.Core.RoundNE

section NearestEvenRounding

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
variable [FloatSpec.Core.Generic_fmt.Monotone_exp fexp]

/-- Nearest-even rounding property

    Coq:
    Definition NE_prop (_ : R) f :=
      exists g : float beta, f = F2R g /\\ canonical g /\\ Z.even (Fnum g) = true.

    A tie-breaking rule that selects the value whose mantissa
    is even when two representable values are equidistant.
-/
def NE_prop (beta : Int) (fexp : Int → Int) (x : ℝ) (f : ℝ) : Prop :=
  ∃ g : FlocqFloat beta, f = (F2R g) ∧ canonical beta fexp g ∧ g.Fnum % 2 = 0

/-- Nearest-even rounding predicate

    Coq:
    Definition {name}`Rnd_NE_pt` :=
      {name (full := Round_pred.Rnd_NG_pt)}`Rnd_NG_pt` format {name}`NE_prop`.

    Combines nearest rounding with the even tie-breaking rule.
    This is the IEEE 754 default rounding mode.
-/
def Rnd_NE_pt : ℝ → ℝ → Prop :=
  FloatSpec.Core.Round_pred.Rnd_NG_pt (fun x => FloatSpec.Core.Generic_fmt.generic_format beta fexp x) (NE_prop beta fexp)

/-- Down-up parity property for positive numbers

    Coq:
    Definition DN_UP_parity_pos_prop :=
      forall x xd xu,
      (0 < x)%R ->
      ~ format x ->
      canonical xd ->
      canonical xu ->
      F2R xd = round beta fexp Zfloor x ->
      F2R xu = round beta fexp Zceil x ->
      Z.even (Fnum xu) = negb (Z.even (Fnum xd)).

    When a positive number is not exactly representable,
    its round-down and round-up values have mantissas of opposite parity.
    This ensures the nearest-even tie-breaking is well-defined.
-/
def DN_UP_parity_pos_prop : Prop :=
  ∀ x xd xu,
  0 < x →
  ¬FloatSpec.Core.Generic_fmt.generic_format beta fexp x →
  FloatSpec.Core.Round_pred.Rnd_DN_pt (fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y) x xd →
  FloatSpec.Core.Round_pred.Rnd_UP_pt (fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y) x xu →
  ∃ gd gu : FlocqFloat beta,
    xd = (F2R gd) ∧ xu = (F2R gu) ∧
    canonical beta fexp gd ∧ canonical beta fexp gu ∧
    gd.Fnum % 2 ≠ gu.Fnum % 2

end NearestEvenRounding

/-- Flocq `Round_NE.v`: class `Exists_NE`.

This is the extra exponent-format condition used by the nearest-even parity
proof. It is intentionally local to `Round_NE`: it is not a generic-format
fact, and the Coq theorem `DN_UP_parity_generic_pos` is stated under this
typeclass context.
-/
class Exists_NE (beta : Int) (fexp : Int → Int) : Prop where
  exists_ne :
    beta % 2 ≠ 0 ∨
      ∀ e : Int,
        (fexp e < e → fexp (e + 1) < e) ∧
        (e ≤ fexp e → fexp (fexp e + 1) = fexp e)

section ParityAuxiliary

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
variable [Exists_NE beta fexp]

/-- Parity property without sign restriction

    Like {name}`DN_UP_parity_pos_prop` but without the positivity assumption on x.

    Coq:
    ```
    Definition DN_UP_parity_prop :=
      forall x xd xu,
      ~ format x ->
      canonical xd ->
      canonical xu ->
      F2R xd = round beta fexp Zfloor x ->
      F2R xu = round beta fexp Zceil x ->
      Z.even (Fnum xu) = negb (Z.even (Fnum xd)).
    ```
-/
def DN_UP_parity_prop : Prop :=
  ∀ x xd xu,
  ¬FloatSpec.Core.Generic_fmt.generic_format beta fexp x →
  FloatSpec.Core.Round_pred.Rnd_DN_pt (fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y) x xd →
  FloatSpec.Core.Round_pred.Rnd_UP_pt (fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y) x xu →
  ∃ gd gu : FlocqFloat beta,
    xd = (F2R gd) ∧ xu = (F2R gu) ∧
    canonical beta fexp gd ∧ canonical beta fexp gu ∧
    gd.Fnum % 2 ≠ gu.Fnum % 2

/-- Check DN/UP parity auxiliary lemma -/
noncomputable def DN_UP_parity_aux_check : Bool :=
    @decide (DN_UP_parity_prop beta fexp) (Classical.dec _)

/-- Coq:
    Lemma DN_UP_parity_aux :
      DN_UP_parity_pos_prop ->
      DN_UP_parity_prop.

    Auxiliary lemma: parity for positives implies general parity via symmetry.
-/
theorem DN_UP_parity_aux :
    ⦃⌜beta > 1 ∧ DN_UP_parity_pos_prop beta fexp⌝⦄
    (pure (DN_UP_parity_aux_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hpre
  -- Extract the base precondition `beta > 1` and the positive-case parity property.
  rcases hpre with ⟨hβ, hpos_prop⟩
  simp [wp, PostCond.noThrow, pure]
  unfold DN_UP_parity_aux_check
  classical
  -- Reduce the Hoare triple on `Id` to a propositional goal about `decide`.
  -- It suffices to prove `DN_UP_parity_prop beta fexp`.
  simp [decide_eq_true_iff]
  -- Continue with the full constructive proof
  -- Unpack the precondition: base > 1 and the positive-case parity property.
  intro x xd xu hnotFmt hDN hUP
  -- We'll reason by cases on the sign of x.
  have htrich := lt_trichotomy (0 : ℝ) x
  -- Helper: format predicate for this file.
  let F := fun y : ℝ => FloatSpec.Core.Generic_fmt.generic_format beta fexp y
  have Fopp : ∀ y, F y → F (-y) :=
    by
      intro y hy
      -- `generic_format_opp` gives closure under negation.
      simpa using (FloatSpec.Core.Generic_fmt.generic_format_opp (beta := beta) (fexp := fexp) (x := y) hy)
  -- Case analysis on the sign of x
  rcases htrich with hpos | hzeq | hneg
  · -- 0 < x: apply the given positive parity hypothesis directly.
    -- The hypothesis provides the required canonical neighbors with opposite parity.
    -- `DN_UP_parity_pos_prop` is exactly the desired property under 0 < x.
    simpa using (hpos_prop x xd xu hpos hnotFmt hDN hUP)
  · -- x = 0: this contradicts `¬ format x`, as 0 is always representable.
    -- Hence the goal holds vacuously.
    exfalso
    have h0F : F 0 := by
      -- generic_format_0 ensures 0 is in format when beta > 1
      have h := FloatSpec.Core.Generic_fmt.generic_format_0 (beta := beta) (fexp := fexp) (hβ)
      -- The theorem above states `generic_format beta fexp 0`.
      simpa using h
    -- Rewrite x = 0 into the hypothesis and contradict using hnotFmt.
    exact hnotFmt (by simpa [hzeq] using h0F)
  · -- x < 0: reduce to the positive case on -x and transport the conclusion back.
    -- From x < 0, we have 0 < -x.
    have hpos' : 0 < -x := by simpa [neg_pos] using hneg
    -- Show that -x is not representable (otherwise x would be representable by symmetry).
    have hnotFmtNeg : ¬ F (-x) := by
      intro hFneg
      have hxF : F x := by
        -- Using closure under opposite in the other direction (apply to -x)
        have := Fopp (-x) hFneg
        simpa [neg_neg] using this
      exact hnotFmt hxF
    -- Build the dual rounding predicates at -x by unfolding definitions.
    -- From DN at x, we get UP at -x for -xd.
    have hUP_at_negx : FloatSpec.Core.Defs.Rnd_UP_pt F (-x) (-xd) := by
      -- Expand the definition and push negations through inequalities.
      rcases hDN with ⟨Hf, Hle, Hmax⟩
      refine And.intro (Fopp _ Hf) ?_
      refine And.intro (by simpa using (neg_le_neg Hle)) ?_
      intro g HgF hxle
      have h1 : -g ≤ x := by
        have := neg_le_neg hxle
        simpa [neg_neg] using this
      have Hnegg : F (-g) := Fopp _ HgF
      have h2 : -g ≤ xd := Hmax (-g) Hnegg h1
      have := neg_le_neg h2
      simpa [neg_neg] using this
    -- From UP at x, we get DN at -x for -xu.
    have hDN_at_negx : FloatSpec.Core.Defs.Rnd_DN_pt F (-x) (-xu) := by
      rcases hUP with ⟨Hf, hxle, Hmin⟩
      refine And.intro (Fopp _ Hf) ?_
      refine And.intro (by simpa using (neg_le_neg hxle)) ?_
      intro g HgF hgle
      have hx_le_negg : x ≤ -g := by
        have := neg_le_neg hgle
        simpa [neg_neg] using this
      have Hnegg : F (-g) := Fopp _ HgF
      have hf_le_negg : xu ≤ -g := Hmin (-g) Hnegg hx_le_negg
      -- Negate back to get g ≤ -xu
      have := neg_le_neg hf_le_negg
      simpa [neg_neg] using this
    -- Apply the positive-case property at -x with neighbors (-xu) and (-xd).
    rcases (hpos_prop)
      (-x) (-xu) (-xd) hpos' hnotFmtNeg hDN_at_negx hUP_at_negx with
      ⟨gd_pos, gu_pos, hxueq, hxdeq, hcanon_d, hcanon_u, hpar_pos⟩
    -- Transport back to x by negating the canonical floats.
    -- Define the floats for x so that their real values equal xd and xu respectively.
    refine ?_
    -- Candidate floats for x
    let gd : FlocqFloat beta := ⟨-gu_pos.Fnum, gu_pos.Fexp⟩
    let gu : FlocqFloat beta := ⟨-gd_pos.Fnum, gd_pos.Fexp⟩
    -- Show xd = F2R gd and xu = F2R gu using F2R_Zopp.
    have hxd : xd = (F2R gd) := by
      -- From hxdeq: (-xd) = (F2R gu_pos).run
      -- So xd = -(F2R gu_pos).run = (F2R gd).run via F2R_Zopp
      have hx' : -(F2R gu_pos) = (F2R gd) := by
        have := FloatSpec.Core.Float_prop.F2R_Zopp (beta := beta) (f := gu_pos) (hbeta := hβ)
        exact this
      have hneg : xd = -(F2R gu_pos) := by
        have h := congrArg Neg.neg hxdeq
        simpa using h
      calc xd = -(F2R gu_pos) := hneg
           _ = (F2R gd) := hx'
    have hxu : xu = (F2R gu) := by
      -- From hxueq: (-xu) = (F2R gd_pos).run
      have hx' : -(F2R gd_pos) = (F2R gu) := by
        have := FloatSpec.Core.Float_prop.F2R_Zopp (beta := beta) (f := gd_pos) (hbeta := hβ)
        exact this
      have hneg : xu = -(F2R gd_pos) := by
        have h := congrArg Neg.neg hxueq
        simpa using h
      calc xu = -(F2R gd_pos) := hneg
           _ = (F2R gu) := hx'
    -- Canonicality is preserved under mantissa negation.
    have hcanon_gd : canonical beta fexp gd := by
      -- Use `canonical_opp` from Generic_fmt
      exact FloatSpec.Core.Generic_fmt.canonical_opp (beta := beta) (fexp := fexp) (m := gu_pos.Fnum) (e := gu_pos.Fexp) hcanon_u
    have hcanon_gu : canonical beta fexp gu := by
      exact FloatSpec.Core.Generic_fmt.canonical_opp (beta := beta) (fexp := fexp) (m := gd_pos.Fnum) (e := gd_pos.Fexp) hcanon_d
    -- Parity of the mantissa is invariant under negation modulo 2.
    -- We prove `(-n) % 2 = n % 2` by case-splitting on `n % 2 ∈ {0,1}`.
    have neg_mod_two (n : Int) : (-n) % 2 = n % 2 := by
      -- Using that the remainder mod 2 is either 0 or 1.
      rcases Int.emod_two_eq_zero_or_one n with hn0 | hn1
      · -- n % 2 = 0 ⇒ (-n) % 2 = 0 as well
        have : (-n) % 2 = 0 := by
          -- remainder flips sign then normalizes to {0,1}; with 0 it stays 0
          rcases Int.emod_two_eq_zero_or_one (-n) with hneg0 | hneg1
          · exact hneg0
          · -- impossible branch under parity constraints; eliminate via rewriting by contradiction
            -- combine with hn0 to discharge this branch succinctly
            exact False.elim (by
              -- rewrite goal to 1 = 0 and close by no-confusion
              have : (1 : Int) ≠ 0 := by decide
              exact this (by simpa [hn0] using hneg1))
        simp [hn0, this]
      · -- n % 2 = 1 ⇒ (-n) % 2 = 1
        have : (-n) % 2 = 1 := by
          rcases Int.emod_two_eq_zero_or_one (-n) with hneg0 | hneg1
          · -- cannot have 0 here; discharge as above
            exact False.elim (by
              have : (0 : Int) ≠ 1 := by decide
              exact this (by simpa [hn1] using hneg0))
          · exact hneg1
        simp [hn1, this]
    -- Now convert the parity inequality through negation using the lemma.
    have hparity' : gd.Fnum % 2 ≠ gu.Fnum % 2 := by
      -- gd.Fnum = -gu_pos.Fnum, gu.Fnum = -gd_pos.Fnum
      change (-gu_pos.Fnum) % 2 ≠ (-gd_pos.Fnum) % 2
      -- Rewrite both sides using `neg_mod_two`.
      -- Note the sides are swapped compared to `hpar_pos`; use symmetry on `≠`.
      have hpar_pos' : gu_pos.Fnum % 2 ≠ gd_pos.Fnum % 2 := ne_comm.mp hpar_pos
      simpa [neg_mod_two] using hpar_pos'
    -- Assemble the final witnesses.
    refine ⟨gd, gu, hxd, hxu, hcanon_gd, hcanon_gu, hparity'⟩

/-- Check DN/UP parity holds for the generic format (positive case) -/
noncomputable def DN_UP_parity_generic_pos_check : Bool :=
    @decide (DN_UP_parity_pos_prop beta fexp) (Classical.dec _)


/-- Parity flips on successors. -/
private theorem parity_succ_flip (n : Int) : n % 2 ≠ (n + 1) % 2 := by
  -- Use `(n+1) % 2 = ((n % 2) + (1 % 2)) % 2` and case on `n % 2`.
  have hadd : (n + 1) % 2 = ((n % 2) + (1 % 2)) % 2 := by
    simpa using (Int.add_emod n 1 2)
  have h1mod : (1 % 2 : Int) = 1 := by decide
  rcases Int.emod_two_eq_zero_or_one n with hn0 | hn1
  · -- n even ⇒ (n+1) odd
    -- Rewrite using the additive rule and evaluate the small constants
    have : (n + 1) % 2 = 1 := by
      simpa [hadd, hn0, h1mod] using (rfl : ((0 + 1) % 2 : Int) = 1)
    simpa [hn0, this]
  · -- n odd ⇒ (n+1) even
    have h2mod : (2 % 2 : Int) = 0 := by decide
    have : (n + 1) % 2 = 0 := by
      -- ((1 + 1) % 2) = 0
      simpa [hadd, hn1, h1mod, h2mod, Int.cast_ofNat] using (rfl : ((1 + 1) % 2 : Int) = 0)
    simpa [hn1, this]

/-- Parity flips when subtracting one. -/
private theorem parity_pred_flip (n : Int) : (n - 1) % 2 ≠ n % 2 := by
  have h := parity_succ_flip (n - 1)
  simpa using h

/-- The `Ulp` file has a local non-FTZ class. In the current Lean port,
`Round_NE` already carries the standard monotonicity assumption on `fexp`, and
the same Flocq argument gives `Exp_not_FTZ`: in the large regime monotonicity
applies to `fexp e + 1 ≤ e`; in the small regime `Valid_exp` gives constancy.
-/
private theorem monotone_exp_to_ulp_not_FTZ
    (beta : Int) (fexp : Int → Int)
    [Valid_exp beta fexp] [FloatSpec.Core.Generic_fmt.Monotone_exp fexp] :
    FloatSpec.Core.Ulp.Exp_not_FTZ fexp := by
  classical
  refine ⟨?_⟩
  intro e
  by_cases hlarge : fexp e < e
  · have hle : fexp e + 1 ≤ e := (Int.add_one_le_iff).mpr hlarge
    exact FloatSpec.Core.Generic_fmt.Monotone_exp.mono (fexp := fexp) hle
  · have hsmall : e ≤ fexp e := le_of_not_gt hlarge
    exact (Valid_exp.valid_exp (beta := beta) (fexp := fexp) e).right hsmall |>.left

/-- Pure uniqueness for down-rounding points. -/
private theorem Rnd_DN_pt_unique_pure (F : ℝ → Prop) (x f₁ f₂ : ℝ)
    (h₁ : FloatSpec.Core.Round_pred.Rnd_DN_pt F x f₁)
    (h₂ : FloatSpec.Core.Round_pred.Rnd_DN_pt F x f₂) : f₁ = f₂ := by
  rcases h₁ with ⟨F₁, h₁le, h₁max⟩
  rcases h₂ with ⟨F₂, h₂le, h₂max⟩
  exact le_antisymm (h₂max f₁ F₁ h₁le) (h₁max f₂ F₂ h₂le)

/-- Concrete integer rounding produces a generic-format value. -/
private theorem roundR_format_int
    (beta : Int) (fexp : Int → Int)
    [Valid_exp beta fexp] (rnd : ℝ → Int) [Valid_rnd rnd]
    (x : ℝ) (hβ : 1 < beta) :
    generic_format beta fexp (roundR beta fexp rnd x) := by
  classical
  have hpos_format :
      ∀ (rnd' : ℝ → Int), [Valid_rnd rnd'] → ∀ y : ℝ, 0 ≤ y →
        generic_format beta fexp (roundR beta fexp rnd' y) := by
    intro rnd' _ y hy_nonneg
    by_cases hy0 : y = 0
    · have hrnd0 : rnd' (0 : ℝ) = (0 : Int) := by
        simpa using (Valid_rnd.Zrnd_IZR (rnd := rnd') (0 : Int))
      have hround0 : roundR beta fexp rnd' y = 0 := by
        simp [hy0, roundR, scaled_mantissa, hrnd0]
      simpa [hround0] using generic_format_0_run (beta := beta) (fexp := fexp)
    · have hy_pos : 0 < y := lt_of_le_of_ne hy_nonneg (Ne.symm hy0)
      set ex : Int := FloatSpec.Core.Raux.mag beta y with hex
      set c : Int := fexp ex with hc
      set sm : ℝ := scaled_mantissa beta fexp y with hsm
      set r : ℝ := roundR beta fexp rnd' y with hr
      have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
      have hpow_pos : 0 < (beta : ℝ) ^ (ex - 1) := by
        exact zpow_pos (by exact_mod_cast hbposℤ) _
      have hlow : (beta : ℝ) ^ (ex - 1) ≤ y := by
        have htrip := FloatSpec.Core.Raux.mag_lower_bound (beta := beta) (x := y) hβ hy0
        simpa [FloatSpec.Core.Raux.abs_val, abs_of_nonneg hy_nonneg, hex, wp,
          PostCond.noThrow, Id.run, pure] using htrip True.intro
      have hhigh : y < (beta : ℝ) ^ ex := by
        have htrip := FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := y) hβ hy0
        simpa [FloatSpec.Core.Raux.abs_val, abs_of_nonneg hy_nonneg, hex, wp,
          PostCond.noThrow, Id.run, pure] using htrip True.intro
      have hcexp_y : cexp beta fexp y = c := by
        simpa [cexp, hex.symm, hc]
      have hsm_y : scaled_mantissa beta fexp y = sm := by simpa using hsm.symm
      have hr_eval : r = ((rnd' sm : Int) : ℝ) * (beta : ℝ) ^ c := by
        simpa [r, hr, roundR, hsm_y, hcexp_y]
      by_cases hsmall : ex ≤ fexp ex
      · have hround :=
          roundR_bounded_small_pos (beta := beta) (fexp := fexp) (rnd := rnd')
            (x := y) (ex := ex) ⟨hlow, hhigh⟩ hsmall hβ
        have hround_r : r = 0 ∨ r = (beta : ℝ) ^ (fexp ex) := by
          simpa [r, hr] using hround
        rcases hround_r with hr0 | hrpow
        · simpa [hr0] using generic_format_0_run (beta := beta) (fexp := fexp)
        · have hfexp_self : fexp (fexp ex) ≤ fexp ex := by
            have hpair := Valid_exp.valid_exp (beta := beta) (fexp := fexp) ex
            have hconst := (hpair.right hsmall).right
            have heq : fexp (fexp ex) = fexp ex := hconst (fexp ex) le_rfl
            exact le_of_eq heq
          have hgen := generic_format_bpow' (beta := beta) (fexp := fexp)
            (e := fexp ex) ⟨hβ, hfexp_self⟩
          have hgen_run : generic_format beta fexp ((beta : ℝ) ^ (fexp ex)) := by
            simpa [wp, PostCond.noThrow, Id.run, pure] using hgen
          simpa [hrpow] using hgen_run
      · have hlarge : fexp ex < ex := lt_of_not_ge hsmall
        have hround :=
          roundR_bounded_large_pos (beta := beta) (fexp := fexp) (rnd := rnd')
            (x := y) (ex := ex) ⟨hlow, hhigh⟩ hlarge hβ
        have hr_low : (beta : ℝ) ^ (ex - 1) ≤ r := by simpa [r, hr] using hround.left
        have hr_high : r ≤ (beta : ℝ) ^ ex := by simpa [r, hr] using hround.right
        rcases lt_or_eq_of_le hr_high with hr_lt | hr_eq_pow
        · have hr_pos : 0 < r := lt_of_lt_of_le hpow_pos hr_low
          have hmag_r : FloatSpec.Core.Raux.mag beta r = ex := by
            have hr_low_abs : (beta : ℝ) ^ (ex - 1) ≤ |r| := by
              simpa [abs_of_pos hr_pos] using hr_low
            have hr_lt_abs : |r| < (beta : ℝ) ^ ex := by
              simpa [abs_of_pos hr_pos] using hr_lt
            have htrip := FloatSpec.Core.Raux.mag_unique
              (beta := beta) (x := r) (e := ex) hβ hr_low_abs hr_lt_abs
            simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
          have hfmt_float :
              generic_format beta fexp
                (F2R (FlocqFloat.mk (rnd' sm) c : FlocqFloat beta)) := by
            have htrip := generic_format_F2R (beta := beta) (fexp := fexp)
              (m := rnd' sm) (e := c)
            have hbound :
                (rnd' sm ≠ 0 →
                  cexp beta fexp (F2R (FlocqFloat.mk (rnd' sm) c : FlocqFloat beta)) ≤ c) := by
              intro _
              have hF2R_eq :
                  F2R (FlocqFloat.mk (rnd' sm) c : FlocqFloat beta) = r := by
                simpa [FloatSpec.Core.Defs.F2R] using hr_eval.symm
              have hcexp_r : cexp beta fexp r = c := by
                simpa [cexp, hmag_r, hc]
              rw [hF2R_eq, hcexp_r]
            have hres := htrip ⟨hβ, hbound⟩
            simpa [wp, PostCond.noThrow, Id.run, pure] using hres
          have hF2R_eq : F2R (FlocqFloat.mk (rnd' sm) c : FlocqFloat beta) = r := by
            simpa [FloatSpec.Core.Defs.F2R] using hr_eval.symm
          have hF2R_eq' : ((rnd' sm : Int) : ℝ) * (beta : ℝ) ^ c = r := by
            simpa [FloatSpec.Core.Defs.F2R] using hF2R_eq
          simpa [hF2R_eq'] using hfmt_float
        · have hc_le_ex : fexp ex ≤ ex := le_of_lt hlarge
          have hgen := generic_format_bpow' (beta := beta) (fexp := fexp)
            (e := ex) ⟨hβ, hc_le_ex⟩
          have hgen_run : generic_format beta fexp ((beta : ℝ) ^ ex) := by
            simpa [wp, PostCond.noThrow, Id.run, pure] using hgen
          simpa [hr_eq_pow] using hgen_run
  by_cases hx_nonneg : 0 ≤ x
  · exact hpos_format rnd x hx_nonneg
  · have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
    have hx_pos_neg : 0 ≤ -x := le_of_lt (neg_pos.mpr hx_neg)
    haveI : Valid_rnd (Zrnd_opp rnd) := inferInstance
    have hneg_fmt :
        generic_format beta fexp (roundR beta fexp (Zrnd_opp rnd) (-x)) :=
      hpos_format (Zrnd_opp rnd) (-x) hx_pos_neg
    have hopp : roundR beta fexp rnd x =
        - roundR beta fexp (Zrnd_opp rnd) (-x) := by
      have h := roundR_opp (beta := beta) (fexp := fexp) (rnd := rnd) (x := -x) hβ
      simpa [neg_neg] using h
    have hfmt_opp := generic_format_opp (beta := beta) (fexp := fexp)
      (x := roundR beta fexp (Zrnd_opp rnd) (-x)) hneg_fmt
    simpa [hopp] using hfmt_opp

/-- Concrete floor rounding is the Flocq DN point for the generic format. -/
private theorem roundR_floor_DN_pt
    (beta : Int) (fexp : Int → Int)
    [Valid_exp beta fexp]
    (x : ℝ) (hβ : 1 < beta) :
    FloatSpec.Core.Round_pred.Rnd_DN_pt
      (fun y => generic_format beta fexp y) x
      (roundR beta fexp rnd_floor x) := by
  classical
  refine ⟨?hfmt, ?hle, ?hmax⟩
  · exact roundR_format_int (beta := beta) (fexp := fexp) (rnd := rnd_floor)
      (x := x) hβ
  · have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    set e : Int := cexp beta fexp x with he
    set sm : ℝ := scaled_mantissa beta fexp x with hsm
    have hfloor_le : ((rnd_floor sm : Int) : ℝ) ≤ sm := by
      simpa [rnd_floor, FloatSpec.Core.Raux.Zfloor] using (Int.floor_le sm)
    have hmul := mul_le_mul_of_nonneg_right hfloor_le
      (le_of_lt (zpow_pos hbposR e))
    have hscaled : sm * (beta : ℝ) ^ e = x := by
      have htrip := scaled_mantissa_mult_bpow (beta := beta) (fexp := fexp) (x := x)
      simpa [wp, PostCond.noThrow, Id.run, pure, sm, hsm, e, he] using htrip hβ
    have hdn_eval :
        roundR beta fexp rnd_floor x = ((rnd_floor sm : Int) : ℝ) * (beta : ℝ) ^ e := by
      simpa [roundR, sm, hsm, e, he]
    calc
      roundR beta fexp rnd_floor x
          = ((rnd_floor sm : Int) : ℝ) * (beta : ℝ) ^ e := hdn_eval
      _ ≤ sm * (beta : ℝ) ^ e := hmul
      _ = x := hscaled
  · intro g hgF hg_le
    exact roundR_ge_generic (beta := beta) (fexp := fexp) (rnd := rnd_floor)
      (x := g) (y := x) hβ hgF hg_le

/-- Concrete ceil rounding is the Flocq UP point for the generic format. -/
private theorem roundR_ceil_UP_pt
    (beta : Int) (fexp : Int → Int)
    [Valid_exp beta fexp]
    (x : ℝ) (hβ : 1 < beta) :
    FloatSpec.Core.Round_pred.Rnd_UP_pt
      (fun y => generic_format beta fexp y) x
      (roundR beta fexp rnd_ceil x) := by
  classical
  refine ⟨?hfmt, ?hle, ?hmin⟩
  · exact roundR_format_int (beta := beta) (fexp := fexp) (rnd := rnd_ceil)
      (x := x) hβ
  · have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    set e : Int := cexp beta fexp x with he
    set sm : ℝ := scaled_mantissa beta fexp x with hsm
    have hceil_ge : sm ≤ ((rnd_ceil sm : Int) : ℝ) := by
      simpa [rnd_ceil, FloatSpec.Core.Raux.Zceil] using (Int.le_ceil sm)
    have hmul := mul_le_mul_of_nonneg_right hceil_ge
      (le_of_lt (zpow_pos hbposR e))
    have hscaled : sm * (beta : ℝ) ^ e = x := by
      have htrip := scaled_mantissa_mult_bpow (beta := beta) (fexp := fexp) (x := x)
      simpa [wp, PostCond.noThrow, Id.run, pure, sm, hsm, e, he] using htrip hβ
    have hup_eval :
        roundR beta fexp rnd_ceil x = ((rnd_ceil sm : Int) : ℝ) * (beta : ℝ) ^ e := by
      simpa [roundR, sm, hsm, e, he]
    calc
      x = sm * (beta : ℝ) ^ e := hscaled.symm
      _ ≤ ((rnd_ceil sm : Int) : ℝ) * (beta : ℝ) ^ e := hmul
      _ = roundR beta fexp rnd_ceil x := hup_eval.symm
  · intro g hgF hx_le_g
    exact roundR_le_generic (beta := beta) (fexp := fexp) (rnd := rnd_ceil)
      (x := x) (y := g) hβ hgF hx_le_g

/-- Flocq-aligned bridge from arbitrary DN/UP witnesses to the ULP gap.

`Ulp.round_UP_DN_ulp` is stated for the chosen DN/UP rounders. This lemma
transports it to the point predicates used by `Round_NE` via DN/UP uniqueness.
-/
private theorem DN_UP_gap_of_not_format
    (beta : Int) (fexp : Int → Int)
    [Valid_exp beta fexp] [FloatSpec.Core.Generic_fmt.Monotone_exp fexp]
    (x xd xu : ℝ) (hβ : 1 < beta)
    (hnotFmt : ¬ generic_format beta fexp x)
    (hDN : FloatSpec.Core.Round_pred.Rnd_DN_pt
      (fun y => generic_format beta fexp y) x xd)
    (hUP : FloatSpec.Core.Round_pred.Rnd_UP_pt
      (fun y => generic_format beta fexp y) x xu) :
    xu = xd + FloatSpec.Core.Ulp.ulp beta fexp x := by
  classical
  haveI : FloatSpec.Core.Ulp.Exp_not_FTZ fexp :=
    monotone_exp_to_ulp_not_FTZ (beta := beta) (fexp := fexp)
  let F : ℝ → Prop := fun y => generic_format beta fexp y
  have hDN_chosen :
      FloatSpec.Core.Round_pred.Rnd_DN_pt F x
        (round_DN_to_format beta fexp x hβ) := by
    have h := (Classical.choose_spec
      (round_DN_exists (beta := beta) (fexp := fexp) (x := x) (hβ := hβ))).2
    simpa [F, round_DN_to_format] using h
  have hUP_chosen :
      FloatSpec.Core.Round_pred.Rnd_UP_pt F x
        (round_UP_to_format beta fexp x hβ) := by
    have h := (Classical.choose_spec
      (round_UP_exists (beta := beta) (fexp := fexp) (x := x) (hβ := hβ))).2
    simpa [F, round_UP_to_format] using h
  have hxd :
      xd = round_DN_to_format beta fexp x hβ := by
    exact Rnd_DN_pt_unique_pure F x xd
      (round_DN_to_format beta fexp x hβ) (by simpa [F] using hDN) hDN_chosen
  have hxu :
      xu = round_UP_to_format beta fexp x hβ := by
    exact FloatSpec.Core.Round_pred.Rnd_UP_pt_unique_pure F x xu
      (round_UP_to_format beta fexp x hβ) (by simpa [F] using hUP) hUP_chosen
  have hgap := FloatSpec.Core.Ulp.round_UP_DN_ulp
    (beta := beta) (fexp := fexp) (x := x) hnotFmt hβ
  have hgap_run :
      round_UP_to_format beta fexp x hβ =
        round_DN_to_format beta fexp x hβ + FloatSpec.Core.Ulp.ulp beta fexp x := by
    simpa [wp, PostCond.noThrow, Id.run, bind, pure]
      using hgap True.intro
  simpa [hxd, hxu] using hgap_run

/-- Same-canonical-exponent arithmetic: if two canonical endpoints are separated
by exactly one unit at their common exponent, their mantissas are consecutive.
-/
private theorem canonical_mantissa_succ_of_same_exp_gap
    (beta : Int) (fexp : Int → Int) (gd gu : FlocqFloat beta)
    (hβ : 1 < beta)
    (hgap :
      F2R gu = F2R gd + (beta : ℝ) ^ gd.Fexp)
    (hexp : gu.Fexp = gd.Fexp) :
    gu.Fnum = gd.Fnum + 1 := by
  cases gd with
  | mk md ed =>
  cases gu with
  | mk mu eu =>
  simp only [FlocqFloat.mk.injEq] at hexp
  subst eu
  unfold F2R at hgap
  have hbpos : (0 : ℝ) < (beta : ℝ) := by
    exact_mod_cast (lt_trans Int.zero_lt_one hβ)
  have hpow_ne : (beta : ℝ) ^ ed ≠ 0 := zpow_ne_zero ed (ne_of_gt hbpos)
  have hcast : (mu : ℝ) = (md : ℝ) + 1 := by
    have h := congrArg (fun t : ℝ => t * ((beta : ℝ) ^ ed)⁻¹) hgap
    have hleft : (mu : ℝ) * (beta : ℝ) ^ ed * ((beta : ℝ) ^ ed)⁻¹ = (mu : ℝ) := by
      field_simp [hpow_ne]
    have hright :
        ((md : ℝ) * (beta : ℝ) ^ ed + (beta : ℝ) ^ ed)
            * ((beta : ℝ) ^ ed)⁻¹ = (md : ℝ) + 1 := by
      calc
        ((md : ℝ) * (beta : ℝ) ^ ed + (beta : ℝ) ^ ed)
            * ((beta : ℝ) ^ ed)⁻¹
            = ((md : ℝ) + 1) * ((beta : ℝ) ^ ed * ((beta : ℝ) ^ ed)⁻¹) := by ring
        _ = ((md : ℝ) + 1) * 1 := by simp [hpow_ne]
        _ = (md : ℝ) + 1 := by ring
    simpa [hleft, hright] using h
  exact Int.cast_injective (by simpa [Int.cast_add, Int.cast_one] using hcast)

/-- Same-exponent one-ULP gaps imply opposite parity. -/
private theorem canonical_parity_of_same_exp_gap
    (beta : Int) (fexp : Int → Int) (gd gu : FlocqFloat beta)
    (hβ : 1 < beta)
    (hgap :
      F2R gu = F2R gd + (beta : ℝ) ^ gd.Fexp)
    (hexp : gu.Fexp = gd.Fexp) :
    gd.Fnum % 2 ≠ gu.Fnum % 2 := by
  have hsucc := canonical_mantissa_succ_of_same_exp_gap
    (beta := beta) (fexp := fexp) (gd := gd) (gu := gu) hβ hgap hexp
  simpa [hsucc] using parity_succ_flip gd.Fnum

/-- Integer parity helper used by the `Exists_NE` odd-radix branch. -/
private theorem int_pow_odd_mod_two {b : Int} (n : Nat) (hb : b % 2 ≠ 0) :
    (b ^ n) % 2 ≠ 0 := by
  have hb1 : b % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one b with hb0 | hb1
    · exact False.elim (hb hb0)
    · exact hb1
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      have hmul : (b ^ (Nat.succ n)) % 2 = ((b % 2) * ((b ^ n) % 2)) % 2 := by
        simpa [pow_succ, mul_comm] using (Int.mul_emod b (b ^ n) 2)
      have ih1 : (b ^ n) % 2 = 1 := by
        rcases Int.emod_two_eq_zero_or_one (b ^ n) with h0 | h1
        · exact False.elim (ih h0)
        · exact h1
      intro hzero
      have : (1 : Int) = 0 := by
        simpa [hmul, hb1, ih1] using hzero
      norm_num at this

/-- Positive powers have the same parity as the base. -/
private theorem int_pow_pos_mod_two_eq_base (b : Int) {n : Nat} (hn : 0 < n) :
    (b ^ n) % 2 = b % 2 := by
  rcases Int.emod_two_eq_zero_or_one b with hb0 | hb1
  · rcases n with _ | k
    · cases hn
    · have hmul : (b ^ Nat.succ k) % 2 = ((b % 2) * ((b ^ k) % 2)) % 2 := by
        simpa [pow_succ, mul_comm] using (Int.mul_emod b (b ^ k) 2)
      simpa [hb0, hmul]
  · have hbodd : b % 2 ≠ 0 := by simpa [hb1]
    have hpodd := int_pow_odd_mod_two (b := b) n hbodd
    rcases Int.emod_two_eq_zero_or_one (b ^ n) with hp0 | hp1
    · exact False.elim (hpodd hp0)
    · simpa [hb1, hp1]

/-- Cancel a common radix scale from an equality `m * β^c = β^e`. -/
private theorem scaled_int_eq_power_mantissa
    (beta m c e : Int) (hβ : 1 < beta) (hce : c ≤ e)
    (hval : (m : ℝ) * (beta : ℝ) ^ c = (beta : ℝ) ^ e) :
    m = beta ^ ((e - c).natAbs) := by
  have hbpow := FloatSpec.Core.Float_prop.F2R_bpow
    (beta := beta) (e := e) hβ
  have hchange := FloatSpec.Core.Float_prop.F2R_change_exp
    (beta := beta) (f := (FlocqFloat.mk 1 e : FlocqFloat beta))
    (e' := c) hβ hce
  have hsame :
      F2R (FlocqFloat.mk m c : FlocqFloat beta) =
        F2R (FlocqFloat.mk (beta ^ ((e - c).natAbs)) c : FlocqFloat beta) := by
    calc
      F2R (FlocqFloat.mk m c : FlocqFloat beta)
          = (beta : ℝ) ^ e := by simpa [F2R] using hval
      _ = F2R (FlocqFloat.mk 1 e : FlocqFloat beta) := hbpow.symm
      _ = F2R (FlocqFloat.mk
            ((1 : Int) * beta ^ ((e - c).natAbs)) c : FlocqFloat beta) := hchange
      _ = F2R (FlocqFloat.mk (beta ^ ((e - c).natAbs)) c : FlocqFloat beta) := by simp
  unfold F2R at hsame
  have hbpos : (0 : ℝ) < (beta : ℝ) := by
    exact_mod_cast (lt_trans Int.zero_lt_one hβ)
  have hpow_ne : (beta : ℝ) ^ c ≠ 0 := zpow_ne_zero c (ne_of_gt hbpos)
  exact Int.cast_injective (mul_right_cancel₀ hpow_ne hsame)

/-- A canonical float representing the exact power `β^e` has the expected
mantissa after changing the power float to the canonical exponent. -/
private theorem canonical_power_mantissa
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (g : FlocqFloat beta) (e : Int) (hβ : 1 < beta)
    (hcan : canonical beta fexp g)
    (hg : F2R g = (beta : ℝ) ^ e) :
    g.Fnum = beta ^ ((e - g.Fexp).natAbs) := by
  classical
  have hmag_pow : FloatSpec.Core.Raux.mag beta ((beta : ℝ) ^ e) = e + 1 := by
    have htrip := FloatSpec.Core.Raux.mag_bpow (beta := beta) (e := e) hβ
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hgexp : g.Fexp = fexp (e + 1) := by
    unfold canonical at hcan
    have hmag_g : FloatSpec.Core.Raux.mag beta (F2R g) = e + 1 := by
      rw [hg]
      exact hmag_pow
    rwa [hmag_g] at hcan
  have hfmt_pow : generic_format beta fexp ((beta : ℝ) ^ e) := by
    have hfmt_g := generic_format_canonical (beta := beta) (fexp := fexp) (f := g) hcan
    rwa [hg] at hfmt_g
  have hfe : fexp e ≤ e :=
    generic_format_bpow_inv' (beta := beta) (fexp := fexp) (e := e) hβ hfmt_pow
  have hfe1 : fexp (e + 1) ≤ e := by
    have hpair := Valid_exp.valid_exp (beta := beta) (fexp := fexp) e
    by_cases hlt : fexp e < e
    · exact hpair.left hlt
    · have heq : fexp e = e := le_antisymm hfe (le_of_not_gt hlt)
      have hsmall : e ≤ fexp e := by simpa [heq]
      have hbound := (hpair.right hsmall).left
      simpa [heq] using hbound
  have hgle : g.Fexp ≤ e := by simpa [hgexp] using hfe1
  have hchange := FloatSpec.Core.Float_prop.F2R_change_exp
    (beta := beta) (f := (FlocqFloat.mk 1 e : FlocqFloat beta))
    (e' := g.Fexp) hβ hgle
  have hbpow := FloatSpec.Core.Float_prop.F2R_bpow
    (beta := beta) (e := e) hβ
  have hsame :
      F2R g =
        F2R (FlocqFloat.mk (beta ^ ((e - g.Fexp).natAbs)) g.Fexp : FlocqFloat beta) := by
    calc
      F2R g = (beta : ℝ) ^ e := hg
      _ = F2R (FlocqFloat.mk 1 e : FlocqFloat beta) := hbpow.symm
      _ = F2R (FlocqFloat.mk
            ((1 : Int) * beta ^ ((e - g.Fexp).natAbs)) g.Fexp : FlocqFloat beta) := hchange
      _ = F2R (FlocqFloat.mk
            (beta ^ ((e - g.Fexp).natAbs)) g.Fexp : FlocqFloat beta) := by simp
  cases g with
  | mk m ge =>
      simp only [FlocqFloat.Fnum, FlocqFloat.Fexp] at hsame ⊢
      unfold F2R at hsame
      have hbpos : (0 : ℝ) < (beta : ℝ) := by
        exact_mod_cast (lt_trans Int.zero_lt_one hβ)
      have hpow_ne : (beta : ℝ) ^ ge ≠ 0 := zpow_ne_zero ge (ne_of_gt hbpos)
      have hcast : (m : ℝ) = (beta ^ ((e - ge).natAbs) : Int) := by
        exact mul_right_cancel₀ hpow_ne hsame
      exact Int.cast_injective hcast

/-- Canonical exponent of a canonical float representing `β^e`. -/
private theorem canonical_power_exp
    (beta : Int) (fexp : Int → Int)
    (g : FlocqFloat beta) (e : Int) (hβ : 1 < beta)
    (hcan : canonical beta fexp g)
    (hg : F2R g = (beta : ℝ) ^ e) :
    g.Fexp = fexp (e + 1) := by
  have hmag_pow : FloatSpec.Core.Raux.mag beta ((beta : ℝ) ^ e) = e + 1 := by
    have htrip := FloatSpec.Core.Raux.mag_bpow (beta := beta) (e := e) hβ
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
  unfold canonical at hcan
  have hmag_g : FloatSpec.Core.Raux.mag beta (F2R g) = e + 1 := by
    rw [hg]
    exact hmag_pow
  rwa [hmag_g] at hcan

/-- A canonical float whose value is zero has zero mantissa. -/
private theorem canonical_zero_mantissa
    (beta : Int) (fexp : Int → Int)
    (g : FlocqFloat beta) (hβ : 1 < beta)
    (hg : F2R g = 0) :
    g.Fnum = 0 :=
  FloatSpec.Core.Float_prop.eq_0_F2R (beta := beta) g hβ hg

/-- If a float value is written at its own exponent, the mantissa is unique. -/
private theorem same_exp_mantissa
    (beta : Int) (g : FlocqFloat beta) (m e : Int) (hβ : 1 < beta)
    (hexp : g.Fexp = e)
    (hval : F2R g = (m : ℝ) * (beta : ℝ) ^ e) :
    g.Fnum = m := by
  cases g with
  | mk mg eg =>
      simp only [FlocqFloat.Fnum, FlocqFloat.Fexp] at hexp ⊢
      subst eg
      unfold F2R at hval
      have hbpos : (0 : ℝ) < (beta : ℝ) := by
        exact_mod_cast (lt_trans Int.zero_lt_one hβ)
      have hpow_ne : (beta : ℝ) ^ e ≠ 0 := zpow_ne_zero e (ne_of_gt hbpos)
      exact Int.cast_injective (mul_right_cancel₀ hpow_ne hval)

/-- Coq:
    Theorem DN_UP_parity_generic_pos :
      DN_UP_parity_pos_prop.

    Parity of down/up rounded neighbors differs when x > 0 and not representable.
-/
theorem DN_UP_parity_generic_pos :
    ⦃⌜beta > 1⌝⦄
    (pure (DN_UP_parity_generic_pos_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hβ
  simp [wp, PostCond.noThrow, pure]
  unfold DN_UP_parity_generic_pos_check
  classical
  simp [decide_eq_true_iff]
  intro x xd xu hx_pos hnotFmt hDN hUP
  let F : ℝ → Prop := fun y => generic_format beta fexp y
  rcases FloatSpec.Core.Generic_fmt.DN_UP_canonical_neighbors
      (beta := beta) (fexp := fexp) (x := x) (xd := xd) (xu := xu)
      hβ hDN hUP with
    ⟨gd, gu, hxd_eq, hxu_eq, hcan_d, hcan_u⟩
  refine ⟨gd, gu, hxd_eq, hxu_eq, hcan_d, hcan_u, ?_⟩
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  set ex : Int := FloatSpec.Core.Raux.mag beta x with hex
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hlow : (beta : ℝ) ^ (ex - 1) ≤ x := by
    have htrip := FloatSpec.Core.Raux.mag_lower_bound (beta := beta) (x := x) hβ hx_ne
    simpa [FloatSpec.Core.Raux.abs_val, abs_of_nonneg hx_nonneg, hex,
      wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hhigh : x < (beta : ℝ) ^ ex := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := x) hβ hx_ne
    simpa [FloatSpec.Core.Raux.abs_val, abs_of_nonneg hx_nonneg, hex,
      wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
  by_cases hsmall : ex ≤ fexp ex
  · have hDN_floor : FloatSpec.Core.Round_pred.Rnd_DN_pt F x
        (roundR beta fexp rnd_floor x) := by
      simpa [F] using roundR_floor_DN_pt (beta := beta) (fexp := fexp) x hβ
    have hxd_floor : xd = roundR beta fexp rnd_floor x :=
      Rnd_DN_pt_unique_pure F x xd (roundR beta fexp rnd_floor x)
        (by simpa [F] using hDN) hDN_floor
    have hdn_small : roundR beta fexp rnd_floor x = 0 := by
      exact round_DN_small_pos (beta := beta) (fexp := fexp)
        (x := x) (ex := ex) ⟨hlow, hhigh⟩ hsmall hβ
    have hxd_zero : xd = 0 := by simpa [hdn_small] using hxd_floor
    have hgd_num : gd.Fnum = 0 := by
      apply canonical_zero_mantissa (beta := beta) (fexp := fexp) (g := gd) hβ
      calc
        F2R gd = xd := hxd_eq.symm
        _ = 0 := hxd_zero
    have hUP_ceil : FloatSpec.Core.Round_pred.Rnd_UP_pt F x
        (roundR beta fexp rnd_ceil x) := by
      simpa [F] using roundR_ceil_UP_pt (beta := beta) (fexp := fexp) x hβ
    have hxu_ceil : xu = roundR beta fexp rnd_ceil x :=
      FloatSpec.Core.Round_pred.Rnd_UP_pt_unique_pure F x xu
        (roundR beta fexp rnd_ceil x) (by simpa [F] using hUP) hUP_ceil
    have hup_small_to_generic :
        round_to_generic beta fexp rnd_ceil x = (beta : ℝ) ^ (fexp ex) := by
      have htrip := round_UP_small_pos (beta := beta) (fexp := fexp)
        (x := x) (ex := ex)
      simpa [wp, PostCond.noThrow, Id.run, pure]
        using htrip ⟨hβ, hsmall, hlow, hhigh⟩
    have hup_small : roundR beta fexp rnd_ceil x = (beta : ℝ) ^ (fexp ex) := by
      calc
        roundR beta fexp rnd_ceil x = round_to_generic beta fexp rnd_ceil x := by
          exact (round_to_generic_int_eq_roundR
            (beta := beta) (fexp := fexp) (rnd := rnd_ceil) (x := x)).symm
        _ = (beta : ℝ) ^ (fexp ex) := hup_small_to_generic
    have hxu_pow : xu = (beta : ℝ) ^ (fexp ex) := by
      simpa [hup_small] using hxu_ceil
    have hgu_pow :
        F2R gu = (beta : ℝ) ^ (fexp ex) := by
      calc
        F2R gu = xu := hxu_eq.symm
        _ = (beta : ℝ) ^ (fexp ex) := hxu_pow
    have hgu_num := canonical_power_mantissa
      (beta := beta) (fexp := fexp) (g := gu) (e := fexp ex)
      hβ hcan_u hgu_pow
    have hgu_exp : gu.Fexp = fexp (fexp ex + 1) := by
      have hmag_pow :
          FloatSpec.Core.Raux.mag beta ((beta : ℝ) ^ (fexp ex)) = fexp ex + 1 := by
        have htrip := FloatSpec.Core.Raux.mag_bpow (beta := beta) (e := fexp ex) hβ
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
      have hcan_u' := hcan_u
      unfold canonical at hcan_u'
      have hmag_gu : FloatSpec.Core.Raux.mag beta (F2R gu) = fexp ex + 1 := by
        rw [hgu_pow]
        exact hmag_pow
      rwa [hmag_gu] at hcan_u'
    rcases Exists_NE.exists_ne (beta := beta) (fexp := fexp) with hodd | heven
    · have hgu_odd : gu.Fnum % 2 ≠ 0 := by
        rw [hgu_num]
        exact int_pow_odd_mod_two ((fexp ex - gu.Fexp).natAbs) hodd
      intro hsame
      exact hgu_odd (by simpa [hgd_num] using hsame.symm)
    · have hgu_exp_eq : gu.Fexp = fexp ex := by
        have hsmall_eq := (heven ex).right hsmall
        simpa [hsmall_eq] using hgu_exp
      have hgu_num_one : gu.Fnum = 1 := by
        rw [hgu_num, hgu_exp_eq]
        simp
      intro hsame
      have : (0 : Int) = 1 := by
        simpa [hgd_num, hgu_num_one] using hsame
      norm_num at this
  · have hlarge : fexp ex < ex := lt_of_not_ge hsmall
    have hcexp_x : cexp beta fexp x = fexp ex := by
      have htrip := cexp_fexp_pos (beta := beta) (fexp := fexp) (x := x) (ex := ex)
      simpa [wp, PostCond.noThrow, Id.run, pure]
        using htrip ⟨hβ, hlow, hhigh⟩
    set sm : ℝ := scaled_mantissa beta fexp x with hsm
    set c : Int := fexp ex with hc
    have hscaled : sm * (beta : ℝ) ^ c = x := by
      have htrip := scaled_mantissa_mult_bpow (beta := beta) (fexp := fexp) (x := x)
      simpa [wp, PostCond.noThrow, Id.run, pure, sm, hsm, c, hc, hcexp_x]
        using htrip hβ
    have hbpos : (0 : ℝ) < (beta : ℝ) := by
      exact_mod_cast (lt_trans Int.zero_lt_one hβ)
    have hpow_c_pos : 0 < (beta : ℝ) ^ c := zpow_pos hbpos c
    have hsm_pos : 0 < sm := by
      have hx_eq : x = sm * (beta : ℝ) ^ c := hscaled.symm
      have : 0 < sm * (beta : ℝ) ^ c := by simpa [hx_eq] using hx_pos
      exact (mul_pos_iff_of_pos_right hpow_c_pos).mp this
    have hsm_ne_floor : sm ≠ ((Int.floor sm : Int) : ℝ) := by
      intro hfloor
      have htrunc : FloatSpec.Core.Raux.Ztrunc (scaled_mantissa beta fexp x) = Int.floor sm := by
        rw [← hsm]
        simp [FloatSpec.Core.Raux.Ztrunc, not_lt.mpr (le_of_lt hsm_pos)]
      have hx_recon : x = ((Int.floor sm : Int) : ℝ) * (beta : ℝ) ^ c := by
        calc
          x = sm * (beta : ℝ) ^ c := hscaled.symm
          _ = ((Int.floor sm : Int) : ℝ) * (beta : ℝ) ^ c :=
            congrArg (fun t : ℝ => t * (beta : ℝ) ^ c) hfloor
      have hfmt : generic_format beta fexp x := by
        unfold generic_format
        change x =
          F2R (FlocqFloat.mk
            (FloatSpec.Core.Raux.Ztrunc (scaled_mantissa beta fexp x))
            (cexp beta fexp x) : FlocqFloat beta)
        rw [hcexp_x, htrunc]
        change x = ((Int.floor sm : Int) : ℝ) * (beta : ℝ) ^ (fexp ex)
        simpa [c, hc] using hx_recon
      exact hnotFmt hfmt
    have hceil_succ : Int.ceil sm = Int.floor sm + 1 :=
      ceil_eq_floor_add_one hsm_ne_floor
    have hDN_floor : FloatSpec.Core.Round_pred.Rnd_DN_pt F x
        (roundR beta fexp rnd_floor x) := by
      simpa [F] using roundR_floor_DN_pt (beta := beta) (fexp := fexp) x hβ
    have hUP_ceil : FloatSpec.Core.Round_pred.Rnd_UP_pt F x
        (roundR beta fexp rnd_ceil x) := by
      simpa [F] using roundR_ceil_UP_pt (beta := beta) (fexp := fexp) x hβ
    have hxd_floor : xd = roundR beta fexp rnd_floor x :=
      Rnd_DN_pt_unique_pure F x xd (roundR beta fexp rnd_floor x)
        (by simpa [F] using hDN) hDN_floor
    have hxu_ceil : xu = roundR beta fexp rnd_ceil x :=
      FloatSpec.Core.Round_pred.Rnd_UP_pt_unique_pure F x xu
        (roundR beta fexp rnd_ceil x) (by simpa [F] using hUP) hUP_ceil
    have hdn_eval :
        roundR beta fexp rnd_floor x =
          ((Int.floor sm : Int) : ℝ) * (beta : ℝ) ^ c := by
      simp [roundR, rnd_floor, FloatSpec.Core.Raux.Zfloor, sm, hsm, c, hc, hcexp_x]
    have hup_eval :
        roundR beta fexp rnd_ceil x =
          ((Int.ceil sm : Int) : ℝ) * (beta : ℝ) ^ c := by
      simp [roundR, rnd_ceil, FloatSpec.Core.Raux.Zceil, sm, hsm, c, hc, hcexp_x]
    have hround_floor_bounds :=
      roundR_bounded_large_pos (beta := beta) (fexp := fexp) (rnd := rnd_floor)
        (x := x) (ex := ex) ⟨hlow, hhigh⟩ hlarge hβ
    have hround_ceil_bounds :=
      roundR_bounded_large_pos (beta := beta) (fexp := fexp) (rnd := rnd_ceil)
        (x := x) (ex := ex) ⟨hlow, hhigh⟩ hlarge hβ
    have hxd_low : (beta : ℝ) ^ (ex - 1) ≤ xd := by
      simpa [hxd_floor] using hround_floor_bounds.left
    have hxu_le : xu ≤ (beta : ℝ) ^ ex := by
      simpa [hxu_ceil] using hround_ceil_bounds.right
    rcases lt_or_eq_of_le hxu_le with hxu_lt | hxu_eq_pow
    · have hxd_lt : xd < (beta : ℝ) ^ ex := lt_of_le_of_lt hDN.2.1 hhigh
      have hxd_pos : 0 < xd := lt_of_lt_of_le (zpow_pos hbpos (ex - 1)) hxd_low
      have hgd_pos : 0 < F2R gd := by simpa [hxd_eq] using hxd_pos
      have hmag_gd : FloatSpec.Core.Raux.mag beta (F2R gd) = ex := by
        have hlow_abs : (beta : ℝ) ^ (ex - 1) ≤ |F2R gd| := by
          have hlow_gd : (beta : ℝ) ^ (ex - 1) ≤ F2R gd := by
            simpa [hxd_eq] using hxd_low
          rw [abs_of_pos hgd_pos]
          exact hlow_gd
        have hhigh_abs : |F2R gd| < (beta : ℝ) ^ ex := by
          have hhigh_gd : F2R gd < (beta : ℝ) ^ ex := by
            simpa [hxd_eq] using hxd_lt
          rw [abs_of_pos hgd_pos]
          exact hhigh_gd
        have htrip := FloatSpec.Core.Raux.mag_unique
          (beta := beta) (x := F2R gd) (e := ex) hβ hlow_abs hhigh_abs
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
      have hgd_exp : gd.Fexp = c := by
        unfold canonical at hcan_d
        rw [hmag_gd] at hcan_d
        simpa [c, hc] using hcan_d
      have hxu_low : (beta : ℝ) ^ (ex - 1) ≤ xu := le_trans hlow hUP.2.1
      have hxu_pos : 0 < xu := lt_of_lt_of_le (zpow_pos hbpos (ex - 1)) hxu_low
      have hgu_pos : 0 < F2R gu := by simpa [hxu_eq] using hxu_pos
      have hmag_gu : FloatSpec.Core.Raux.mag beta (F2R gu) = ex := by
        have hlow_abs : (beta : ℝ) ^ (ex - 1) ≤ |F2R gu| := by
          have hlow_gu : (beta : ℝ) ^ (ex - 1) ≤ F2R gu := by
            simpa [hxu_eq] using hxu_low
          rw [abs_of_pos hgu_pos]
          exact hlow_gu
        have hhigh_abs : |F2R gu| < (beta : ℝ) ^ ex := by
          have hhigh_gu : F2R gu < (beta : ℝ) ^ ex := by
            simpa [hxu_eq] using hxu_lt
          rw [abs_of_pos hgu_pos]
          exact hhigh_gu
        have htrip := FloatSpec.Core.Raux.mag_unique
          (beta := beta) (x := F2R gu) (e := ex) hβ hlow_abs hhigh_abs
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
      have hgu_exp : gu.Fexp = c := by
        unfold canonical at hcan_u
        rw [hmag_gu] at hcan_u
        simpa [c, hc] using hcan_u
      have hgd_val :
          F2R gd = ((Int.floor sm : Int) : ℝ) * (beta : ℝ) ^ c := by
        calc
          F2R gd = xd := hxd_eq.symm
          _ = roundR beta fexp rnd_floor x := hxd_floor
          _ = ((Int.floor sm : Int) : ℝ) * (beta : ℝ) ^ c := hdn_eval
      have hgu_val :
          F2R gu = ((Int.ceil sm : Int) : ℝ) * (beta : ℝ) ^ c := by
        calc
          F2R gu = xu := hxu_eq.symm
          _ = roundR beta fexp rnd_ceil x := hxu_ceil
          _ = ((Int.ceil sm : Int) : ℝ) * (beta : ℝ) ^ c := hup_eval
      have hgd_num : gd.Fnum = Int.floor sm :=
        same_exp_mantissa (beta := beta) (g := gd) (m := Int.floor sm) (e := c)
          hβ hgd_exp hgd_val
      have hgu_num : gu.Fnum = Int.ceil sm :=
        same_exp_mantissa (beta := beta) (g := gu) (m := Int.ceil sm) (e := c)
          hβ hgu_exp hgu_val
      have hsucc : gu.Fnum = gd.Fnum + 1 := by
        simp [hgd_num, hgu_num, hceil_succ]
      simpa [hsucc] using parity_succ_flip gd.Fnum
    · -- Boundary case: `xu = β^ex`; the UP endpoint changes canonical binade.
      have hceil_val :
          ((Int.ceil sm : Int) : ℝ) * (beta : ℝ) ^ c = (beta : ℝ) ^ ex := by
        calc
          ((Int.ceil sm : Int) : ℝ) * (beta : ℝ) ^ c
              = roundR beta fexp rnd_ceil x := hup_eval.symm
          _ = xu := hxu_ceil.symm
          _ = (beta : ℝ) ^ ex := hxu_eq_pow
      have hc_le_ex : c ≤ ex := le_of_lt hlarge
      have hceil_num : Int.ceil sm = beta ^ ((ex - c).natAbs) :=
        scaled_int_eq_power_mantissa (beta := beta) (m := Int.ceil sm)
          (c := c) (e := ex) hβ hc_le_ex hceil_val
      have hfloor_num : Int.floor sm = beta ^ ((ex - c).natAbs) - 1 := by
        omega
      have hxd_lt : xd < (beta : ℝ) ^ ex := lt_of_le_of_lt hDN.2.1 hhigh
      have hxd_pos : 0 < xd := lt_of_lt_of_le (zpow_pos hbpos (ex - 1)) hxd_low
      have hgd_pos : 0 < F2R gd := by simpa [hxd_eq] using hxd_pos
      have hmag_gd : FloatSpec.Core.Raux.mag beta (F2R gd) = ex := by
        have hlow_abs : (beta : ℝ) ^ (ex - 1) ≤ |F2R gd| := by
          have hlow_gd : (beta : ℝ) ^ (ex - 1) ≤ F2R gd := by
            simpa [hxd_eq] using hxd_low
          rw [abs_of_pos hgd_pos]
          exact hlow_gd
        have hhigh_abs : |F2R gd| < (beta : ℝ) ^ ex := by
          have hhigh_gd : F2R gd < (beta : ℝ) ^ ex := by
            simpa [hxd_eq] using hxd_lt
          rw [abs_of_pos hgd_pos]
          exact hhigh_gd
        have htrip := FloatSpec.Core.Raux.mag_unique
          (beta := beta) (x := F2R gd) (e := ex) hβ hlow_abs hhigh_abs
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
      have hgd_exp : gd.Fexp = c := by
        unfold canonical at hcan_d
        rw [hmag_gd] at hcan_d
        simpa [c, hc] using hcan_d
      have hgd_val :
          F2R gd = ((Int.floor sm : Int) : ℝ) * (beta : ℝ) ^ c := by
        calc
          F2R gd = xd := hxd_eq.symm
          _ = roundR beta fexp rnd_floor x := hxd_floor
          _ = ((Int.floor sm : Int) : ℝ) * (beta : ℝ) ^ c := hdn_eval
      have hgd_floor : gd.Fnum = Int.floor sm :=
        same_exp_mantissa (beta := beta) (g := gd) (m := Int.floor sm) (e := c)
          hβ hgd_exp hgd_val
      have hgd_num : gd.Fnum = beta ^ ((ex - c).natAbs) - 1 := by
        rw [hgd_floor, hfloor_num]
      have hgu_pow : F2R gu = (beta : ℝ) ^ ex := by
        calc
          F2R gu = xu := hxu_eq.symm
          _ = (beta : ℝ) ^ ex := hxu_eq_pow
      have hgu_num := canonical_power_mantissa
        (beta := beta) (fexp := fexp) (g := gu) (e := ex)
        hβ hcan_u hgu_pow
      have hgu_exp := canonical_power_exp
        (beta := beta) (fexp := fexp) (g := gu) (e := ex)
        hβ hcan_u hgu_pow
      set kd : Nat := (ex - c).natAbs with hkd
      set ku : Nat := (ex - gu.Fexp).natAbs with hku
      have hgd_num' : gd.Fnum = beta ^ kd - 1 := by simpa [kd, hkd] using hgd_num
      have hgu_num' : gu.Fnum = beta ^ ku := by simpa [ku, hku] using hgu_num
      have hpow_parity : (beta ^ kd) % 2 = (beta ^ ku) % 2 := by
        rcases Exists_NE.exists_ne (beta := beta) (fexp := fexp) with hodd | heven
        · have hdodd : (beta ^ kd) % 2 ≠ 0 := int_pow_odd_mod_two (b := beta) kd hodd
          have huodd : (beta ^ ku) % 2 ≠ 0 := int_pow_odd_mod_two (b := beta) ku hodd
          have hd1 : (beta ^ kd) % 2 = 1 := by
            rcases Int.emod_two_eq_zero_or_one (beta ^ kd) with h0 | h1
            · exact False.elim (hdodd h0)
            · exact h1
          have hu1 : (beta ^ ku) % 2 = 1 := by
            rcases Int.emod_two_eq_zero_or_one (beta ^ ku) with h0 | h1
            · exact False.elim (huodd h0)
            · exact h1
          rw [hd1, hu1]
        · have hkd_pos_int : 0 < ex - c := sub_pos.mpr hlarge
          have hkd_pos : 0 < kd := by
            rw [hkd]
            exact Int.natAbs_pos.mpr (ne_of_gt hkd_pos_int)
          have hgu_exp_lt : gu.Fexp < ex := by
            have hlt := (heven ex).left hlarge
            simpa [hgu_exp] using hlt
          have hku_pos_int : 0 < ex - gu.Fexp := sub_pos.mpr hgu_exp_lt
          have hku_pos : 0 < ku := by
            rw [hku]
            exact Int.natAbs_pos.mpr (ne_of_gt hku_pos_int)
          have hdbase := int_pow_pos_mod_two_eq_base beta (n := kd) hkd_pos
          have hubase := int_pow_pos_mod_two_eq_base beta (n := ku) hku_pos
          exact hdbase.trans hubase.symm
      intro hsame
      have hbad : (beta ^ kd - 1) % 2 = (beta ^ kd) % 2 := by
        have hsame_pow : (beta ^ kd - 1) % 2 = (beta ^ ku) % 2 := by
          simpa [hgd_num', hgu_num'] using hsame
        simpa [hpow_parity] using hsame_pow
      exact parity_pred_flip (beta ^ kd) hbad


/-- Check DN/UP parity holds for the generic format (all reals) -/
noncomputable def DN_UP_parity_generic_check : Bool :=
    @decide (DN_UP_parity_prop beta fexp) (Classical.dec _)

/-- Coq:
    Theorem DN_UP_parity_generic :
      DN_UP_parity_prop.

    General parity property derived from the positive case.
-/
theorem DN_UP_parity_generic :
    ⦃⌜beta > 1⌝⦄
    (pure (DN_UP_parity_generic_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure]
  unfold DN_UP_parity_generic_check
  classical
  -- Reduce the Hoare triple on Id to proving the propositional property.
  -- Target: decide (DN_UP_parity_prop beta fexp) = true
  simp [decide_eq_true_iff]
  -- It suffices to derive DN_UP_parity_prop from the positive-case property via the auxiliary lemma.
  -- First, obtain the positive-case property from `DN_UP_parity_generic_pos`.
  have hβ : 1 < beta := by
    -- The precondition is ⌜beta > 1⌝
    assumption
  have hpos : DN_UP_parity_pos_prop beta fexp := by
    -- Consume the triple-style theorem to a pure proposition using `simp` on decide
    have htrip := DN_UP_parity_generic_pos (beta := beta) (fexp := fexp)
    -- `htrip hβ` states that `decide (DN_UP_parity_pos_prop) = true`
    simpa [DN_UP_parity_generic_pos_check, pure, decide_eq_true_iff]
      using (htrip hβ)
  -- Now apply the auxiliary lemma to conclude the general property holds.
  have haux := DN_UP_parity_aux (beta := beta) (fexp := fexp)
  -- Reduce its triple-form statement to the same `decide` goal and finish by rewriting.
  simpa [DN_UP_parity_aux_check, pure, decide_eq_true_iff]
    using (haux ⟨hβ, hpos⟩)

/-- Local bridge from the DN/UP parity theorem to the nearest-even tie payload.

When a non-representable value has concrete down/up neighbors, at least one of
those neighbors satisfies `NE_prop`; the parity theorem says their canonical
mantissas have different residues mod 2, so one residue is zero. -/
theorem DN_UP_NE_prop
    (hβ : 1 < beta) (x xd xu : ℝ)
    (hnotFmt : ¬FloatSpec.Core.Generic_fmt.generic_format beta fexp x)
    (hDN : FloatSpec.Core.Round_pred.Rnd_DN_pt
      (fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y) x xd)
    (hUP : FloatSpec.Core.Round_pred.Rnd_UP_pt
      (fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y) x xu) :
    NE_prop beta fexp x xd ∨ NE_prop beta fexp x xu := by
  classical
  have hpar : DN_UP_parity_prop beta fexp := by
    have htrip := DN_UP_parity_generic (beta := beta) (fexp := fexp)
    simpa [DN_UP_parity_generic_check, pure, decide_eq_true_iff]
      using htrip hβ
  rcases hpar x xd xu hnotFmt hDN hUP with
    ⟨gd, gu, hxd_eq, hxu_eq, hcan_d, hcan_u, hparity⟩
  have hgd_even_or_gu_even : gd.Fnum % 2 = 0 ∨ gu.Fnum % 2 = 0 := by
    rcases Int.emod_two_eq_zero_or_one gd.Fnum with hgd0 | hgd1
    · exact Or.inl hgd0
    · rcases Int.emod_two_eq_zero_or_one gu.Fnum with hgu0 | hgu1
      · exact Or.inr hgu0
      · have : gd.Fnum % 2 = gu.Fnum % 2 := by simpa [hgd1, hgu1]
        exact (hparity this).elim
  cases hgd_even_or_gu_even with
  | inl hEven =>
      exact Or.inl ⟨gd, by simpa using hxd_eq, hcan_d, by simpa using hEven⟩
  | inr hEven =>
      exact Or.inr ⟨gu, by simpa using hxu_eq, hcan_u, by simpa using hEven⟩

omit [Exists_NE beta fexp] in
/-- Off-midpoint bridge for the concrete nearest-even integer choice.

If the concrete down/up neighbors are not equidistant from `x`, nearest
rounding is unique. Therefore the concrete `ZnearestE` result satisfies the
nearest-even NG predicate through its uniqueness branch; the only remaining
case for the full Flocq `round_NE_pt` theorem is the exact midpoint tie. -/
theorem round_NE_pt_of_ne_mid
    (hβ : 1 < beta) (x : ℝ)
    (hneq :
      x - FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_floor x ≠
        FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_ceil x - x) :
    Rnd_NE_pt beta fexp x
      (FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) x) := by
  classical
  let F : ℝ → Prop := fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y
  let choice : Int → Bool := fun t => !(decide (2 ∣ t))
  let d : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_floor x
  let u : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_ceil x
  let r : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp (FloatSpec.Core.Generic_fmt.Znearest choice) x
  have hN : FloatSpec.Core.Defs.Rnd_N_pt F x r := by
    simpa [F, r, choice] using
      (FloatSpec.Core.Generic_fmt.round_N_pt (beta := beta) (fexp := fexp)
        (choice := choice) (x := x) hβ)
  have hDN : FloatSpec.Core.Defs.Rnd_DN_pt F x d := by
    simpa [F, d] using
      (FloatSpec.Core.Generic_fmt.round_DN_pt (beta := beta) (fexp := fexp)
        (x := x) hβ)
  have hUP : FloatSpec.Core.Defs.Rnd_UP_pt F x u := by
    simpa [F, u] using
      (FloatSpec.Core.Generic_fmt.round_UP_pt (beta := beta) (fexp := fexp)
        (x := x) hβ)
  have hneq' : x - d ≠ u - x := by
    simpa [d, u] using hneq
  have huniq : ∀ f2 : ℝ, FloatSpec.Core.Defs.Rnd_N_pt F x f2 → f2 = r := by
    intro f2 hf2
    have hspec := FloatSpec.Core.Round_pred.Rnd_N_pt_unique_spec
      (F := F) (x := x) (d := d) (u := u) (f1 := r) (f2 := f2)
    have hres := hspec ⟨hDN, hUP, hneq', hN, hf2⟩
    have hr_eq_f2 : r = f2 := by
      simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_unique_check, pure,
        decide_eq_true_iff] using hres
    exact hr_eq_f2.symm
  exact ⟨by simpa [F, r, choice] using hN, Or.inr huniq⟩

/-- At an exact half-integer, the nearest-even integer choice returns an even
integer. This is the integer-side payload needed by the concrete midpoint
branch of Flocq's `round_NE_pt`. -/
theorem ZnearestE_half_even (x : ℝ)
    (hmid :
      x - (((FloatSpec.Core.Raux.Zfloor x) : Int) : ℝ) = (1 / 2 : ℝ)) :
    (FloatSpec.Core.Generic_fmt.Znearest
      (fun t : Int => !(decide (2 ∣ t))) x) % 2 = 0 := by
  classical
  let choice : Int → Bool := fun t : Int => !(decide (2 ∣ t))
  set f : Int := FloatSpec.Core.Raux.Zfloor x with hf
  have hmid_f : x - (f : ℝ) = (1 / 2 : ℝ) := by
    simpa [hf] using hmid
  have hnot_f : x ≠ (f : ℝ) := by
    intro hx
    linarith
  have hnot_int : x ≠ ((Int.floor x : Int) : ℝ) := by
    simpa [hf, FloatSpec.Core.Raux.Zfloor] using hnot_f
  have hceil :
      FloatSpec.Core.Raux.Zceil x = f + 1 := by
    have hceil_floor := FloatSpec.Core.Generic_fmt.ceil_eq_floor_add_one
      (x := x) hnot_int
    simpa [hf, FloatSpec.Core.Raux.Zceil, FloatSpec.Core.Raux.Zfloor]
      using hceil_floor
  have hZraw :
      FloatSpec.Core.Generic_fmt.Znearest choice x =
        (if choice (FloatSpec.Core.Raux.Zfloor x)
         then FloatSpec.Core.Raux.Zceil x
         else FloatSpec.Core.Raux.Zfloor x) := by
    simpa [choice] using
      (FloatSpec.Core.Generic_fmt.Znearest_eq_choice_of_eq_half choice x hmid)
  rcases Int.emod_two_eq_zero_or_one f with hf0 | hf1
  · have hdiv_f : 2 ∣ f := Int.dvd_of_emod_eq_zero (by simpa using hf0)
    have hchoice : choice f = false := by
      simp [choice, hdiv_f]
    have hchoice_floor : choice (FloatSpec.Core.Raux.Zfloor x) = false := by
      simpa [hf] using hchoice
    have hZ_floor :
        FloatSpec.Core.Generic_fmt.Znearest choice x = f := by
      have hZ_floor_raw :
          FloatSpec.Core.Generic_fmt.Znearest choice x =
            FloatSpec.Core.Raux.Zfloor x := by
        simpa [hchoice_floor] using hZraw
      simpa [hf] using hZ_floor_raw
    simpa [choice, hZ_floor] using hf0
  · have hndiv_f : ¬ 2 ∣ f := by
      intro hdiv
      have hzero : f % 2 = 0 :=
        Int.emod_eq_zero_of_dvd (a := 2) (b := f) hdiv
      have : (1 : Int) = 0 := by simpa [hf1] using hzero
      norm_num at this
    have hchoice : choice f = true := by
      simp [choice, hndiv_f]
    have hchoice_floor : choice (FloatSpec.Core.Raux.Zfloor x) = true := by
      simpa [hf] using hchoice
    have hZ_ceil :
        FloatSpec.Core.Generic_fmt.Znearest choice x =
          FloatSpec.Core.Raux.Zceil x := by
      simpa [hchoice_floor] using hZraw
    have hadd :
        (f + 1) % 2 = ((f % 2) + (1 % 2)) % 2 := by
      simpa using (Int.add_emod f 1 2)
    have h1mod : (1 % 2 : Int) = 1 := by decide
    have h11 : ((1 + 1) % 2 : Int) = 0 := by decide
    have hsucc_even : (f + 1) % 2 = 0 := by
      simpa [hadd, hf1, h1mod] using h11
    simpa [choice, hZ_ceil, hceil] using hsucc_even

omit [Exists_NE beta fexp] in
/-- Concrete nearest-even rounding fixes representable values as an
`Rnd_NE_pt`. This is the generic-format branch of Flocq's `round_NE_pt`. -/
theorem round_NE_pt_of_generic
    (hβ : 1 < beta) (x : ℝ)
    (hx : FloatSpec.Core.Generic_fmt.generic_format beta fexp x) :
    Rnd_NE_pt beta fexp x
      (FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) x) := by
  classical
  let F : ℝ → Prop := fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y
  let P : ℝ → ℝ → Prop := NE_prop beta fexp
  let choice : Int → Bool := fun t : Int => !(decide (2 ∣ t))
  have hfix :
      FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest choice) x = x := by
    exact FloatSpec.Core.Generic_fmt.roundR_generic
      (beta := beta) (fexp := fexp)
      (rnd := FloatSpec.Core.Generic_fmt.Znearest choice) (x := x) hβ hx
  have hrefl := FloatSpec.Core.Round_pred.Rnd_NG_pt_refl_spec
    (F := F) (P := P) (x := x)
  have hNGx : FloatSpec.Core.Defs.Rnd_NG_pt F P x x := by
    simpa [FloatSpec.Core.Round_pred.Rnd_NG_pt_refl_check, pure,
      decide_eq_true_iff, F, P] using hrefl hx
  simpa [F, P, choice, hfix] using hNGx

omit [Exists_NE beta fexp] in
/-- Concrete nearest-even rounding is already proved except for the single
non-generic exact-midpoint case. -/
theorem round_NE_pt_of_generic_or_ne_mid
    (hβ : 1 < beta) (x : ℝ)
    (hcase :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp x ∨
        x - FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_floor x ≠
          FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_ceil x - x) :
    Rnd_NE_pt beta fexp x
      (FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) x) := by
  cases hcase with
  | inl hx =>
      exact round_NE_pt_of_generic (beta := beta) (fexp := fexp) hβ x hx
  | inr hneq =>
      exact round_NE_pt_of_ne_mid (beta := beta) (fexp := fexp) hβ x hneq

omit [Exists_NE beta fexp] in
/-- Midpoint bridge for concrete nearest rounding.

At an exact midpoint, `round_N_middle` rewrites the concrete nearest result to
the endpoint selected by the integer choice function.  Thus the remaining
midpoint obligation for Flocq's `round_NE_pt` is precisely to prove that this
selected endpoint satisfies `NE_prop`. -/
theorem round_NE_pt_of_midpoint_choice
    (hβ : 1 < beta) (choice : Int → Bool) (x : ℝ)
    (hmid :
      x - FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_floor x =
        FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_ceil x - x)
    (hNE :
      NE_prop beta fexp x
        (if choice (FloatSpec.Core.Raux.Zfloor
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x))
         then FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_ceil x
         else FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_floor x)) :
    Rnd_NE_pt beta fexp x
      (FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest choice) x) := by
  let F : ℝ → Prop := fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y
  let P : ℝ → ℝ → Prop := NE_prop beta fexp
  have hN : FloatSpec.Core.Defs.Rnd_N_pt F x
      (FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest choice) x) := by
    simpa [F] using
      (FloatSpec.Core.Generic_fmt.round_N_pt (beta := beta) (fexp := fexp)
        (choice := choice) (x := x) hβ)
  have hmiddle :
      FloatSpec.Core.Generic_fmt.roundR beta fexp
          (FloatSpec.Core.Generic_fmt.Znearest choice) x =
        (if choice (FloatSpec.Core.Raux.Zfloor
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x))
         then FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_ceil x
         else FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_floor x) := by
    simpa [FloatSpec.Core.Generic_fmt.rnd_floor, FloatSpec.Core.Generic_fmt.rnd_ceil] using
      (FloatSpec.Core.Generic_fmt.round_N_middle (beta := beta) (fexp := fexp)
        (choice := choice) (x := x) hβ hmid)
  exact ⟨by simpa [F] using hN, Or.inl (by simpa [P, hmiddle] using hNE)⟩

omit [Exists_NE beta fexp] in
/-- Build the nearest-even tie payload from the canonical mantissa of a
generic-format value.

This is the witness construction used in Flocq's midpoint branch for
`round_NE_pt`: the canonical float
`(Ztrunc (scaled_mantissa r), cexp r)` represents `r`, and evenness of that
mantissa supplies `NE_prop`. -/
theorem NE_prop_of_generic_even_mantissa
    (hβ : 1 < beta) (x r : ℝ)
    (hr : FloatSpec.Core.Generic_fmt.generic_format beta fexp r)
    (heven :
      FloatSpec.Core.Raux.Ztrunc
        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp r) % 2 = 0) :
    NE_prop beta fexp x r := by
  let g : FlocqFloat beta :=
    ⟨FloatSpec.Core.Raux.Ztrunc
        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp r),
      FloatSpec.Core.Generic_fmt.cexp beta fexp r⟩
  have hcanTrip := FloatSpec.Core.Generic_fmt.canonical_generic_format
    (beta := beta) (fexp := fexp) (x := r)
  have hcan : FloatSpec.Core.Generic_fmt.canonical beta fexp g := by
    have hpost :
        r = F2R g → FloatSpec.Core.Generic_fmt.canonical beta fexp g := by
      simpa [g, wp, PostCond.noThrow, Id.run, pure] using hcanTrip ⟨hβ, hr⟩
    exact hpost hr
  exact ⟨g, by simpa [g] using hr, hcan, by simpa [g] using heven⟩

omit [Exists_NE beta fexp] in
/-- Concrete nearest rounding becomes nearest-even once its canonical mantissa
is known to be even. This isolates the remaining midpoint work for
`round_NE_pt` to a parity statement about the rounded value itself. -/
theorem round_NE_pt_of_canonical_even
    (hβ : 1 < beta) (choice : Int → Bool) (x : ℝ)
    (heven :
      FloatSpec.Core.Raux.Ztrunc
        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp
          (FloatSpec.Core.Generic_fmt.roundR beta fexp
            (FloatSpec.Core.Generic_fmt.Znearest choice) x)) % 2 = 0) :
    Rnd_NE_pt beta fexp x
      (FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest choice) x) := by
  let F : ℝ → Prop := fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y
  let r : ℝ :=
    FloatSpec.Core.Generic_fmt.roundR beta fexp
      (FloatSpec.Core.Generic_fmt.Znearest choice) x
  have hN : FloatSpec.Core.Defs.Rnd_N_pt F x r := by
    simpa [F, r] using
      (FloatSpec.Core.Generic_fmt.round_N_pt (beta := beta) (fexp := fexp)
        (choice := choice) (x := x) hβ)
  have hNE : NE_prop beta fexp x r :=
    NE_prop_of_generic_even_mantissa (beta := beta) (fexp := fexp)
      hβ x r (by simpa [F] using hN.1) (by simpa [r] using heven)
  exact ⟨by simpa [F, r] using hN, Or.inl hNE⟩

omit [Exists_NE beta fexp] in
/-- Floor endpoint parity bridge for the positive midpoint branch.

If positive `x` is rounded downward and the original scaled floor mantissa is
even, then the canonical mantissa of the down-rounded value is even.  This is
the floor-selected half of Flocq's midpoint proof for `round_NE_pt_pos`. -/
theorem round_DN_canonical_even_of_floor_even
    (hβ : 1 < beta) (x : ℝ) (hx : 0 < x)
    (heven_floor :
      FloatSpec.Core.Generic_fmt.rnd_floor
        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x) % 2 = 0) :
    FloatSpec.Core.Raux.Ztrunc
      (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp
        (FloatSpec.Core.Generic_fmt.roundR beta fexp
          FloatSpec.Core.Generic_fmt.rnd_floor x)) % 2 = 0 := by
  classical
  let sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x
  let e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x
  let r : ℝ :=
    FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_floor x
  have hr_nonneg : 0 ≤ r := by
    exact FloatSpec.Core.Generic_fmt.roundR_nonneg_of_nonneg
      (beta := beta) (fexp := fexp)
      (rnd := FloatSpec.Core.Generic_fmt.rnd_floor) (x := x) hβ (le_of_lt hx)
  by_cases hr0 : r = 0
  · have hsm0 :
        FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp r = 0 := by
      simp [hr0, FloatSpec.Core.Generic_fmt.scaled_mantissa]
    simp [r, hsm0, FloatSpec.Core.Raux.Ztrunc]
  · have hrpos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr0)
    have hcexp : FloatSpec.Core.Generic_fmt.cexp beta fexp r =
        FloatSpec.Core.Generic_fmt.cexp beta fexp x := by
      have htrip := FloatSpec.Core.Generic_fmt.cexp_DN
        (beta := beta) (fexp := fexp) (x := x)
      have himp :
          0 < FloatSpec.Core.Generic_fmt.roundR beta fexp
              FloatSpec.Core.Generic_fmt.rnd_floor x →
            FloatSpec.Core.Generic_fmt.cexp beta fexp
                (FloatSpec.Core.Generic_fmt.roundR beta fexp
                  FloatSpec.Core.Generic_fmt.rnd_floor x) =
              FloatSpec.Core.Generic_fmt.cexp beta fexp x := by
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hβ
      simpa [r] using himp hrpos
    have hbpos : (0 : ℝ) < (beta : ℝ) := by
      exact_mod_cast (lt_trans Int.zero_lt_one hβ)
    have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
    have hr_eval :
        r =
          (((FloatSpec.Core.Generic_fmt.rnd_floor sm : Int) : ℝ) *
            (beta : ℝ) ^ e) := by
      simp [r, sm, e, FloatSpec.Core.Generic_fmt.roundR]
    have hcexp_e : FloatSpec.Core.Generic_fmt.cexp beta fexp r = e := by
      simpa [e] using hcexp
    have hpows : (beta : ℝ) ^ e * (beta : ℝ) ^ (-e) = 1 := by
      rw [← zpow_add₀ hbne e (-e)]
      simp
    have hsm_r :
        FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp r =
          ((FloatSpec.Core.Generic_fmt.rnd_floor sm : Int) : ℝ) := by
      calc
        FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp r
            = r * (beta : ℝ) ^ (-(FloatSpec.Core.Generic_fmt.cexp beta fexp r)) := by
                rfl
        _ = (((FloatSpec.Core.Generic_fmt.rnd_floor sm : Int) : ℝ) *
              (beta : ℝ) ^ e) * (beta : ℝ) ^ (-e) := by
                rw [hcexp_e, hr_eval]
        _ = ((FloatSpec.Core.Generic_fmt.rnd_floor sm : Int) : ℝ) *
              ((beta : ℝ) ^ e * (beta : ℝ) ^ (-e)) := by ring
        _ = ((FloatSpec.Core.Generic_fmt.rnd_floor sm : Int) : ℝ) * 1 := by
                rw [hpows]
        _ = ((FloatSpec.Core.Generic_fmt.rnd_floor sm : Int) : ℝ) := by ring
    have htrunc :
        FloatSpec.Core.Raux.Ztrunc
          (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp r) =
            FloatSpec.Core.Generic_fmt.rnd_floor sm := by
      rw [hsm_r]
      exact FloatSpec.Core.Generic_fmt.Ztrunc_intCast _
    simpa [r, sm, htrunc] using heven_floor

omit [Exists_NE beta fexp] in
/-- Canonical parity bridge for the down-rounded endpoint.

For positive `x`, any canonical float representing the concrete downward
rounding has the same mantissa parity as the original scaled floor mantissa.
This is the missing odd-floor half needed by the exact midpoint branch of
Flocq's `round_NE_pt`: if the floor mantissa is odd, `DN_UP_parity_prop` can
force the upward endpoint to be even. -/
theorem round_DN_canonical_parity_of_floor
    (hβ : 1 < beta) (x : ℝ) (hx : 0 < x)
    (gd : FlocqFloat beta)
    (hgd_val :
      FloatSpec.Core.Generic_fmt.roundR beta fexp
        FloatSpec.Core.Generic_fmt.rnd_floor x = F2R gd)
    (hcanon_gd : canonical beta fexp gd) :
    gd.Fnum % 2 =
      FloatSpec.Core.Generic_fmt.rnd_floor
        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x) % 2 := by
  classical
  set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x with hsm
  set e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x with he
  set mf : Int := FloatSpec.Core.Generic_fmt.rnd_floor sm with hmf
  set rd : ℝ :=
    FloatSpec.Core.Generic_fmt.roundR beta fexp
      FloatSpec.Core.Generic_fmt.rnd_floor x with hrd
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hpow_e_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbposR e
  have hsm_pos : 0 < sm := by
    have hpow_neg_pos : 0 < (beta : ℝ) ^ (-(e)) := zpow_pos hbposR _
    have hsm_def : sm = x * (beta : ℝ) ^ (-(e)) := by
      simp [sm, hsm, e, he, FloatSpec.Core.Generic_fmt.scaled_mantissa]
    rw [hsm_def]
    exact mul_pos hx hpow_neg_pos
  have hmf_nonneg : (0 : Int) ≤ mf := by
    rw [hmf]
    exact Int.floor_nonneg.mpr (le_of_lt hsm_pos)
  have hrd_eval : rd = ((mf : Int) : ℝ) * (beta : ℝ) ^ e := by
    simp [rd, hrd, FloatSpec.Core.Generic_fmt.roundR, sm, hsm, e, he, mf, hmf]
  by_cases hmf0 : mf = 0
  · let gz : FlocqFloat beta := ⟨0, fexp (FloatSpec.Core.Raux.mag beta 0)⟩
    have Cgz : canonical beta fexp gz := by
      simpa [gz] using
        FloatSpec.Core.Generic_fmt.canonical_0 (beta := beta) (fexp := fexp)
    have hrd0 : rd = 0 := by
      simp [hrd_eval, hmf0]
    have hgd_eq : gd = gz := by
      apply FloatSpec.Core.Generic_fmt.canonical_unique
        (beta := beta) (hbeta := hβ) (fexp := fexp)
      · exact hcanon_gd
      · exact Cgz
      · calc
          F2R gd = rd := by simpa [rd, hrd] using hgd_val.symm
          _ = 0 := hrd0
          _ = F2R gz := by simp [gz, FloatSpec.Core.Defs.F2R]
    simp [hgd_eq, gz, hmf0, mf, hmf]
  · have hmf_pos : 0 < mf := lt_of_le_of_ne hmf_nonneg (Ne.symm hmf0)
    have hrd_pos : 0 < rd := by
      have hmf_posR : 0 < ((mf : Int) : ℝ) := by exact_mod_cast hmf_pos
      simpa [hrd_eval] using mul_pos hmf_posR hpow_e_pos
    let gf : FlocqFloat beta := ⟨mf, e⟩
    have hgf_val : F2R gf = rd := by
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
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hβ
      simpa [rd, hrd, e, he] using himp (by simpa [rd, hrd] using hrd_pos)
    have Cgf : canonical beta fexp gf := by
      simpa [gf, FloatSpec.Core.Generic_fmt.canonical,
        FloatSpec.Core.Generic_fmt.cexp, hgf_val, hcexp_rd] using hcexp_rd.symm
    have hgd_eq : gd = gf := by
      apply FloatSpec.Core.Generic_fmt.canonical_unique
        (beta := beta) (hbeta := hβ) (fexp := fexp)
      · exact hcanon_gd
      · exact Cgf
      · calc
          F2R gd = rd := by simpa [rd, hrd] using hgd_val.symm
          _ = F2R gf := hgf_val.symm
    simp [hgd_eq, gf, mf, hmf]

/-- Positive-input branch of Flocq's concrete `round_NE_pt`.

For positive values, the generic case, non-midpoint case, and midpoint parity
case are all discharged for the concrete nearest-even choice.  The remaining
public wrapper work is sign/zero plumbing around this theorem. -/
theorem round_NE_pt_pos_exact
    (hβ : 1 < beta) (x : ℝ) (hx : 0 < x) :
    Rnd_NE_pt beta fexp x
      (FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) x) := by
  classical
  let choice : Int → Bool := fun t => !(decide (2 ∣ t))
  let F : ℝ → Prop := fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y
  let d : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_floor x
  let u : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_ceil x
  let sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x
  by_cases hxFmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp x
  · exact round_NE_pt_of_generic (beta := beta) (fexp := fexp) hβ x hxFmt
  · by_cases hmid : x - d = u - x
    · by_cases hfloor_even :
          FloatSpec.Core.Generic_fmt.rnd_floor sm % 2 = 0
      · have hchoice_false : choice (FloatSpec.Core.Raux.Zfloor sm) = false := by
          have hdiv : 2 ∣ FloatSpec.Core.Raux.Zfloor sm :=
            Int.dvd_of_emod_eq_zero
              (by simpa [FloatSpec.Core.Generic_fmt.rnd_floor] using hfloor_even)
          simp [choice, hdiv]
        have hfmt_d : FloatSpec.Core.Generic_fmt.generic_format beta fexp d := by
          simpa [F, d] using
            FloatSpec.Core.Generic_fmt.generic_format_roundR
              (beta := beta) (fexp := fexp)
              (rnd := FloatSpec.Core.Generic_fmt.rnd_floor) (x := x) hβ
        have heven_d :
            FloatSpec.Core.Raux.Ztrunc
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp d) % 2 = 0 := by
          simpa [d, sm] using
            round_DN_canonical_even_of_floor_even
              (beta := beta) (fexp := fexp) hβ x hx hfloor_even
        have hNEd : NE_prop beta fexp x d :=
          NE_prop_of_generic_even_mantissa (beta := beta) (fexp := fexp)
            hβ x d hfmt_d heven_d
        have hselected :
            NE_prop beta fexp x
              (if choice (FloatSpec.Core.Raux.Zfloor
                    (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x))
               then FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_ceil x
               else FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_floor x) := by
          simpa [choice, d, u, sm, hchoice_false] using hNEd
        exact
          round_NE_pt_of_midpoint_choice (beta := beta) (fexp := fexp)
            hβ choice x (by simpa [d, u] using hmid) hselected
      · have hchoice_true : choice (FloatSpec.Core.Raux.Zfloor sm) = true := by
          have hndiv : ¬2 ∣ FloatSpec.Core.Raux.Zfloor sm := by
            intro hdiv
            exact hfloor_even
              (by
                simpa [FloatSpec.Core.Generic_fmt.rnd_floor] using
                  (Int.emod_eq_zero_of_dvd
                    (a := 2) (b := FloatSpec.Core.Raux.Zfloor sm) hdiv))
          simp [choice, hndiv]
        have hDN : FloatSpec.Core.Round_pred.Rnd_DN_pt F x d := by
          simpa [F, d] using
            FloatSpec.Core.Generic_fmt.round_DN_pt
              (beta := beta) (fexp := fexp) (x := x) hβ
        have hUP : FloatSpec.Core.Round_pred.Rnd_UP_pt F x u := by
          simpa [F, u] using
            FloatSpec.Core.Generic_fmt.round_UP_pt
              (beta := beta) (fexp := fexp) (x := x) hβ
        have hpar : DN_UP_parity_prop beta fexp := by
          have htrip := DN_UP_parity_generic (beta := beta) (fexp := fexp)
          simpa [DN_UP_parity_generic_check, pure, decide_eq_true_iff]
            using htrip hβ
        rcases hpar x d u hxFmt hDN hUP with
          ⟨gd, gu, hgd_val, hgu_val, hcanon_d, hcanon_u, hparity⟩
        have hgd_floor :
            gd.Fnum % 2 = FloatSpec.Core.Generic_fmt.rnd_floor sm % 2 := by
          exact
            round_DN_canonical_parity_of_floor
              (beta := beta) (fexp := fexp) hβ x hx gd
              (by simpa [d] using hgd_val) hcanon_d
        have hgd_odd : gd.Fnum % 2 ≠ 0 := by
          intro hgd_even
          exact hfloor_even (by simpa [hgd_floor] using hgd_even)
        have hgd_one : gd.Fnum % 2 = 1 := by
          rcases Int.emod_two_eq_zero_or_one gd.Fnum with h0 | h1
          · exact False.elim (hgd_odd h0)
          · exact h1
        have hgu_even : gu.Fnum % 2 = 0 := by
          rcases Int.emod_two_eq_zero_or_one gu.Fnum with h0 | h1
          · exact h0
          · exact False.elim (hparity (by rw [hgd_one, h1]))
        have hNEu : NE_prop beta fexp x u :=
          ⟨gu, by simpa using hgu_val, hcanon_u, hgu_even⟩
        have hselected :
            NE_prop beta fexp x
              (if choice (FloatSpec.Core.Raux.Zfloor
                    (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x))
               then FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_ceil x
               else FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_floor x) := by
          simpa [choice, d, u, sm, hchoice_true] using hNEu
        exact
          round_NE_pt_of_midpoint_choice (beta := beta) (fexp := fexp)
            hβ choice x (by simpa [d, u] using hmid) hselected
    · exact round_NE_pt_of_ne_mid (beta := beta) (fexp := fexp) hβ x
        (by simpa [d, u] using hmid)

end ParityAuxiliary

section UniquenessProperties

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
variable [Exists_NE beta fexp]

/-- NE_prop resolves ties uniquely between DN/UP nearest points.
    If both down- and up-rounded neighbors are nearest for x and both satisfy NE_prop,
    then they must be equal. This consolidates parity/adjacency reasoning proved
    elsewhere in the development. -/
private theorem tie_unique_NE_ax
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] [Exists_NE beta fexp]
    (hβ : 1 < beta) (x d u : ℝ) :
    let F : ℝ → Prop := fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y
    FloatSpec.Core.Defs.Rnd_DN_pt F x d →
    FloatSpec.Core.Defs.Rnd_N_pt F x d →
    FloatSpec.Core.Defs.Rnd_UP_pt F x u →
    FloatSpec.Core.Defs.Rnd_N_pt F x u →
    NE_prop beta fexp x d → NE_prop beta fexp x u → d = u := by
  intro F hDN hN_d hUP hN_u hP_d hP_u
  classical
  by_cases hxF : F x
  · have hd_eq_x : d = x := by
      have hd_le_zero : |d - x| ≤ 0 := by
        simpa using hN_d.2 x hxF
      have hd_abs_zero : |d - x| = 0 := le_antisymm hd_le_zero (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp hd_abs_zero)
    have hu_eq_x : u = x := by
      have hu_le_zero : |u - x| ≤ 0 := by
        simpa using hN_u.2 x hxF
      have hu_abs_zero : |u - x| = 0 := le_antisymm hu_le_zero (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp hu_abs_zero)
    exact hd_eq_x.trans hu_eq_x.symm
  · have hpar_prop : DN_UP_parity_prop beta fexp := by
      have htrip := DN_UP_parity_generic (beta := beta) (fexp := fexp)
      simpa [DN_UP_parity_generic_check, pure, decide_eq_true_iff]
        using (htrip hβ)
    rcases hpar_prop x d u hxF hDN hUP with
      ⟨gd, gu, hd_eq, hu_eq, hcanon_d, hcanon_u, hparity⟩
    rcases hP_d with ⟨gd_even, hd_even_eq, hcanon_d_even, hgd_even⟩
    rcases hP_u with ⟨gu_even, hu_even_eq, hcanon_u_even, hgu_even⟩
    have hgd_eq : gd = gd_even := by
      apply FloatSpec.Core.Generic_fmt.canonical_unique (beta := beta) (hbeta := hβ) (fexp := fexp)
      · exact hcanon_d
      · exact hcanon_d_even
      · calc
          F2R gd = d := hd_eq.symm
          _ = F2R gd_even := hd_even_eq
    have hgu_eq : gu = gu_even := by
      apply FloatSpec.Core.Generic_fmt.canonical_unique (beta := beta) (hbeta := hβ) (fexp := fexp)
      · exact hcanon_u
      · exact hcanon_u_even
      · calc
          F2R gu = u := hu_eq.symm
          _ = F2R gu_even := hu_even_eq
    have hgd_even' : gd.Fnum % 2 = 0 := by
      simpa [hgd_eq] using hgd_even
    have hgu_even' : gu.Fnum % 2 = 0 := by
      simpa [hgu_eq] using hgu_even
    exact False.elim (hparity (by rw [hgd_even', hgu_even']))

/-- Check nearest-even uniqueness property
-/
noncomputable def Rnd_NE_pt_unique_check : Bool :=
    @decide
      (∀ x f1 f2 : ℝ, Rnd_NE_pt beta fexp x f1 → Rnd_NE_pt beta fexp x f2 → f1 = f2)
      (Classical.dec _)

/-- Specification: Nearest-even uniqueness property

    The nearest-even rounding satisfies the uniqueness property
    required by the generic nearest rounding framework.
-/
theorem Rnd_NE_pt_unique_prop :
    ⦃⌜beta > 1⌝⦄
    (pure (Rnd_NE_pt_unique_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hβ
  simp [wp, PostCond.noThrow, pure]
  unfold Rnd_NE_pt_unique_check
  classical
  -- Reduce the Hoare triple to a propositional goal.
  simp [decide_eq_true_iff]
  -- Shorthand for the format predicate and NE tie-breaking.
  intro x f1 f2 hNE1 hNE2
  let F : ℝ → Prop := fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y
  let P : ℝ → ℝ → Prop := NE_prop beta fexp
  -- Tie-uniqueness property for NE: at most one of DN/UP can satisfy NE in a tie.
  have tie_unique_NE :
      ∀ x d u,
        FloatSpec.Core.Defs.Rnd_DN_pt F x d →
        FloatSpec.Core.Defs.Rnd_N_pt F x d →
        FloatSpec.Core.Defs.Rnd_UP_pt F x u →
        FloatSpec.Core.Defs.Rnd_N_pt F x u →
        P x d → P x u → d = u := by
    intro x d u hDN hN_d hUP hN_u hP_d hP_u
    -- Delegate to the local lemma consolidating tie uniqueness.
    exact tie_unique_NE_ax (beta := beta) (fexp := fexp) (hβ := hβ) (x := x) (d := d) (u := u)
      hDN hN_d hUP hN_u hP_d hP_u
  -- Coerce to the `Round_pred` aliases expected by the NG-uniqueness spec.
  have tie_unique_NE_pred :
      ∀ x d u,
        FloatSpec.Core.Round_pred.Rnd_DN_pt F x d →
        FloatSpec.Core.Round_pred.Rnd_N_pt F x d →
        FloatSpec.Core.Round_pred.Rnd_UP_pt F x u →
        FloatSpec.Core.Round_pred.Rnd_N_pt F x u →
        P x d → P x u → d = u := by
    intro x d u h1 h2 h3 h4 hp1 hp2
    exact tie_unique_NE x d u h1 h2 h3 h4 hp1 hp2
  -- Apply the NG uniqueness spec using this tie-uniqueness property
  have huniq := FloatSpec.Core.Round_pred.Rnd_NG_pt_unique_spec
      (F := F) (P := P) (x := x) (f1 := f1) (f2 := f2)
  have : f1 = f2 := by
    simpa [FloatSpec.Core.Round_pred.Rnd_NG_pt_unique_check, pure,
            decide_eq_true_iff, Rnd_NE_pt]
      using huniq ⟨tie_unique_NE_pred, hNE1, hNE2⟩
  exact this

/-- Check nearest-even rounding uniqueness for specific values
    Decides whether two NE-points at a fixed x are equal. -/
noncomputable def Rnd_NE_pt_unique_specific_check (x f1 f2 : ℝ) : Bool :=
    @decide (f1 = f2) (Classical.dec _)

/-- Specification: Nearest-even rounding is unique

    For any real number, there is at most one value that
    satisfies the nearest-even rounding predicate.
-/
theorem Rnd_NE_pt_unique (x f1 f2 : ℝ) :
    ⦃⌜beta > 1 ∧ Rnd_NE_pt beta fexp x f1 ∧ Rnd_NE_pt beta fexp x f2⌝⦄
    (pure (Rnd_NE_pt_unique_specific_check x f1 f2) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  simp [wp, PostCond.noThrow, pure]
  unfold Rnd_NE_pt_unique_specific_check
  classical
  -- Reduce to equality for this specific x.
  simp [decide_eq_true_iff]
  rcases h with ⟨hβ, hNE1, hNE2⟩
  -- Shorthand
  let F : ℝ → Prop := fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y
  let P : ℝ → ℝ → Prop := NE_prop beta fexp
  -- Reuse the tie uniqueness proof (coerced to `Round_pred` aliases).
  have tie_unique_NE :
      ∀ x d u,
        FloatSpec.Core.Defs.Rnd_DN_pt F x d →
        FloatSpec.Core.Defs.Rnd_N_pt F x d →
        FloatSpec.Core.Defs.Rnd_UP_pt F x u →
        FloatSpec.Core.Defs.Rnd_N_pt F x u →
        P x d → P x u → d = u := by
    intro x d u hDN hN_d hUP hN_u hP_d hP_u
    exact tie_unique_NE_ax (beta := beta) (fexp := fexp) (hβ := hβ) (x := x) (d := d) (u := u)
      hDN hN_d hUP hN_u hP_d hP_u
  have tie_unique_NE_pred :
      ∀ x d u,
        FloatSpec.Core.Round_pred.Rnd_DN_pt F x d →
        FloatSpec.Core.Round_pred.Rnd_N_pt F x d →
        FloatSpec.Core.Round_pred.Rnd_UP_pt F x u →
        FloatSpec.Core.Round_pred.Rnd_N_pt F x u →
        P x d → P x u → d = u := by
    intro x d u h1 h2 h3 h4 hp1 hp2
    exact tie_unique_NE x d u h1 h2 h3 h4 hp1 hp2
  -- Conclude with the generic NG uniqueness spec at this x.
  have huniq := FloatSpec.Core.Round_pred.Rnd_NG_pt_unique_spec
      (F := F) (P := P) (x := x) (f1 := f1) (f2 := f2)
  have : f1 = f2 := by
    simpa [FloatSpec.Core.Round_pred.Rnd_NG_pt_unique_check, pure,
            decide_eq_true_iff, Rnd_NE_pt]
      using huniq ⟨tie_unique_NE_pred, hNE1, hNE2⟩
  exact this

/-- Check nearest-even monotonicity
-/
noncomputable def Rnd_NE_pt_monotone_check : Bool :=
    @decide (round_pred_monotone (Rnd_NE_pt beta fexp)) (Classical.dec _)



/-- Coq:
    Theorem {name}`Rnd_NE_pt_monotone` :
      {name (full := Defs.round_pred_monotone)}`round_pred_monotone`
      applied to {name}`Rnd_NE_pt`.

    Specification: Nearest-even rounding is monotone

    The nearest-even rounding preserves the ordering of inputs.
-/
theorem Rnd_NE_pt_monotone :
    ⦃⌜beta > 1⌝⦄
    (pure (Rnd_NE_pt_monotone_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hβ
  simp [wp, PostCond.noThrow, pure]
  unfold Rnd_NE_pt_monotone_check
  classical
  -- Reduce to the decidable statement for monotonicity of NG with NE tie-breaking.
  -- Shorthand for format predicate and NE tie-breaking.
  let F : ℝ → Prop := fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y
  let P : ℝ → ℝ → Prop := NE_prop beta fexp
  -- Apply the generic NG-point monotonicity spec, supplying NE tie-uniqueness.
  have hNGmono := FloatSpec.Core.Round_pred.Rnd_NG_pt_monotone_spec (F := F) (P := P)
  -- NE tie uniqueness (coerced to the aliases in Round_pred)
  have hTieUnique : ∀ x d u,
      FloatSpec.Core.Round_pred.Rnd_DN_pt F x d →
      FloatSpec.Core.Round_pred.Rnd_N_pt F x d →
      FloatSpec.Core.Round_pred.Rnd_UP_pt F x u →
      FloatSpec.Core.Round_pred.Rnd_N_pt F x u →
      P x d → P x u → d = u := by
    intro x d u hDN hN_d hUP hN_u hPd hPu
    exact tie_unique_NE_ax (beta := beta) (fexp := fexp) (hβ := hβ) (x := x) (d := d) (u := u)
      hDN hN_d hUP hN_u hPd hPu
  -- Finish by rewriting Rnd_NE_pt to Rnd_NG_pt F P.
  simpa [FloatSpec.Core.Round_pred.Rnd_NG_pt_monotone_check, pure,
         Rnd_NE_pt]
    using (hNGmono hTieUnique)

/-- Check nearest-even totality -/
noncomputable def Rnd_NE_pt_total_check : Bool :=
  by
    classical
    -- Decide totality of the nearest-even rounding predicate.
    exact @decide (round_pred_total (Rnd_NE_pt beta fexp)) (Classical.dec _)


/-- Coq:
    Theorem {name}`Rnd_NE_pt_total` :
      {name (full := Defs.round_pred_total)}`round_pred_total`
      applied to {name}`Rnd_NE_pt`.

    Nearest-even rounding predicate is total.
-/
theorem Rnd_NE_pt_total :
    ⦃⌜beta > 1⌝⦄
    (pure (Rnd_NE_pt_total_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hβ
  unfold Rnd_NE_pt_total_check
  classical
  -- Reduce the Hoare triple to the propositional totality statement.
  simp [ pure, decide_eq_true_iff, Defs.round_pred_total]
  -- Shorthands
  intro x
  let F : ℝ → Prop := fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y
  let P : ℝ → ℝ → Prop := NE_prop beta fexp
  -- Case split on whether x itself is representable.
  have hxEM := FloatSpec.Core.Generic_fmt.generic_format_EM (beta := beta) (fexp := fexp) x
  cases hxEM with
  | inl hxF =>
      -- x is representable: the reflexivity property gives an NG-point at x.
      have hrefl := FloatSpec.Core.Round_pred.Rnd_NG_pt_refl_spec (F := F) (P := P) (x := x)
      have : FloatSpec.Core.Defs.Rnd_NG_pt F P x x := by
        simpa [FloatSpec.Core.Round_pred.Rnd_NG_pt_refl_check, pure,
               decide_eq_true_iff] using (hrefl hxF)
      exact ⟨x, this⟩
  | inr hxNotF =>
      -- x is not representable: obtain DN and UP witnesses, then choose an NE tie-break in case of a tie.
      -- DN/UP witnesses exist in the generic format.
      obtain ⟨xd, hFxd, hDN⟩ :=
        FloatSpec.Core.Generic_fmt.round_DN_exists (beta := beta) (fexp := fexp) (x := x) (hβ := hβ)
      obtain ⟨xu, hFxu, hUP⟩ :=
        FloatSpec.Core.Generic_fmt.round_UP_exists (beta := beta) (fexp := fexp) (x := x) (hβ := hβ)
      -- Compare the two distances to decide which side is nearest.
      -- Distances (nonnegative by construction)
      have hxd_le_x : xd ≤ x := hDN.2.1
      have hx_le_xu : x ≤ xu := hUP.2.1
      have hdist_cases := le_total (x - xd) (xu - x)
      cases hdist_cases with
      | inl hL =>
          -- Left distance no larger: DN is a nearest point.
          have hN_dn := FloatSpec.Core.Round_pred.Rnd_N_pt_DN_spec (F := F) (x := x) (d := xd) (u := xu)
          have hNxd : FloatSpec.Core.Defs.Rnd_N_pt F x xd := by
            -- Apply the DN-nearest spec using the distance inequality.
            simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_DN_check, pure,
                   decide_eq_true_iff] using hN_dn ⟨hDN, hUP, hL⟩
          -- If the inequality is strict, uniqueness-of-nearest discharges the NG tie condition.
          by_cases hstrict : (x - xd) ≠ (xu - x)
          · -- Unique nearest: use the uniqueness branch of NG.
            -- Any nearest point equals xd by uniqueness.
            have huniq_xd : ∀ f2, FloatSpec.Core.Defs.Rnd_N_pt F x f2 → f2 = xd := by
              intro f2 hf2
              have huniq := FloatSpec.Core.Round_pred.Rnd_N_pt_unique_spec (F := F) (x := x) (d := xd) (u := xu) (f1 := xd) (f2 := f2)
              have hres := huniq ⟨hDN, hUP, hstrict, hNxd, hf2⟩
              -- Convert boolean check result back to equality
              simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_unique_check, pure,
                     decide_eq_true_iff, eq_comm]
                using hres
            exact ⟨xd, And.intro hNxd (Or.inr huniq_xd)⟩
          · -- Tie case: choose the even-mantissa endpoint using the parity lemma.
            have hEq : (x - xd) = (xu - x) := by
              -- From ¬(x - xd ≠ xu - x) we get equality by classical logic.
              have : ¬ ((x - xd) ≠ (xu - x)) := hstrict
              exact Classical.not_not.mp (by simpa using this)
            -- Obtain canonical representatives for xd and xu with opposite parity.
            have hpar_all := DN_UP_parity_generic (beta := beta) (fexp := fexp)
            have hpar : DN_UP_parity_prop beta fexp := by
              -- Consume the triple-style lemma to a pure proposition.
              have H := hpar_all hβ
              simpa [DN_UP_parity_generic_check, pure,
                     decide_eq_true_iff]
                using H
            rcases hpar x xd xu hxNotF hDN hUP with
              ⟨gd, gu, hxd_eq, hxu_eq, hcanon_d, hcanon_u, hparity⟩
            -- Exactly one of gd.Fnum and gu.Fnum is even; pick the corresponding endpoint.
            have hgd_even_or_gu_even : (gd.Fnum % 2 = 0) ∨ (gu.Fnum % 2 = 0) := by
              -- Since residues modulo 2 are either 0 or 1, different residues imply one is 0.
              rcases Int.emod_two_eq_zero_or_one gd.Fnum with hgd0 | hgd1
              · exact Or.inl hgd0
              · rcases Int.emod_two_eq_zero_or_one gu.Fnum with hgu0 | hgu1
                · exact Or.inr hgu0
                · -- gd % 2 = 1 and gu % 2 = 1 contradict parity difference.
                  have : gd.Fnum % 2 = gu.Fnum % 2 := by simpa [hgd1, hgu1]
                  exact (hparity this).elim
            -- Build the NE witness using the chosen even endpoint.
            cases hgd_even_or_gu_even with
            | inl hEven =>
                -- Choose f = xd, realized by gd with even mantissa.
                have hNE : P x xd := by
                  -- NE_prop holds via the canonical float gd with even mantissa.
                  refine ⟨gd, ?_, hcanon_d, ?_⟩
                  · simpa using hxd_eq
                  · simpa using hEven
                -- Nearest in tie is satisfied (DN branch), NG holds via P.
                exact ⟨xd, And.intro hNxd (Or.inl hNE)⟩
            | inr hEven =>
                -- Choose f = xu, realized by gu with even mantissa.
                -- Show nearest for xu from the symmetric inequality.
                have hR : (xu - x) ≤ (x - xd) := by simpa [hEq]
                have hN_up := FloatSpec.Core.Round_pred.Rnd_N_pt_UP_spec (F := F) (x := x) (d := xd) (u := xu)
                have hNxu : FloatSpec.Core.Defs.Rnd_N_pt F x xu := by
                  simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_UP_check, pure,
                         decide_eq_true_iff] using hN_up ⟨hDN, hUP, hR⟩
                have hNE : P x xu := by
                  refine ⟨gu, ?_, hcanon_u, ?_⟩
                  · simpa using hxu_eq
                  · simpa using hEven
                exact ⟨xu, And.intro hNxu (Or.inl hNE)⟩
      | inr hR =>
          -- Right distance no larger: symmetric to the previous branch.
          have hN_up := FloatSpec.Core.Round_pred.Rnd_N_pt_UP_spec (F := F) (x := x) (d := xd) (u := xu)
          have hNxu : FloatSpec.Core.Defs.Rnd_N_pt F x xu := by
            simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_UP_check, pure,
                   decide_eq_true_iff] using hN_up ⟨hDN, hUP, hR⟩
          by_cases hstrict : (xu - x) ≠ (x - xd)
          · -- Unique nearest on the UP side.
            have huniq_xu : ∀ f2, FloatSpec.Core.Defs.Rnd_N_pt F x f2 → f2 = xu := by
              intro f2 hf2
              have huniq := FloatSpec.Core.Round_pred.Rnd_N_pt_unique_spec (F := F) (x := x) (d := xd) (u := xu) (f1 := xu) (f2 := f2)
              -- Flip the inequality orientation to match the lemma statement.
              have hstrict' : (x - xd) ≠ (xu - x) := by simpa [eq_comm] using hstrict
              have hres := huniq ⟨hDN, hUP, hstrict', hNxu, hf2⟩
              simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_unique_check, pure,
                     decide_eq_true_iff, eq_comm]
                using hres
            exact ⟨xu, And.intro hNxu (Or.inr huniq_xu)⟩
          · -- Tie case on the right: use parity to pick the even endpoint.
            have hEq : (xu - x) = (x - xd) := by
              have : ¬ ((xu - x) ≠ (x - xd)) := by
                -- `hstrict` is `¬(xu - x ≠ x - xd)` since we are in the negated branch.
                -- Coerce by symmetry.
                simpa [eq_comm] using hstrict
              exact Classical.not_not.mp (by simpa using this)
            -- Parity lemma as above.
            have hpar_all := DN_UP_parity_generic (beta := beta) (fexp := fexp)
            have hpar : DN_UP_parity_prop beta fexp := by
              have H := hpar_all hβ
              simpa [DN_UP_parity_generic_check, pure,
                     decide_eq_true_iff]
                using H
            rcases hpar x xd xu hxNotF hDN hUP with
              ⟨gd, gu, hxd_eq, hxu_eq, hcanon_d, hcanon_u, hparity⟩
            have hgd_even_or_gu_even : (gd.Fnum % 2 = 0) ∨ (gu.Fnum % 2 = 0) := by
              rcases Int.emod_two_eq_zero_or_one gd.Fnum with hgd0 | hgd1
              · exact Or.inl hgd0
              · rcases Int.emod_two_eq_zero_or_one gu.Fnum with hgu0 | hgu1
                · exact Or.inr hgu0
                · have : gd.Fnum % 2 = gu.Fnum % 2 := by simpa [hgd1, hgu1]
                  exact (hparity this).elim
            cases hgd_even_or_gu_even with
            | inl hEven =>
                -- Choose xd via gd.
                have hNxd : FloatSpec.Core.Defs.Rnd_N_pt F x xd := by
                  -- Convert the equality of distances to the DN inequality and reuse the spec.
                  have hL : (x - xd) ≤ (xu - x) := by simpa [hEq] using le_of_eq hEq
                  have h := FloatSpec.Core.Round_pred.Rnd_N_pt_DN_spec (F := F) (x := x) (d := xd) (u := xu)
                  simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_DN_check, pure,
                         decide_eq_true_iff] using h ⟨hDN, hUP, hL⟩
                have hNE : P x xd := by
                  refine ⟨gd, ?_, hcanon_d, ?_⟩
                  · simpa using hxd_eq
                  · simpa using hEven
                exact ⟨xd, And.intro hNxd (Or.inl hNE)⟩
            | inr hEven =>
                -- Choose xu via gu.
                have hNxu' : FloatSpec.Core.Defs.Rnd_N_pt F x xu := by
                  have hR' : (xu - x) ≤ (x - xd) := by simpa [hEq] using le_of_eq hEq
                  have h := FloatSpec.Core.Round_pred.Rnd_N_pt_UP_spec (F := F) (x := x) (d := xd) (u := xu)
                  simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_UP_check, pure,
                         decide_eq_true_iff] using h ⟨hDN, hUP, hR'⟩
                have hNE : P x xu := by
                  refine ⟨gu, ?_, hcanon_u, ?_⟩
                  · simpa using hxu_eq
                  · simpa using hEven
                exact ⟨xu, And.intro hNxu' (Or.inl hNE)⟩

/-- Check nearest-even forms a rounding predicate -/
noncomputable def Rnd_NE_pt_round_check : Bool :=
  by
    classical
    -- Decide that nearest-even defines a proper rounding predicate.
    exact @decide (round_pred (Rnd_NE_pt beta fexp)) (Classical.dec _)


/-- Coq:
    Theorem Rnd_NE_pt_round :
      round_pred Rnd_NE_pt.

    Nearest-even rounding predicate satisfies totality and monotonicity.
-/
theorem Rnd_NE_pt_round :
    ⦃⌜beta > 1⌝⦄
    (pure (Rnd_NE_pt_round_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NE_pt_round_check
  classical
  -- Reduce to proving `round_pred (Rnd_NE_pt beta fexp)`.
  simp [ pure, decide_eq_true_iff, FloatSpec.Core.Defs.round_pred]
  -- It suffices to show totality and monotonicity separately.
  constructor
  · -- Totality from the dedicated lemma.
    have hTot := Rnd_NE_pt_total (beta := beta) (fexp := fexp)
    -- Consume the triple-style lemma to a pure proposition.
    simpa [Rnd_NE_pt_total_check, pure, decide_eq_true_iff]
      using (hTot ‹beta > 1›)
  · -- Monotonicity from the dedicated lemma.
    have hMono := Rnd_NE_pt_monotone (beta := beta) (fexp := fexp)
    simpa [Rnd_NE_pt_monotone_check, pure, decide_eq_true_iff]
      using (hMono ‹beta > 1›)

end UniquenessProperties

section RoundingPredicateProperties

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
variable [Exists_NE beta fexp]

/-- Check rounding predicate satisfaction
-/
noncomputable def satisfies_any_imp_NE_check : Bool :=
  by
    classical
    -- Decide that nearest-even forms a proper rounding predicate under the
    -- `satisfies_any` hypothesis on the format.
    exact @decide (round_pred (Rnd_NE_pt beta fexp)) (Classical.dec _)

/-- Specification: Nearest-even satisfies rounding predicate

    When the format satisfies the "satisfies-any" property,
    nearest-even rounding forms a proper rounding predicate.
-/
theorem satisfies_any_imp_NE :
    ⦃⌜beta > 1 ∧
      FloatSpec.Core.Generic_fmt.satisfies_any
        (fun x => FloatSpec.Core.Generic_fmt.generic_format beta fexp x)⌝⦄
    (pure (satisfies_any_imp_NE_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  classical
  -- The goal is exactly `round_pred (Rnd_NE_pt beta fexp)`,
  -- which was established in `Rnd_NE_pt_round` under `beta > 1`.
  have hβ : beta > 1 := (show beta > 1 ∧ _ from ‹beta > 1 ∧ _›).left
  have h := Rnd_NE_pt_round (beta := beta) (fexp := fexp)
  -- Both checks compute the same boolean, so we can discharge by `simpa`.
  simpa [satisfies_any_imp_NE_check, Rnd_NE_pt_round_check]
    using (h hβ)

/-- Check nearest-even reflexivity
-/
noncomputable def Rnd_NE_pt_refl_check : Bool :=
  by
    classical
    -- Representable values are fixed points of nearest-even rounding.
    exact
      @decide
        (∀ x : ℝ,
          FloatSpec.Core.Generic_fmt.generic_format beta fexp x →
          Rnd_NE_pt beta fexp x x)
        (Classical.dec _)


/-- Coq:
    {coq}`Rnd_NG_pt_refl` specialized to {name}`Rnd_NE_pt`
    (implicit in Coq proof of {coq}`round_NE_pt`).

    Specification: Nearest-even rounding is reflexive on format

    If x is already in the format, then rounding x gives x itself.
-/
theorem Rnd_NE_pt_refl (x : ℝ) :
    ⦃⌜beta > 1 ∧ FloatSpec.Core.Generic_fmt.generic_format beta fexp x⌝⦄
    (pure (Rnd_NE_pt_refl_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NE_pt_refl_check
  classical
  -- Reduce to proving the universal reflexivity property directly.
  simp [ pure, decide_eq_true_iff]
  -- Show: ∀ x, if x is representable, then it is its own NE-rounding.
  intro x hxF
  -- Shorthands for the generic format predicate and NE tie-breaking.
  let F : ℝ → Prop := fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y
  let P : ℝ → ℝ → Prop := NE_prop beta fexp
  -- Use the generic NG reflexivity spec and rewrite to Rnd_NE_pt.
  have hrefl := FloatSpec.Core.Round_pred.Rnd_NG_pt_refl_spec (F := F) (P := P) (x := x)
  have : FloatSpec.Core.Defs.Rnd_NG_pt F P x x := by
    simpa [FloatSpec.Core.Round_pred.Rnd_NG_pt_refl_check, pure,
           decide_eq_true_iff] using (hrefl hxF)
  simpa [Rnd_NE_pt] using this

/-- Check nearest-even idempotence
-/
noncomputable def Rnd_NE_pt_idempotent_check : Bool :=
  by
    classical
    -- If x is representable and f rounds to x under NE, then f = x.
    exact
      @decide
        (∀ x f : ℝ,
          Rnd_NE_pt beta fexp x f →
          FloatSpec.Core.Generic_fmt.generic_format beta fexp x →
          f = x)
        (Classical.dec _)


/-- Coq:
    {coq}`Rnd_NG_pt_idempotent` specialized (implicit in Coq lemmas around Rnd predicates).

    Specification: Nearest-even rounding is idempotent

    If x is in the format and f is its rounding, then f = x.
-/
theorem Rnd_NE_pt_idempotent (x f : ℝ) :
    ⦃⌜beta > 1 ∧ Rnd_NE_pt beta fexp x f ∧ FloatSpec.Core.Generic_fmt.generic_format beta fexp x⌝⦄
    (pure (Rnd_NE_pt_idempotent_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NE_pt_idempotent_check
  classical
  -- Reduce the Hoare triple on `Id` to a propositional goal about `decide`.
  -- Target: ∀ x f, Rnd_NE_pt x f → F x → f = x
  simp [ pure, decide_eq_true_iff]
  -- Prove the property for arbitrary `x` and `f`.
  intro x f hNE hxF
  -- Shorthand for the format predicate used throughout this file.
  let F : ℝ → Prop := fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y
  -- From NG, extract the nearest property.
  have hN : FloatSpec.Core.Defs.Rnd_N_pt F x f := (And.left hNE)
  -- Apply the generic idempotency of nearest rounding on representables.
  have h := FloatSpec.Core.Round_pred.Rnd_N_pt_idempotent_spec (F := F) (x := x) (f := f)
  simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_idempotent_check, pure,
         decide_eq_true_iff]
    using h ⟨hN, hxF⟩

end RoundingPredicateProperties

section ParityProperties

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
variable [Exists_NE beta fexp]

/-- Check down-up parity property
-/
noncomputable def DN_UP_parity_pos_holds_check : Bool :=
  by
    classical
    -- Decide the positive-case parity property for DN/UP neighbors.
    exact @decide (DN_UP_parity_pos_prop beta fexp) (Classical.dec _)

/-- Specification: Down-up parity for positive numbers

    Validates that the parity property holds for the format,
    ensuring nearest-even tie-breaking is well-defined.

    Coq:
    Theorem DN_UP_parity_generic_pos :
      DN_UP_parity_pos_prop.
-/
theorem DN_UP_parity_pos_holds :
    -- Coq: Theorem DN_UP_parity_generic_pos : DN_UP_parity_pos_prop.
    ⦃⌜beta > 1⌝⦄
    (pure (DN_UP_parity_pos_holds_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold DN_UP_parity_pos_holds_check
  classical
  -- Reduce the Hoare triple on `Id` to a propositional goal about `decide`.
  -- Target: DN_UP_parity_pos_prop beta fexp
  simp [ pure, decide_eq_true_iff]
  -- Obtain the positive-case parity property from the previously proven theorem.
  have h := DN_UP_parity_generic_pos (beta := beta) (fexp := fexp)
  -- Consume its precondition and convert its boolean result to the proposition.
  simpa [DN_UP_parity_generic_pos_check, pure, decide_eq_true_iff]
    using (h (by assumption))

/-- Check sign preservation
-/
noncomputable def Rnd_NE_pt_sign_check : Bool :=
  by
    classical
    -- Decide sign preservation: if Rnd_NE_pt x f with x ≠ 0 and 0 < f, then 0 < x.
    exact
      @decide
        (∀ x f : ℝ,
          Rnd_NE_pt beta fexp x f → x ≠ 0 → 0 < f → 0 < x)
        (Classical.dec _)

/-- Coq: Derived from {coq}`round_NE_pt_pos` and symmetry; sign preserved except zeros.

    Specification: Nearest-even preserves sign

    The sign of the result matches the sign of the input
    (except potentially for signed zeros).
-/
theorem Rnd_NE_pt_sign (x f : ℝ) :
    ⦃⌜beta > 1 ∧ Rnd_NE_pt beta fexp x f ∧ x ≠ 0 ∧ 0 < f⌝⦄
    (pure (Rnd_NE_pt_sign_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hpre
  unfold Rnd_NE_pt_sign_check
  classical
  -- Reduce to proving the underlying proposition.
  simp [ pure, decide_eq_true_iff]
  -- Unpack the precondition to extract `beta > 1` (the rest is unused here).
  rcases hpre with ⟨hβ, _hRnd, _hxne, _hfpos⟩
  -- Zero is representable in the generic format.
  have hF0 : FloatSpec.Core.Generic_fmt.generic_format beta fexp 0 := by
    have h := FloatSpec.Core.Generic_fmt.generic_format_0 (beta := beta) (fexp := fexp)
    simpa using (h hβ)
  -- Prove the sign-preservation property for arbitrary `x f`.
  intro x f hNE hxne hfpos
  -- Extract the nearest component from the NG predicate.
  have hN : FloatSpec.Core.Round_pred.Rnd_N_pt
      (fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y) x f := hNE.1
  -- Show that `x` cannot be nonpositive, otherwise `f ≤ 0` contradicts `0 < f`.
  have hx_not_le : ¬ x ≤ 0 := by
    intro hxle
    -- From nonpositivity of `x`, nearest rounding yields `f ≤ 0`.
    have hf_le0 : f ≤ 0 := by
      have hspec :=
        FloatSpec.Core.Round_pred.Rnd_N_pt_le_0_spec
          (F := fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y)
          (x := x) (f := f)
      -- Consume its preconditions and read back the propositional payload.
      have := hspec ⟨hF0, hxle, hN⟩
      simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_le_0_check, pure, decide_eq_true_iff] using this
    exact (not_le.mpr hfpos) hf_le0
  -- Hence `0 < x`.
  exact lt_of_not_ge hx_not_le

/-- Check absolute value property
-/
noncomputable def Rnd_NE_pt_abs_check : Bool :=
  by
    classical
    -- Decide absolute-value stability: rounding relates |x| to |f| as well.
    exact
      @decide
        (∀ x f : ℝ,
          Rnd_NE_pt beta fexp x f →
          Rnd_NE_pt beta fexp (abs x) (abs f))
        (Classical.dec _)


/-- Coq:
    Lemma round_NE_abs:
      forall x : R,
      round beta fexp ZnearestE (Rabs x) =
      Rabs (round beta fexp ZnearestE x).

    Specification: Nearest-even absolute value property

    Rounding preserves relationships with absolute values.
-/
theorem Rnd_NE_pt_abs (x f : ℝ) :
    ⦃⌜beta > 1 ∧ Rnd_NE_pt beta fexp x f⌝⦄
    (pure (Rnd_NE_pt_abs_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hpre
  unfold Rnd_NE_pt_abs_check
  classical
  -- Reduce the Hoare triple on `Id` to a propositional goal about `decide`.
  -- Target: ∀ x f, Rnd_NE_pt x f → Rnd_NE_pt |x| |f|
  simp [ pure, decide_eq_true_iff]
  -- Work with generic-format predicate and the NE tie-breaking predicate.
  intro x f hNE
  let F : ℝ → Prop := fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y
  let P : ℝ → ℝ → Prop := NE_prop beta fexp
  -- Basic facts: 0 is representable and `F` is closed under negation.
  have hβ : 1 < beta := by
    rcases hpre with ⟨hβ, _⟩; exact hβ
  have hF0 : F 0 := by
    have h := FloatSpec.Core.Generic_fmt.generic_format_0 (beta := beta) (fexp := fexp)
    simpa using (h hβ)
  have Fopp : ∀ y, F y → F (-y) := by
    intro y hy
    simpa using (FloatSpec.Core.Generic_fmt.generic_format_opp (beta := beta) (fexp := fexp) (x := y) hy)
  -- Helper: NE predicate is sign-symmetric on the output value.
  have Popp : ∀ x f, P x f → P (-x) (-f) := by
    intro _x _f hP
    rcases hP with ⟨g, hf, hcanon, heven⟩
    -- Candidate for (-f) is the float with negated mantissa.
    let gneg : FlocqFloat beta := ⟨-g.Fnum, g.Fexp⟩
    -- Real value equality via F2R_Zopp
    have hF2Rneg : -(F2R g) = (F2R gneg) := by
      exact FloatSpec.Core.Float_prop.F2R_Zopp (beta := beta) (f := g) (hbeta := hβ)
    -- Parity invariance under negation (mod 2)
    have neg_mod_two (n : Int) : (-n) % 2 = n % 2 := by
      rcases Int.emod_two_eq_zero_or_one n with hn0 | hn1
      · have : (-n) % 2 = 0 := by
          rcases Int.emod_two_eq_zero_or_one (-n) with hneg0 | hneg1
          · exact hneg0
          · exact False.elim (by
              have : (1 : Int) ≠ 0 := by decide
              exact this (by simpa [hn0] using hneg1))
        simpa [hn0, this]
      · have : (-n) % 2 = 1 := by
          rcases Int.emod_two_eq_zero_or_one (-n) with hneg0 | hneg1
          · exact False.elim (by
              have : (0 : Int) ≠ 1 := by decide
              exact this (by simpa [hn1] using hneg0))
          · exact hneg1
        simpa [hn1, this]
    have heavneg : gneg.Fnum % 2 = 0 := by simpa [gneg, neg_mod_two] using heven
    -- Canonical preserved by mantissa negation
    have hcanon_neg : canonical beta fexp gneg :=
      FloatSpec.Core.Generic_fmt.canonical_opp (beta := beta) (fexp := fexp)
        (m := g.Fnum) (e := g.Fexp) hcanon
    -- Assemble
    refine ⟨gneg, ?_, hcanon_neg, by simpa [gneg] using heavneg⟩
    have : -_f = -(F2R g) := by simpa [hf]
    simpa [this] using hF2Rneg
  -- Build nearest at |x| for |f| using the absolute-value spec for nearest.
  have hNabs : FloatSpec.Core.Defs.Rnd_N_pt F |x| |f| := by
    have h := FloatSpec.Core.Round_pred.Rnd_N_pt_abs_spec (F := F) (x := x) (f := f)
    simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_abs_check, pure,
           decide_eq_true_iff]
      using h ⟨hF0, Fopp, hNE.1⟩
  -- We now establish the tie side for NG at |x|,|f|.
  -- If the original had a tie with NE property, push it through absolute value.
  have hTie : P |x| |f| ∨ ∀ f2 : ℝ, FloatSpec.Core.Defs.Rnd_N_pt F |x| f2 → f2 = |f| := by
    cases hNE.2 with
    | inl hP_xf =>
        -- Transform NE witness for f into a witness for |f|.
        rcases hP_xf with ⟨g, hf, hcanon, heven⟩
        -- Choose witness for |f| by cases on the sign of f.
        by_cases hf_nonneg : 0 ≤ f
        · -- Nonnegative f: take the same float `g` as witness.
          let gabs : FlocqFloat beta := g
          have hf_abs : |f| = (F2R gabs) := by
            have hf' : (F2R g) = f := by simpa using hf.symm
            have hg_nonneg : 0 ≤ (F2R g) := by
              -- Since f = F2R g and f ≥ 0, we have F2R g ≥ 0
              rw [hf']; exact hf_nonneg
            calc |f| = |((F2R g))| := by rw [← hf']
                 _ = (F2R g) := abs_of_nonneg hg_nonneg
                 _ = (F2R gabs) := by rfl
          -- Parity and canonicality carry over directly.
          have hcanon_abs : canonical beta fexp gabs := by simpa [gabs] using hcanon
          have heav_abs : gabs.Fnum % 2 = 0 := by simpa [gabs] using heven
          exact Or.inl ⟨gabs, hf_abs, hcanon_abs, heav_abs⟩
        · -- Negative f: use the opposite float as witness.
          let gabs : FlocqFloat beta := ⟨-g.Fnum, g.Fexp⟩
          have hf_abs : |f| = (F2R gabs) := by
            have hf' : f = (F2R g) := hf
            have hg_neg : (F2R g) < 0 := by
              have h : f < 0 := lt_of_not_ge hf_nonneg
              rw [hf'] at h; exact h
            have hfneg : |f| = -(F2R g) := by
              calc |f| = |((F2R g))| := by rw [← hf']
                   _ = -(F2R g) := abs_of_neg hg_neg
            have hF2Rneg : -(F2R g) = (F2R gabs) := by
              simpa [gabs] using (FloatSpec.Core.Float_prop.F2R_Zopp (beta := beta) (f := g) (hbeta := hβ))
            calc |f| = -(F2R g) := hfneg
                 _ = (F2R gabs) := hF2Rneg
          -- Canonicality preserved under mantissa negation; parity invariant modulo 2.
          have hcanon_abs : canonical beta fexp gabs :=
            FloatSpec.Core.Generic_fmt.canonical_opp (beta := beta) (fexp := fexp)
              (m := g.Fnum) (e := g.Fexp) hcanon
          have neg_mod_two (n : Int) : (-n) % 2 = n % 2 := by
            rcases Int.emod_two_eq_zero_or_one n with hn0 | hn1
            · have : (-n) % 2 = 0 := by
                rcases Int.emod_two_eq_zero_or_one (-n) with hneg0 | hneg1
                · exact hneg0
                · exact False.elim (by
                    have : (1 : Int) ≠ 0 := by decide
                    exact this (by simpa [hn0] using hneg1))
              simpa [hn0, this]
            · have : (-n) % 2 = 1 := by
                rcases Int.emod_two_eq_zero_or_one (-n) with hneg0 | hneg1
                · exact False.elim (by
                    have : (0 : Int) ≠ 1 := by decide
                    exact this (by simpa [hn1] using hneg0))
                · exact hneg1
              simpa [hn1, this]
          have heav_abs : gabs.Fnum % 2 = 0 := by simpa [gabs, neg_mod_two] using heven
          exact Or.inl ⟨gabs, hf_abs, hcanon_abs, heav_abs⟩

    | inr huniq_x =>
        -- Uniqueness branch: deduce sign of f from `x` and transfer uniqueness.
        by_cases hx : 0 ≤ x
        · -- Nonnegative x: f is nonnegative, hence |f| = f and uniqueness transfers.
          have hf_nonneg : 0 ≤ f := by
            have h := FloatSpec.Core.Round_pred.Rnd_N_pt_ge_0_spec (F := F) (x := x) (f := f)
            simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_ge_0_check, pure,
                   decide_eq_true_iff, hx] using h ⟨hF0, hx, hNE.1⟩
          have : ∀ f2 : ℝ, FloatSpec.Core.Defs.Rnd_N_pt F |x| f2 → f2 = |f| := by
            intro f2 hNf2
            -- Here |x| = x; use uniqueness at x.
            have hxabs : |x| = x := by simpa [abs_of_nonneg hx]
            have : FloatSpec.Core.Defs.Rnd_N_pt F x f2 := by simpa [hxabs] using hNf2
            have hf2_eq_f : f2 = f := huniq_x f2 this
            simpa [abs_of_nonneg hf_nonneg] using hf2_eq_f
          exact Or.inr this
        · -- Nonpositive x: reduce to the nonnegative case on (-x,-f), then rewrite abs.
          have hxle0 : x ≤ 0 := le_of_not_ge hx
          -- Nearest at (-x,-f) via opposite invariance on nearest.
          have hNneg : FloatSpec.Core.Defs.Rnd_N_pt F (-x) (-f) := by
            have h := FloatSpec.Core.Round_pred.Rnd_N_pt_opp_inv_spec (F := F) (x := -x) (f := -f)
            simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_opp_inv_check, pure,
                   decide_eq_true_iff, neg_neg]
              using h Fopp (by simpa [neg_neg] using hNE.1) trivial
          -- Apply the nonnegative-x argument at (-x,-f) and rewrite abs.
          have hxnonneg' : 0 ≤ -x := by simpa using neg_nonneg.mpr hxle0
          have hf_nonneg' : 0 ≤ -f := by
            have h := FloatSpec.Core.Round_pred.Rnd_N_pt_ge_0_spec (F := F) (x := -x) (f := -f)
            simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_ge_0_check, pure,
                   decide_eq_true_iff, hxnonneg'] using h ⟨hF0, hxnonneg', hNneg⟩
          have : ∀ f2 : ℝ, FloatSpec.Core.Defs.Rnd_N_pt F |x| f2 → f2 = |f| := by
            intro f2 hNf2_abs
            -- Here |x| = -x, and |f| = -f by nonpositivity of f.
            have hxabs : |x| = -x := by simpa [abs_of_nonpos hxle0]
            have hfabs : |f| = -f := by
              have hf_le0 : f ≤ 0 := by simpa using (neg_nonneg.mp hf_nonneg')
              simpa [abs_of_nonpos hf_le0]
            -- Convert nearest at |x| to nearest at -x and use uniqueness at -x.
            have hNf2_neg : FloatSpec.Core.Defs.Rnd_N_pt F (-x) f2 := by simpa [hxabs] using hNf2_abs
            -- Uniqueness at -x from uniqueness at x by mapping with opp-inv.
            have huniq_neg : ∀ g, FloatSpec.Core.Defs.Rnd_N_pt F (-x) g → g = -f := by
              intro g hNg
              -- Map to x using opp-inv and apply uniqueness at x.
              have hN_at_x : FloatSpec.Core.Defs.Rnd_N_pt F x (-g) := by
                have h := FloatSpec.Core.Round_pred.Rnd_N_pt_opp_inv_spec (F := F) (x := x) (f := -g)
                simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_opp_inv_check, pure,
                       decide_eq_true_iff]
                  using h Fopp (by simp; exact hNg) trivial
              have := huniq_x (-g) hN_at_x
              -- From -g = f, deduce g = -f.
              have : g = -f := by
                have := congrArg Neg.neg this
                simpa using this
              exact this
            have hf2_eq_negf : f2 = -f := huniq_neg f2 hNf2_neg
            simpa [hfabs] using hf2_eq_negf
          exact Or.inr this
  -- Conclude NG at |x|, |f|.
  exact And.intro hNabs hTie

/-- Check rounding at positive inputs -/
noncomputable def round_NE_pt_pos_check : Bool :=
  by
    classical
    -- Decide existence of an NE-rounded value at positive inputs.
    exact @decide (∀ x : ℝ, 0 < x → ∃ f : ℝ, Rnd_NE_pt beta fexp x f) (Classical.dec _)


-- Helper: consume `Rnd_NE_pt_total` (triple style) into a pure proposition form.
private theorem Rnd_NE_pt_total_prop
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] [Exists_NE beta fexp]
    (hβ : beta > 1) : ∀ y : ℝ, ∃ f : ℝ, Rnd_NE_pt beta fexp y f := by
  -- Use the triple-encoded totality lemma and eliminate the Hoare wrapper by `simp`.
  have hTot := Rnd_NE_pt_total (beta := beta) (fexp := fexp)
  have := hTot hβ
  simpa [Rnd_NE_pt_total_check, pure,
         decide_eq_true_iff, FloatSpec.Core.Defs.round_pred_total]
    using this


/-- Coq:
    Lemma {coq}`round_NE_pt_pos`:
      for all x with 0 < x, Rnd_NE_pt x (round beta fexp ZnearestE x).

    Rounding to nearest-even at positive x satisfies the predicate.
-/
theorem round_NE_pt_pos (x : ℝ) :
    ⦃⌜beta > 1 ∧ 0 < x⌝⦄
    (pure (round_NE_pt_pos_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, _hxpos⟩
  unfold round_NE_pt_pos_check
  classical
  -- Reduce to the decidable statement for existence on positives.
  -- Target: ∀ x, 0 < x → ∃ f, Rnd_NE_pt x f
  simp [ pure, decide_eq_true_iff]
  -- Existence for all x follows from totality of Rnd_NE_pt.
  -- Hence, the positive case is immediate.
  intro x hxpos
  -- Obtain totality at this base from the previously established lemma.
  have hTotProp : ∀ y : ℝ, ∃ f : ℝ, Rnd_NE_pt beta fexp y f :=
    Rnd_NE_pt_total_prop (beta := beta) (fexp := fexp) hβ
  -- Specialize totality to the given positive x and conclude.
  exact hTotProp x

/-- Check rounding negation -/
noncomputable def round_NE_opp_check : Bool :=
  by
    classical
    -- Decide negation-compatibility: rounding commutes with negation at the predicate level.
    exact
      @decide
        (∀ x f : ℝ, Rnd_NE_pt beta fexp x f ↔ Rnd_NE_pt beta fexp (-x) (-f))
        (Classical.dec _)


/-- Coq:
    Theorem round_NE_opp :
      forall x,
      round beta fexp ZnearestE (-x) =
      (- round beta fexp ZnearestE x)%R.

    Rounding commutes with negation under nearest-even.
-/
theorem round_NE_opp (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    (pure (round_NE_opp_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hβ
  unfold round_NE_opp_check
  classical
  -- Reduce to the decidable equivalence statement.
  simp [ pure, decide_eq_true_iff]
  -- Work with the generic-format predicate and the NE tie-breaking predicate.
  intro x f
  let F : ℝ → Prop := fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y
  let P : ℝ → ℝ → Prop := NE_prop beta fexp
  -- Closure under opposite for the format predicate.
  have Fopp : ∀ y, F y → F (-y) := by
    intro y hy
    simpa using (FloatSpec.Core.Generic_fmt.generic_format_opp (beta := beta) (fexp := fexp) (x := y) hy)
  -- NE predicate is preserved by negation on both arguments.
  have Popp : ∀ x f, P x f → P (-x) (-f) := by
    intro _x _f hP
    rcases hP with ⟨g, hf, hcanon, heven⟩
    -- Candidate for (-f) is the float with negated mantissa.
    let gneg : FlocqFloat beta := ⟨-g.Fnum, g.Fexp⟩
    -- Real value equality via F2R_Zopp (requires 1 < beta).
    have hF2Rneg : -(F2R g) = (F2R gneg) := by
      exact FloatSpec.Core.Float_prop.F2R_Zopp (beta := beta) (f := g) (hbeta := hβ)
    -- Parity invariance under negation (mod 2).
    have neg_mod_two (n : Int) : (-n) % 2 = n % 2 := by
      rcases Int.emod_two_eq_zero_or_one n with hn0 | hn1
      · have : (-n) % 2 = 0 := by
          rcases Int.emod_two_eq_zero_or_one (-n) with hneg0 | hneg1
          · exact hneg0
          · exact False.elim (by
              have : (1 : Int) ≠ 0 := by decide
              exact this (by simpa [hn0] using hneg1))
        simpa [hn0, this]
      · have : (-n) % 2 = 1 := by
          rcases Int.emod_two_eq_zero_or_one (-n) with hneg0 | hneg1
          · exact False.elim (by
              have : (0 : Int) ≠ 1 := by decide
              exact this (by simpa [hn1] using hneg0))
          · exact hneg1
        simpa [hn1, this]
    have heavneg : gneg.Fnum % 2 = 0 := by simpa [gneg, neg_mod_two] using heven
    -- Canonicality preserved under mantissa negation.
    have hcanon_neg : canonical beta fexp gneg :=
      FloatSpec.Core.Generic_fmt.canonical_opp (beta := beta) (fexp := fexp)
        (m := g.Fnum) (e := g.Fexp) hcanon
    -- Assemble the NE witness for (-x,-f).
    refine ⟨gneg, ?_, hcanon_neg, by simpa [gneg] using heavneg⟩
    have : -_f = -(F2R g) := by simpa [hf]
    simpa [this] using hF2Rneg
  -- Prove the two implications using the NG opp-inv specification.
  constructor
  · intro hNE
    -- From Rnd_NE_pt x f, get Rnd_NE_pt (-x) (-f) by applying opp-inv at (-x,-f).
    have h := FloatSpec.Core.Round_pred.Rnd_NG_pt_opp_inv_spec (F := F) (P := P) (x := -x) (f := -f)
    simpa [FloatSpec.Core.Round_pred.Rnd_NG_pt_opp_inv_check, pure,
           decide_eq_true_iff, neg_neg]
      using h ⟨Fopp, Popp, by simpa⟩
  · intro hNEneg
    -- From Rnd_NE_pt (-x) (-f), get Rnd_NE_pt x f directly by opp-inv.
    have h := FloatSpec.Core.Round_pred.Rnd_NG_pt_opp_inv_spec (F := F) (P := P) (x := x) (f := f)
    simpa [FloatSpec.Core.Round_pred.Rnd_NG_pt_opp_inv_check, pure,
           decide_eq_true_iff]
      using h ⟨Fopp, Popp, hNEneg⟩

/-- Check absolute rounding (forward) -/
noncomputable def round_NE_abs_check : Bool :=
  by
    classical
    -- Decide absolute-value stability in the forward direction:
    -- if `Rnd_NE_pt x f` then `Rnd_NE_pt |x| |f|`.
    exact
      @decide
        (∀ x f : ℝ,
          Rnd_NE_pt beta fexp x f → Rnd_NE_pt beta fexp (abs x) (abs f))
        (Classical.dec _)


/-- Coq:
    Lemma round_NE_abs:
      forall x : R,
      round beta fexp ZnearestE (Rabs x) =
      Rabs (round beta fexp ZnearestE x).

    Equality between rounding abs(x) and abs(round(x)).
-/
theorem round_NE_abs (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    (pure (round_NE_abs_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hβ
  unfold round_NE_abs_check
  classical
  -- Reduce Hoare triple to the propositional goal.
  simp [ pure, decide_eq_true_iff]
  -- Prove: ∀ x f, Rnd_NE_pt x f → Rnd_NE_pt |x| |f|
  intro x f hNE
  -- Shorthands
  let F : ℝ → Prop := fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y
  let P : ℝ → ℝ → Prop := NE_prop beta fexp
  -- 0 is representable and the format is closed under negation.
  have hF0 : F 0 := by
    have h := FloatSpec.Core.Generic_fmt.generic_format_0 (beta := beta) (fexp := fexp)
    simpa using (h hβ)
  have Fopp : ∀ y, F y → F (-y) := by
    intro y hy
    simpa using (FloatSpec.Core.Generic_fmt.generic_format_opp (beta := beta) (fexp := fexp) (x := y) hy)
  -- Nearest component transports to absolute values by the generic spec.
  have hNabs : FloatSpec.Core.Defs.Rnd_N_pt F |x| |f| := by
    have h := FloatSpec.Core.Round_pred.Rnd_N_pt_abs_spec (F := F) (x := x) (f := f)
    simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_abs_check, pure,
           decide_eq_true_iff]
      using h ⟨hF0, Fopp, hNE.1⟩
  -- Build the tie-breaking/uniqueness component at absolute values.
  -- We analyze the NG tie component on (x,f).
  have hTieAbs : P |x| |f| ∨ ∀ f2 : ℝ, FloatSpec.Core.Defs.Rnd_N_pt F |x| f2 → f2 = |f| := by
    cases hNE.2 with
    | inl hPx =>
        -- Case 1: we have a concrete NE witness at (x,f); transfer it to (|x|,|f|).
        rcases hPx with ⟨g, hf, hcanon, heven⟩
        by_cases hf_nonneg : 0 ≤ f
        · -- Nonnegative f: reuse the same float witness.
          let gabs : FlocqFloat beta := g
          have hf_abs : |f| = (F2R gabs) := by
            have : |f| = f := abs_of_nonneg hf_nonneg
            simpa [gabs, this, hf]
          exact Or.inl ⟨gabs, by simpa [gabs] using hf_abs, hcanon, by simpa [gabs] using heven⟩
        · -- Negative f: use the opposite float and `F2R_Zopp`.
          have hfneg : f < 0 := lt_of_not_ge hf_nonneg
          let gabs : FlocqFloat beta := ⟨-g.Fnum, g.Fexp⟩
          have hF2Rneg : -(F2R g) = (F2R gabs) := by
            simpa [gabs] using (FloatSpec.Core.Float_prop.F2R_Zopp (beta := beta) (f := g) (hbeta := hβ))
          have hf_abs : |f| = (F2R gabs) := by
            -- Since f < 0, |f| = -f, and by F2R_Zopp we have -f = F2R gabs.
            have h1 : |f| = -f := by simpa [abs_of_neg hfneg]
            have h2 : -f = (F2R gabs) := by simpa [hf] using hF2Rneg
            simpa [h1] using h2
          -- Canonicality preserved under mantissa negation; parity invariant mod 2.
          have hcanon_abs : canonical beta fexp gabs :=
            FloatSpec.Core.Generic_fmt.canonical_opp (beta := beta) (fexp := fexp)
              (m := g.Fnum) (e := g.Fexp) hcanon
          have neg_mod_two (n : Int) : (-n) % 2 = n % 2 := by
            rcases Int.emod_two_eq_zero_or_one n with hn0 | hn1
            · have : (-n) % 2 = 0 := by
                rcases Int.emod_two_eq_zero_or_one (-n) with hneg0 | hneg1
                · exact hneg0
                · exact False.elim (by
                    have : (1 : Int) ≠ 0 := by decide
                    exact this (by simpa [hn0] using hneg1))
              simpa [hn0, this]
            · have : (-n) % 2 = 1 := by
                rcases Int.emod_two_eq_zero_or_one (-n) with hneg0 | hneg1
                · exact False.elim (by
                    have : (0 : Int) ≠ 1 := by decide
                    exact this (by simpa [hn1] using hneg0))
                · exact hneg1
              simpa [hn1, this]
          have heav_abs : gabs.Fnum % 2 = 0 := by simpa [gabs, neg_mod_two] using heven
          exact Or.inl ⟨gabs, by simpa [gabs] using hf_abs, hcanon_abs, by simpa [gabs] using heav_abs⟩
    | inr huniq_x =>
        -- Case 2: uniqueness branch at (x,f). Transfer uniqueness to (|x|,|f|).
        by_cases hx : 0 ≤ x
        · -- Nonnegative x: then `|x| = x`; also f is nonnegative by ge_0 spec.
          have hf_nonneg : 0 ≤ f := by
            have h := FloatSpec.Core.Round_pred.Rnd_N_pt_ge_0_spec (F := F) (x := x) (f := f)
            simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_ge_0_check, pure,
                   decide_eq_true_iff, hx] using h ⟨hF0, hx, hNE.1⟩
          -- Uniqueness at |x| using uniqueness at x.
          have : ∀ f2 : ℝ, FloatSpec.Core.Defs.Rnd_N_pt F |x| f2 → f2 = |f| := by
            intro f2 hNf2
            have hxabs : |x| = x := by simpa [abs_of_nonneg hx]
            have : FloatSpec.Core.Defs.Rnd_N_pt F x f2 := by simpa [hxabs] using hNf2
            have hf2_eq_f : f2 = f := huniq_x f2 this
            simpa [abs_of_nonneg hf_nonneg] using hf2_eq_f
          exact Or.inr this
        · -- Nonpositive x: reduce to the nonnegative case on (-x,-f), then rewrite abs.
          have hxle0 : x ≤ 0 := le_of_not_ge hx
          -- Nearest at (-x,-f) via opposite invariance on nearest.
          have hNneg : FloatSpec.Core.Defs.Rnd_N_pt F (-x) (-f) := by
            have h := FloatSpec.Core.Round_pred.Rnd_N_pt_opp_inv_spec (F := F) (x := -x) (f := -f)
            simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_opp_inv_check, pure,
                   decide_eq_true_iff, neg_neg]
              using h Fopp (by simpa [neg_neg] using hNE.1) trivial
          -- Apply the nonnegative-x argument at (-x,-f) and rewrite abs.
          have hxnonneg' : 0 ≤ -x := by simpa using neg_nonneg.mpr hxle0
          have hf_nonneg' : 0 ≤ -f := by
            have h := FloatSpec.Core.Round_pred.Rnd_N_pt_ge_0_spec (F := F) (x := -x) (f := -f)
            simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_ge_0_check, pure,
                   decide_eq_true_iff, hxnonneg'] using h ⟨hF0, hxnonneg', hNneg⟩
          -- Transfer uniqueness from x to -x using opp_inv, then rewrite absolutes.
          have : ∀ f2 : ℝ, FloatSpec.Core.Defs.Rnd_N_pt F |x| f2 → f2 = |f| := by
            intro f2 hNf2_abs
            -- Here |x| = -x, and |f| = -f by nonpositivity of f.
            have hxabs : |x| = -x := by simpa [abs_of_nonpos hxle0]
            have hfabs : |f| = -f := by
              have hf_le0 : f ≤ 0 := by simpa using (neg_nonneg.mp hf_nonneg')
              simpa [abs_of_nonpos hf_le0]
            -- Convert nearest at |x| to nearest at -x and use uniqueness at -x.
            have hNf2_neg : FloatSpec.Core.Defs.Rnd_N_pt F (-x) f2 := by simpa [hxabs] using hNf2_abs
            -- Uniqueness at -x from uniqueness at x by mapping with opp-inv.
            have huniq_neg : ∀ g, FloatSpec.Core.Defs.Rnd_N_pt F (-x) g → g = -f := by
              intro g hNg
              -- Map to x using opp-inv and apply uniqueness at x.
              have hN_at_x : FloatSpec.Core.Defs.Rnd_N_pt F x (-g) := by
                have h := FloatSpec.Core.Round_pred.Rnd_N_pt_opp_inv_spec (F := F) (x := x) (f := -g)
                simpa [FloatSpec.Core.Round_pred.Rnd_N_pt_opp_inv_check, pure,
                       decide_eq_true_iff]
                  using h Fopp (by simp; exact hNg) trivial
              have := huniq_x (-g) hN_at_x
              -- From -g = f, deduce g = -f.
              have : g = -f := by
                have := congrArg Neg.neg this
                simpa using this
              exact this
            have hf2_eq_negf : f2 = -f := huniq_neg f2 hNf2_neg
            simpa [hfabs] using hf2_eq_negf
          exact Or.inr this
  -- Conclude the NG predicate at absolute values.
  exact And.intro hNabs hTieAbs

private lemma ZnearestE_choice_transform (t : Int) :
    decide (2 ∣ (-(t + 1) : Int)) = !(decide (2 ∣ t)) := by
  have hsame : (-(t + 1) : Int) = -1 + -t := by ring
  rw [hsame]
  by_cases ht : 2 ∣ t
  · have hnot : ¬ 2 ∣ (-1 + -t : Int) := by
      intro h
      have hsum : 2 ∣ t + (-1 + -t) := dvd_add ht h
      have hminus : t + (-1 + -t) = -1 := by ring
      have hneg1 : 2 ∣ (-1 : Int) := by simpa [hminus] using hsum
      norm_num at hneg1
    simp [ht, hnot]
  · have htmod : t % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one t with h0 | h1
      · exact False.elim (ht (Int.dvd_of_emod_eq_zero h0))
      · exact h1
    have hdiv : 2 ∣ (-1 + -t : Int) := by
      have ht1 : (t + 1) % 2 = 0 := by
        have hadd : (t + 1) % 2 = ((t % 2) + (1 % 2)) % 2 := by
          simpa using (Int.add_emod t 1 2)
        norm_num [hadd, htmod]
      have hneg : 2 ∣ -(t + 1) := dvd_neg.mpr (Int.dvd_of_emod_eq_zero ht1)
      have heq : -(t + 1) = (-1 + -t : Int) := by ring
      simpa [heq] using hneg
    simp [ht, hdiv]

private lemma ZnearestE_opp (x : ℝ) :
    FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t))) (-x) =
      -FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t))) x := by
  classical
  let choice : Int → Bool := fun t => !(decide (2 ∣ t))
  have h := FloatSpec.Core.Generic_fmt.Znearest_opp choice x
  have hchoice :
      (fun t : Int => ! choice (-(t + 1))) = choice := by
    funext t
    simpa [choice] using ZnearestE_choice_transform t
  rw [hchoice] at h
  simpa [choice] using h

private lemma roundR_ZnearestE_opp
    (hβ : 1 < beta) (x : ℝ) :
    FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) (-x) =
      -FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) x := by
  classical
  let choice : Int → Bool := fun t => !(decide (2 ∣ t))
  have hself :
      FloatSpec.Core.Generic_fmt.Zrnd_opp
          (FloatSpec.Core.Generic_fmt.Znearest choice) =
        FloatSpec.Core.Generic_fmt.Znearest choice := by
    funext y
    unfold FloatSpec.Core.Generic_fmt.Zrnd_opp
    have h := ZnearestE_opp y
    simpa [choice] using congrArg Neg.neg h
  have h := FloatSpec.Core.Generic_fmt.roundR_opp
    (beta := beta) (fexp := fexp)
    (rnd := FloatSpec.Core.Generic_fmt.Znearest choice) (x := x) hβ
  simpa [choice, hself] using h

/-- Check predicate holds at the concrete nearest-even rounded value. -/
noncomputable def round_NE_pt_check (x : ℝ) : Bool :=
  by
    classical
    exact
      @decide
        (Rnd_NE_pt beta fexp x
          (FloatSpec.Core.Generic_fmt.roundR beta fexp
            (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) x))
        (Classical.dec _)

theorem round_NE_pt (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    (pure (round_NE_pt_check beta fexp x) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hβ
  unfold round_NE_pt_check
  classical
  simp [pure, decide_eq_true_iff]
  by_cases hxpos : 0 < x
  · exact round_NE_pt_pos_exact (beta := beta) (fexp := fexp) hβ x hxpos
  · by_cases hx0 : x = 0
    · have hround0 :
          FloatSpec.Core.Generic_fmt.roundR beta fexp
            (FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))) x = 0 := by
        have hz :
            FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t))) 0 = 0 := by
          norm_num [FloatSpec.Core.Generic_fmt.Znearest, FloatSpec.Core.Raux.Rcompare,
            FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil]
        simp [hx0, FloatSpec.Core.Generic_fmt.roundR,
          FloatSpec.Core.Generic_fmt.scaled_mantissa, hz]
      have hfmt0 : FloatSpec.Core.Generic_fmt.generic_format beta fexp 0 := by
        have h := FloatSpec.Core.Generic_fmt.generic_format_0 (beta := beta) (fexp := fexp)
        simpa using h hβ
      have hrefl := Rnd_NE_pt_refl (beta := beta) (fexp := fexp) (x := 0)
      have hrefl_prop :
          ∀ y : ℝ, FloatSpec.Core.Generic_fmt.generic_format beta fexp y →
            Rnd_NE_pt beta fexp y y := by
        simpa [Rnd_NE_pt_refl_check, pure, decide_eq_true_iff] using
          hrefl ⟨hβ, hfmt0⟩
      have hNE0 : Rnd_NE_pt beta fexp 0 0 := by
        exact hrefl_prop 0 hfmt0
      rw [hround0, hx0]
      exact hNE0
    · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx0
      have hxneg_pos : 0 < -x := neg_pos.mpr hxneg
      let choice : Int → Bool := fun t => !(decide (2 ∣ t))
      have hNE_neg :
          Rnd_NE_pt beta fexp (-x)
            (FloatSpec.Core.Generic_fmt.roundR beta fexp
              (FloatSpec.Core.Generic_fmt.Znearest choice) (-x)) := by
        simpa [choice] using
          round_NE_pt_pos_exact (beta := beta) (fexp := fexp) hβ (-x) hxneg_pos
      have hopp_eq :
          FloatSpec.Core.Generic_fmt.roundR beta fexp
              (FloatSpec.Core.Generic_fmt.Znearest choice) (-x) =
            -FloatSpec.Core.Generic_fmt.roundR beta fexp
              (FloatSpec.Core.Generic_fmt.Znearest choice) x := by
        simpa [choice] using roundR_ZnearestE_opp (beta := beta) (fexp := fexp) hβ x
      have hopp_prop :
          ∀ y f : ℝ, Rnd_NE_pt beta fexp y f ↔ Rnd_NE_pt beta fexp (-y) (-f) := by
        have h := round_NE_opp (beta := beta) (fexp := fexp) (x := x)
        simpa [round_NE_opp_check, pure, decide_eq_true_iff] using h hβ
      have hright :
          Rnd_NE_pt beta fexp (-x)
            (-(FloatSpec.Core.Generic_fmt.roundR beta fexp
              (FloatSpec.Core.Generic_fmt.Znearest choice) x)) := by
        simpa [hopp_eq] using hNE_neg
      have hmain :
          Rnd_NE_pt beta fexp x
            (FloatSpec.Core.Generic_fmt.roundR beta fexp
              (FloatSpec.Core.Generic_fmt.Znearest choice) x) :=
        (hopp_prop x
          (FloatSpec.Core.Generic_fmt.roundR beta fexp
            (FloatSpec.Core.Generic_fmt.Znearest choice) x)).mpr hright
      simpa [choice] using hmain

end ParityProperties

section ErrorBounds

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
variable [FloatSpec.Core.Generic_fmt.Monotone_exp fexp]

/-- Check error bound property
-/
noncomputable def Rnd_NE_pt_error_bound_check : Bool :=
  by
    classical
    -- Decide the half‑ULP error bound for nearest-even rounding.
    exact
      @decide
        (∀ x f : ℝ,
          Rnd_NE_pt beta fexp x f →
          |f - x| ≤ (1/2) * (FloatSpec.Core.Ulp.ulp beta fexp x))
        (Classical.dec _)

/-- Check minimal error property
-/
noncomputable def Rnd_NE_pt_minimal_error_check : Bool :=
  by
    classical
    -- Decide that nearest-even minimizes absolute error among representables.
    exact
      @decide
        (∀ x f g : ℝ,
          Rnd_NE_pt beta fexp x f →
          FloatSpec.Core.Generic_fmt.generic_format beta fexp g →
          |f - x| ≤ |g - x|)
        (Classical.dec _)

/-- Specification: Nearest-even minimizes absolute error

    Among all representable values, nearest-even rounding
    selects one that minimizes the absolute error.
-/
theorem Rnd_NE_pt_minimal_error (x f : ℝ) :
    ⦃⌜beta > 1 ∧ Rnd_NE_pt beta fexp x f⌝⦄
    (pure (Rnd_NE_pt_minimal_error_check beta fexp) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NE_pt_minimal_error_check
  classical
  -- Reduce the Hoare triple to the propositional goal.
  simp [ pure, decide_eq_true_iff]
  -- Prove the minimal-absolute-error property for arbitrary x, f, g.
  intro x f g hNE hFg
  -- Extract nearest property from NE and apply minimality.
  have hN : FloatSpec.Core.Defs.Rnd_N_pt
      (fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp y) x f := hNE.1
  simpa using (hN.2 g hFg)

end ErrorBounds

end FloatSpec.Core.RoundNE
