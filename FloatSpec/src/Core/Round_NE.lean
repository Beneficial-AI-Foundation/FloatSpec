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
import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Round_pred
import FloatSpec.src.Core.Generic_fmt
import FloatSpec.src.Core.Round_generic
import FloatSpec.src.Core.Float_prop
import FloatSpec.src.Core.Ulp
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Std.Do
open FloatSpec.Core.Defs
open FloatSpec.Core.Round_pred
open FloatSpec.Core.Generic_fmt
open FloatSpec.Core.Round_generic

namespace FloatSpec.Core.RoundNE

section NearestEvenRounding

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

/-- Nearest-even rounding property

    Coq:
    Definition NE_prop (_ : R) f :=
      exists g : float beta, f = F2R g /\\ canonical g /\\ Z.even (Fnum g) = true.

    A tie-breaking rule that selects the value whose mantissa
    is even when two representable values are equidistant.
-/
def NE_prop (beta : Int) (fexp : Int → Int) (x : ℝ) (f : ℝ) : Prop :=
  ∃ g : FlocqFloat beta, f = (F2R g).run ∧ canonical beta fexp g ∧ g.Fnum % 2 = 0

/-- Nearest-even rounding predicate

    Coq:
    Definition Rnd_NE_pt :=
      Rnd_NG_pt format NE_prop.

    Combines nearest rounding with the even tie-breaking rule.
    This is the IEEE 754 default rounding mode.
-/
def Rnd_NE_pt : ℝ → ℝ → Prop :=
  FloatSpec.Core.Round_pred.Rnd_NG_pt (fun x => (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run) (NE_prop beta fexp)

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
  ¬(FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run →
  FloatSpec.Core.Round_pred.Rnd_DN_pt (fun y => (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run) x xd →
  FloatSpec.Core.Round_pred.Rnd_UP_pt (fun y => (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run) x xu →
  ∃ gd gu : FlocqFloat beta,
    xd = (F2R gd).run ∧ xu = (F2R gu).run ∧
    canonical beta fexp gd ∧ canonical beta fexp gu ∧
    gd.Fnum % 2 ≠ gu.Fnum % 2

end NearestEvenRounding

section ParityAuxiliary

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

/-- Parity property without sign restriction

    Like `DN_UP_parity_pos_prop` but without `0 < x`.

    Coq:
    Definition DN_UP_parity_prop :=
      forall x xd xu,
      ~ format x ->
      canonical xd ->
      canonical xu ->
      F2R xd = round beta fexp Zfloor x ->
      F2R xu = round beta fexp Zceil x ->
      Z.even (Fnum xu) = negb (Z.even (Fnum xd)).
-/
def DN_UP_parity_prop : Prop :=
  ∀ x xd xu,
  ¬(FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run →
  FloatSpec.Core.Round_pred.Rnd_DN_pt (fun y => (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run) x xd →
  FloatSpec.Core.Round_pred.Rnd_UP_pt (fun y => (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run) x xu →
  ∃ gd gu : FlocqFloat beta,
    xd = (F2R gd).run ∧ xu = (F2R gu).run ∧
    canonical beta fexp gd ∧ canonical beta fexp gu ∧
    gd.Fnum % 2 ≠ gu.Fnum % 2

/-- Check DN/UP parity auxiliary lemma -/
noncomputable def DN_UP_parity_aux_check : Id Bool :=
  by
    classical
    -- Decide the general parity property; the spec lemma will prove it.
    exact pure (decide (DN_UP_parity_prop beta fexp))

/-- Coq:
    Lemma DN_UP_parity_aux :
      DN_UP_parity_pos_prop ->
      DN_UP_parity_prop.

    Auxiliary lemma: parity for positives implies general parity via symmetry.
-/
theorem DN_UP_parity_aux :
    ⦃⌜beta > 1 ∧ DN_UP_parity_pos_prop beta fexp⌝⦄
    DN_UP_parity_aux_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold DN_UP_parity_aux_check
  classical
  -- Reduce the Hoare triple on `Id` to a propositional goal about `decide`.
  -- It suffices to prove `DN_UP_parity_prop beta fexp`.
  simp [wp, PostCond.noThrow, Id.run, pure, decide_eq_true_iff]
  -- Unpack the precondition: base > 1 and the positive-case parity property.
  intro x xd xu hnotFmt hDN hUP
  -- We'll reason by cases on the sign of x.
  have htrich := lt_trichotomy (0 : ℝ) x
  -- Helper: format predicate for this file.
  let F := fun y : ℝ => (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run
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
    simpa using (And.right ‹beta > 1 ∧ DN_UP_parity_pos_prop beta fexp› x xd xu hpos hnotFmt hDN hUP)
  · -- x = 0: this contradicts `¬ format x`, as 0 is always representable.
    -- Hence the goal holds vacuously.
    exfalso
    have h0F : F 0 := by
      -- generic_format_0 ensures 0 is in format when beta > 1
      have hβ := (And.left ‹beta > 1 ∧ DN_UP_parity_pos_prop beta fexp›)
      -- Extract the boolean result of the Hoare-triple style theorem
      have h := FloatSpec.Core.Generic_fmt.generic_format_0 (beta := beta) (fexp := fexp) (hβ)
      -- The theorem above states `generic_format beta fexp 0`.
      simpa using h
    -- Rewrite x = 0 into the hypothesis and contradict.
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
    rcases (And.right ‹beta > 1 ∧ DN_UP_parity_pos_prop beta fexp›)
      (-x) (-xu) (-xd) hpos' hnotFmtNeg hDN_at_negx hUP_at_negx with
      ⟨gd_pos, gu_pos, hxueq, hxdeq, hcanon_d, hcanon_u, hpar_pos⟩
    -- Transport back to x by negating the canonical floats.
    -- Define the floats for x so that their real values equal xd and xu respectively.
    refine ?_ 
    -- Candidate floats for x
    let gd : FlocqFloat beta := ⟨-gu_pos.Fnum, gu_pos.Fexp⟩
    let gu : FlocqFloat beta := ⟨-gd_pos.Fnum, gd_pos.Fexp⟩
    -- Show xd = F2R gd and xu = F2R gu using F2R_Zopp.
    have hxd : xd = (F2R gd).run := by
      -- From hxdeq: (-xd) = (F2R gu_pos).run
      -- So xd = -(F2R gu_pos).run = F2R (negate mantissa of gu_pos)
      have hx' : -(F2R gu_pos).run = (F2R gd).run := by
        -- F2R_Zopp: -(F2R f).run = F2R (mk (-f.Fnum) f.Fexp)
        have := FloatSpec.Core.Float_prop.F2R_Zopp (beta := beta) (f := gu_pos)
          (hbeta := And.left ‹beta > 1 ∧ DN_UP_parity_pos_prop beta fexp›)
        simpa using this
      -- Rearranging the equation from hxdeq
      -- hxdeq : (-xd) = (F2R gu_pos).run
      have : xd = -(F2R gu_pos).run := by simpa using congrArg Neg.neg hxdeq
      simpa [hx'] using this
    have hxu : xu = (F2R gu).run := by
      -- From hxueq: (-xu) = (F2R gd_pos).run
      have hx' : -(F2R gd_pos).run = (F2R gu).run := by
        have := FloatSpec.Core.Float_prop.F2R_Zopp (beta := beta) (f := gd_pos)
          (hbeta := And.left ‹beta > 1 ∧ DN_UP_parity_pos_prop beta fexp›)
        simpa using this
      have : xu = -(F2R gd_pos).run := by simpa using congrArg Neg.neg hxueq
      simpa [hx'] using this
    -- Canonicality is preserved under mantissa negation.
    have hcanon_gd : canonical beta fexp gd := by
      -- Use `canonical_opp` from Generic_fmt
      exact FloatSpec.Core.Generic_fmt.canonical_opp (beta := beta) (fexp := fexp) (m := gu_pos.Fnum) (e := gu_pos.Fexp) hcanon_u
    have hcanon_gu : canonical beta fexp gu := by
      exact FloatSpec.Core.Generic_fmt.canonical_opp (beta := beta) (fexp := fexp) (m := gd_pos.Fnum) (e := gd_pos.Fexp) hcanon_d
    -- Now convert the parity inequality through negation using the lemma.
    have hparity' : gd.Fnum % 2 ≠ gu.Fnum % 2 := by
      -- gd.Fnum = -gu_pos.Fnum, gu.Fnum = -gd_pos.Fnum
      change (-gu_pos.Fnum) % 2 ≠ (-gd_pos.Fnum) % 2
      -- Rewrite both sides using `Int.neg_emod_two` and symmetry of `≠`.
      simpa [Int.neg_emod_two, ne_comm] using hpar_pos
    -- Assemble the final witnesses.
    refine ⟨gd, gu, hxd, hxu, hcanon_gd, hcanon_gu, hparity'⟩

/-- Check DN/UP parity holds for the generic format (positive case) -/
noncomputable def DN_UP_parity_generic_pos_check : Id Bool :=
  by
    classical
    -- Decide the positive-case parity property for DN/UP neighbors.
    exact pure (decide (DN_UP_parity_pos_prop beta fexp))

/-- Coq:
    Theorem DN_UP_parity_generic_pos :
      DN_UP_parity_pos_prop.

    Parity of down/up rounded neighbors differs when x > 0 and not representable.
-/
theorem DN_UP_parity_generic_pos :
    ⦃⌜beta > 1⌝⦄
    DN_UP_parity_generic_pos_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold DN_UP_parity_generic_pos_check
  sorry

/-- Check DN/UP parity holds for the generic format (all reals) -/
noncomputable def DN_UP_parity_generic_check : Id Bool :=
  by
    classical
    -- Decide the general (sign-agnostic) parity property for DN/UP neighbors.
    exact pure (decide (DN_UP_parity_prop beta fexp))

/-- Coq:
    Theorem DN_UP_parity_generic :
      DN_UP_parity_prop.

    General parity property derived from the positive case.
-/
theorem DN_UP_parity_generic :
    ⦃⌜beta > 1⌝⦄
    DN_UP_parity_generic_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold DN_UP_parity_generic_check
  sorry

end ParityAuxiliary

section UniquenessProperties

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

/-- Check nearest-even uniqueness property
-/
noncomputable def Rnd_NE_pt_unique_check : Id Bool :=
  by
    classical
    -- Decide the global uniqueness property for nearest-even rounding.
    exact
      pure
        (decide
          (∀ x f1 f2 : ℝ,
            Rnd_NE_pt beta fexp x f1 → Rnd_NE_pt beta fexp x f2 → f1 = f2))

/-- Specification: Nearest-even uniqueness property

    The nearest-even rounding satisfies the uniqueness property
    required by the generic nearest rounding framework.
-/
theorem Rnd_NE_pt_unique_prop :
    ⦃⌜beta > 1⌝⦄
    Rnd_NE_pt_unique_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NE_pt_unique_check
  sorry

/-- Check nearest-even rounding uniqueness for specific values
-/
noncomputable def Rnd_NE_pt_unique_specific_check : Id Bool :=
  by
    classical
    -- Decide the uniqueness of the rounded value at any given input.
    -- (Specialized equality goal proved in the accompanying theorem.)
    exact
      pure
        (decide
          (∀ x f1 f2 : ℝ,
            Rnd_NE_pt beta fexp x f1 → Rnd_NE_pt beta fexp x f2 → f1 = f2))

/-- Specification: Nearest-even rounding is unique

    For any real number, there is at most one value that
    satisfies the nearest-even rounding predicate.
-/
theorem Rnd_NE_pt_unique (x f1 f2 : ℝ) :
    ⦃⌜beta > 1 ∧ Rnd_NE_pt beta fexp x f1 ∧ Rnd_NE_pt beta fexp x f2⌝⦄
    Rnd_NE_pt_unique_specific_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NE_pt_unique_specific_check
  sorry

/-- Check nearest-even monotonicity
-/
noncomputable def Rnd_NE_pt_monotone_check : Id Bool :=
  by
    classical
    -- Decide monotonicity of the nearest-even rounding predicate.
    exact pure (decide (round_pred_monotone (Rnd_NE_pt beta fexp)))



/-- Coq:
    Theorem Rnd_NE_pt_monotone :
      round_pred_monotone Rnd_NE_pt.

    Specification: Nearest-even rounding is monotone

    The nearest-even rounding preserves the ordering of inputs.
-/
theorem Rnd_NE_pt_monotone :
    ⦃⌜beta > 1⌝⦄
    Rnd_NE_pt_monotone_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NE_pt_monotone_check
  sorry

/-- Check nearest-even totality -/
noncomputable def Rnd_NE_pt_total_check : Id Bool :=
  by
    classical
    -- Decide totality of the nearest-even rounding predicate.
    exact pure (decide (round_pred_total (Rnd_NE_pt beta fexp)))


/-- Coq:
    Theorem Rnd_NE_pt_total :
      round_pred_total Rnd_NE_pt.

    Nearest-even rounding predicate is total.
-/
theorem Rnd_NE_pt_total :
    ⦃⌜beta > 1⌝⦄
    Rnd_NE_pt_total_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NE_pt_total_check
  sorry

/-- Check nearest-even forms a rounding predicate -/
noncomputable def Rnd_NE_pt_round_check : Id Bool :=
  by
    classical
    -- Decide that nearest-even defines a proper rounding predicate.
    exact pure (decide (round_pred (Rnd_NE_pt beta fexp)))


/-- Coq:
    Theorem Rnd_NE_pt_round :
      round_pred Rnd_NE_pt.

    Nearest-even rounding predicate satisfies totality and monotonicity.
-/
theorem Rnd_NE_pt_round :
    ⦃⌜beta > 1⌝⦄
    Rnd_NE_pt_round_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NE_pt_round_check
  sorry

end UniquenessProperties

section RoundingPredicateProperties

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

/-- Check rounding predicate satisfaction
-/
noncomputable def satisfies_any_imp_NE_check : Id Bool :=
  by
    classical
    -- Decide that nearest-even forms a proper rounding predicate under the
    -- `satisfies_any` hypothesis on the format.
    exact pure (decide (round_pred (Rnd_NE_pt beta fexp)))

/-- Specification: Nearest-even satisfies rounding predicate

    When the format satisfies the "satisfies_any" property,
    nearest-even rounding forms a proper rounding predicate.
-/
theorem satisfies_any_imp_NE :
    ⦃⌜beta > 1 ∧ satisfies_any (fun x => (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)⌝⦄
    satisfies_any_imp_NE_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold satisfies_any_imp_NE_check
  sorry

/-- Check nearest-even reflexivity
-/
noncomputable def Rnd_NE_pt_refl_check : Id Bool :=
  by
    classical
    -- Representable values are fixed points of nearest-even rounding.
    exact
      pure
        (decide
          (∀ x : ℝ,
            (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run →
            Rnd_NE_pt beta fexp x x))


/-- Coq:
    Rnd_NG_pt_refl specialized to Rnd_NE_pt (implicit in Coq proof of round_NE_pt).

    Specification: Nearest-even rounding is reflexive on format

    If x is already in the format, then rounding x gives x itself.
-/
theorem Rnd_NE_pt_refl (x : ℝ) :
    ⦃⌜beta > 1 ∧ (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run⌝⦄
    Rnd_NE_pt_refl_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NE_pt_refl_check
  sorry

/-- Check nearest-even idempotence
-/
noncomputable def Rnd_NE_pt_idempotent_check : Id Bool :=
  by
    classical
    -- If x is representable and f rounds to x under NE, then f = x.
    exact
      pure
        (decide
          (∀ x f : ℝ,
            Rnd_NE_pt beta fexp x f →
            (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run →
            f = x))


/-- Coq:
    Rnd_NG_pt_idempotent specialized (implicit in Coq lemmas around Rnd predicates).

    Specification: Nearest-even rounding is idempotent

    If x is in the format and f is its rounding, then f = x.
-/
theorem Rnd_NE_pt_idempotent (x f : ℝ) :
    ⦃⌜beta > 1 ∧ Rnd_NE_pt beta fexp x f ∧ (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run⌝⦄
    Rnd_NE_pt_idempotent_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NE_pt_idempotent_check
  sorry

end RoundingPredicateProperties

section ParityProperties

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

/-- Check down-up parity property
-/
noncomputable def DN_UP_parity_pos_holds_check : Id Bool :=
  by
    classical
    -- Decide the positive-case parity property for DN/UP neighbors.
    exact pure (decide (DN_UP_parity_pos_prop beta fexp))

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
    DN_UP_parity_pos_holds_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold DN_UP_parity_pos_holds_check
  sorry

/-- Check sign preservation
-/
noncomputable def Rnd_NE_pt_sign_check : Id Bool :=
  by
    classical
    -- Decide sign preservation: if Rnd_NE_pt x f with x ≠ 0 and 0 < f, then 0 < x.
    exact
      pure
        (decide
          (∀ x f : ℝ,
            Rnd_NE_pt beta fexp x f → x ≠ 0 → 0 < f → 0 < x))

/-- Coq: Derived from round_NE_pt_pos and symmetry; sign preserved except zeros.

    Specification: Nearest-even preserves sign

    The sign of the result matches the sign of the input
    (except potentially for signed zeros).
-/
theorem Rnd_NE_pt_sign (x f : ℝ) :
    ⦃⌜beta > 1 ∧ Rnd_NE_pt beta fexp x f ∧ x ≠ 0 ∧ 0 < f⌝⦄
    Rnd_NE_pt_sign_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NE_pt_sign_check
  sorry

/-- Check absolute value property
-/
noncomputable def Rnd_NE_pt_abs_check : Id Bool :=
  by
    classical
    -- Decide absolute-value stability: rounding relates |x| to |f| as well.
    exact
      pure
        (decide
          (∀ x f : ℝ,
            Rnd_NE_pt beta fexp x f →
            Rnd_NE_pt beta fexp (abs x) (abs f)))


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
    Rnd_NE_pt_abs_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NE_pt_abs_check
  sorry

/-- Check rounding at positive inputs -/
noncomputable def round_NE_pt_pos_check : Id Bool :=
  by
    classical
    -- Decide existence of an NE-rounded value at positive inputs.
    exact pure (decide (∀ x : ℝ, 0 < x → ∃ f : ℝ, Rnd_NE_pt beta fexp x f))


/-- Coq:
    Lemma round_NE_pt_pos :
      forall x,
      (0 < x)%R ->
      Rnd_NE_pt x (round beta fexp ZnearestE x).

    Rounding to nearest-even at positive x satisfies the predicate.
-/
theorem round_NE_pt_pos (x : ℝ) :
    ⦃⌜beta > 1 ∧ 0 < x⌝⦄
    round_NE_pt_pos_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold round_NE_pt_pos_check
  sorry

/-- Check rounding negation -/
noncomputable def round_NE_opp_check : Id Bool :=
  by
    classical
    -- Decide negation-compatibility: rounding commutes with negation at the predicate level.
    exact
      pure
        (decide
          (∀ x f : ℝ, Rnd_NE_pt beta fexp x f ↔ Rnd_NE_pt beta fexp (-x) (-f)))


/-- Coq:
    Theorem round_NE_opp :
      forall x,
      round beta fexp ZnearestE (-x) =
      (- round beta fexp ZnearestE x)%R.

    Rounding commutes with negation under nearest-even.
-/
theorem round_NE_opp (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    round_NE_opp_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold round_NE_opp_check
  sorry

/-- Check absolute rounding equality -/
noncomputable def round_NE_abs_check : Id Bool :=
  by
    classical
    -- Decide absolute-value compatibility between input and output under NE rounding.
    exact
      pure
        (decide
          (∀ x f : ℝ,
            Rnd_NE_pt beta fexp x f ↔ Rnd_NE_pt beta fexp (abs x) (abs f)))


/-- Coq:
    Lemma round_NE_abs:
      forall x : R,
      round beta fexp ZnearestE (Rabs x) =
      Rabs (round beta fexp ZnearestE x).

    Equality between rounding abs(x) and abs(round(x)).
-/
theorem round_NE_abs (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    round_NE_abs_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold round_NE_abs_check
  sorry

/-- Check predicate holds at rounded value -/
noncomputable def round_NE_pt_check : Id Bool :=
  by
    classical
    -- Decide totality: every input admits an NE-rounded value.
    exact pure (decide (∀ x : ℝ, ∃ f : ℝ, Rnd_NE_pt beta fexp x f))


/-- Coq:
    Theorem round_NE_pt :
      forall x,
      Rnd_NE_pt x (round beta fexp ZnearestE x).

    The rounded value under nearest-even satisfies the rounding predicate.
-/
theorem round_NE_pt (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    round_NE_pt_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold round_NE_pt_check
  sorry

end ParityProperties

section ErrorBounds

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

/-- Check error bound property
-/
noncomputable def Rnd_NE_pt_error_bound_check : Id Bool :=
  by
    classical
    -- Decide the half‑ULP error bound for nearest-even rounding.
    exact
      pure
        (decide
          (∀ x f : ℝ,
            Rnd_NE_pt beta fexp x f →
            |f - x| ≤ (1/2) * ((FloatSpec.Core.Ulp.ulp beta fexp x).run)))

/-- Specification: Error bound for nearest-even rounding

    The error in nearest-even rounding is bounded by half a ULP.
-/
theorem Rnd_NE_pt_error_bound (x f : ℝ) :
    ⦃⌜beta > 1 ∧ Rnd_NE_pt beta fexp x f⌝⦄
    Rnd_NE_pt_error_bound_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NE_pt_error_bound_check
  sorry

/-- Check minimal error property
-/
noncomputable def Rnd_NE_pt_minimal_error_check : Id Bool :=
  by
    classical
    -- Decide that nearest-even minimizes absolute error among representables.
    exact
      pure
        (decide
          (∀ x f g : ℝ,
            Rnd_NE_pt beta fexp x f →
            (FloatSpec.Core.Generic_fmt.generic_format beta fexp g).run →
            |f - x| ≤ |g - x|))

/-- Specification: Nearest-even minimizes absolute error

    Among all representable values, nearest-even rounding
    selects one that minimizes the absolute error.
-/
theorem Rnd_NE_pt_minimal_error (x f : ℝ) :
    ⦃⌜beta > 1 ∧ Rnd_NE_pt beta fexp x f⌝⦄
    Rnd_NE_pt_minimal_error_check beta fexp
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NE_pt_minimal_error_check
  sorry

end ErrorBounds

end FloatSpec.Core.RoundNE
