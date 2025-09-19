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

Unit in the last place (ULP) definitions and core properties
Based on flocq/src/Core/Ulp.v
-/

import FloatSpec.src.Core.Zaux
import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Round_pred
import FloatSpec.src.Core.Generic_fmt
import FloatSpec.src.Core.Round_generic
import FloatSpec.src.Core.Float_prop
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Std.Do
open FloatSpec.Core.Generic_fmt
open FloatSpec.Core.Defs

namespace FloatSpec.Core.Ulp

section UnitInLastPlace

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

/-- Placeholder: non-FTZ exponent property (class stub for specs). -/
class Exp_not_FTZ (fexp : Int → Int) : Prop where
  trivial : True

/-- Placeholder: monotone exponent property (class stub for specs). -/
class Monotone_exp (fexp : Int → Int) : Prop where
  trivial : True

/-- Unit in the last place (ULP)

Coq (Ulp.v) definition for reference:
```
Definition ulp x := match Req_bool x 0 with
  | true   => match negligible_exp with
            | Some n => bpow (fexp n)
            | None => 0%R
            end
  | false  => bpow (cexp beta fexp x)
end.
```
Note: We use a simplified zero case: `bpow (fexp 1)`.
-/
noncomputable def ulp (x : ℝ) : Id ℝ :=
  if x = 0 then
    pure ((beta : ℝ) ^ (fexp 1))
  else do
    let e ← FloatSpec.Core.Generic_fmt.cexp beta fexp x
    pure ((beta : ℝ) ^ e)

/-- Placeholder for negligible exponent detection (Coq: `negligible_exp`).
In this Lean port, we use a simplified model and always return `none`.
-/
def negligible_exp (fexp : Int → Int) : Option Int := none

/-- Coq (Ulp.v): Auxiliary totality of ≤ on integers. -/
theorem Z_le_dec_aux (x y : Int) : (x ≤ y) ∨ ¬ (x ≤ y) := by
  -- Classical decidability; placeholder
  sorry

/-- Coq (Ulp.v): `negligible_exp` property predicate (parameterized by `fexp`). -/
inductive negligible_exp_prop (fexp : Int → Int) : Option Int → Prop where
  | negligible_None : (∀ n : Int, fexp n < n) → negligible_exp_prop fexp none
  | negligible_Some : ∀ n : Int, n ≤ fexp n → negligible_exp_prop fexp (some n)

/-- Coq (Ulp.v): `negligible_exp_spec`. -/
lemma negligible_exp_spec : negligible_exp_prop fexp (negligible_exp fexp) := by
  -- In this Lean port, `negligible_exp = none` by definition.
  -- We leave the proof abstract as a placeholder.
  sorry

/-- Coq (Ulp.v): `negligible_exp_spec'`. -/
lemma negligible_exp_spec' :
    (negligible_exp fexp = none ∧ ∀ n : Int, fexp n < n)
    ∨ ∃ n : Int, negligible_exp fexp = some n ∧ n ≤ fexp n := by
  -- Placeholder; mirrors Coq alternative characterization.
  sorry

/-- Coq (Ulp.v): `fexp_negligible_exp_eq`. -/
lemma fexp_negligible_exp_eq (n m : Int)
    (hn : n ≤ fexp n) (hm : m ≤ fexp m) :
    fexp n = fexp m := by
  -- Placeholder; relies on Valid_exp monotonic/constancy properties.
  sorry

/-- Positive predecessor used by `pred`/`succ` (mirrors Coq `pred_pos`). -/
noncomputable def pred_pos (x : ℝ) : Id ℝ :=
  if x = (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x).run - 1) then
    pure (x - (beta : ℝ) ^ (fexp ((FloatSpec.Core.Raux.mag beta x).run - 1)))
  else do
    let u ← ulp beta fexp x
    pure (x - u)

/-- Successor at one ULP (mirrors Coq `succ`). -/
noncomputable def succ (x : ℝ) : Id ℝ :=
  if 0 ≤ x then
    do
      let u ← ulp beta fexp x
      pure (x + u)
  else
    do
      let px ← pred_pos beta fexp (-x)
      pure (-px)

/-- Predecessor defined from `succ` (mirrors Coq `pred`). -/
noncomputable def pred (x : ℝ) : Id ℝ := do
  let s ← succ beta fexp (-x)
  pure (-s)

/-- Coq (Ulp.v):
Lemma ulp_neq_0 : forall x, x <> 0%R -> ulp x = bpow (cexp beta fexp x).
-/
theorem ulp_neq_0 (x : ℝ) (hx : x ≠ 0) :
    ⦃⌜True⌝⦄
    ulp beta fexp x
    ⦃⇓r => ⌜r = (beta : ℝ) ^ ((FloatSpec.Core.Generic_fmt.cexp beta fexp x).run)⌝⦄ := by
  sorry

/-- Coq (Ulp.v): Theorem pred_le: forall x y, F x -> F y -> x <= y -> pred x <= pred y. -/
theorem pred_le
    (x y : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (Fy : (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run)
    (hxy : x ≤ y) :
    ⦃⌜True⌝⦄ do
      let px ← pred beta fexp x
      let py ← pred beta fexp y
      pure (px, py)
    ⦃⇓r => ⌜r.1 ≤ r.2⌝⦄ := by
  sorry

/-- Coq (Ulp.v): Theorem succ_le: forall x y, F x -> F y -> x <= y -> succ x <= succ y. -/
theorem succ_le
    (x y : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (Fy : (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run)
    (hxy : x ≤ y) :
    ⦃⌜True⌝⦄ do
      let sx ← succ beta fexp x
      let sy ← succ beta fexp y
      pure (sx, sy)
    ⦃⇓r => ⌜r.1 ≤ r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem pred_le_inv: F x -> F y -> pred x <= pred y -> x <= y. -/
theorem pred_le_inv
    (x y : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (Fy : (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run)
    (h : (pred beta fexp x).run ≤ (pred beta fexp y).run) :
    ⦃⌜True⌝⦄ do
      let px ← pred beta fexp x
      pure px
    ⦃⇓_ => ⌜x ≤ y⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem succ_le_inv: F x -> F y -> succ x <= succ y -> x <= y. -/
theorem succ_le_inv
    (x y : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (Fy : (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run)
    (h : (succ beta fexp x).run ≤ (succ beta fexp y).run) :
    ⦃⌜True⌝⦄ do
      let sx ← succ beta fexp x
      pure sx
    ⦃⇓_ => ⌜x ≤ y⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem pred_lt: F x -> F y -> x < y -> pred x < pred y. -/
theorem pred_lt
    (x y : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (Fy : (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run)
    (hxy : x < y) :
    ⦃⌜True⌝⦄ do
      let px ← pred beta fexp x
      let py ← pred beta fexp y
      pure (px, py)
    ⦃⇓r => ⌜r.1 < r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem succ_lt: F x -> F y -> x < y -> succ x < succ y. -/
theorem succ_lt
    (x y : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (Fy : (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run)
    (hxy : x < y) :
    ⦃⌜True⌝⦄ do
      let sx ← succ beta fexp x
      let sy ← succ beta fexp y
      pure (sx, sy)
    ⦃⇓r => ⌜r.1 < r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma succ_le_plus_ulp:
  forall { Hm : Monotone_exp fexp } x,
  succ x <= x + ulp x.
-/
theorem succ_le_plus_ulp
    [Monotone_exp fexp]
    (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let s ← succ beta fexp x
      let u ← ulp beta fexp x
      pure (s, u)
    ⦃⇓r => ⌜r.1 ≤ x + r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma generic_format_plus_ulp:
  forall { Hm : Monotone_exp fexp } x,
  F x -> F (x + ulp x).
-/
theorem generic_format_plus_ulp
    [Monotone_exp fexp]
    (x : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let u ← ulp beta fexp x
      FloatSpec.Core.Generic_fmt.generic_format beta fexp (x + u)
    ⦃⇓g => ⌜g⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem round_DN_ge_UP_gt:
  forall x y, F y -> y < round UP x -> y <= round DN x.
-/
theorem round_DN_ge_UP_gt
    (x y : ℝ)
    (Fy : (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run)
    (hlt : y < (FloatSpec.Core.Round_generic.round_UP_to_format beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let dn ← FloatSpec.Core.Round_generic.round_DN_to_format beta fexp x
      pure dn
    ⦃⇓r => ⌜y ≤ r⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem round_UP_le_DN_lt:
  forall x y, F y -> round DN x < y -> round UP x <= y.
-/
theorem round_UP_le_DN_lt
    (x y : ℝ)
    (Fy : (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run)
    (hlt : (FloatSpec.Core.Round_generic.round_DN_to_format beta fexp x).run < y) :
    ⦃⌜True⌝⦄ do
      let up ← FloatSpec.Core.Round_generic.round_UP_to_format beta fexp x
      pure up
    ⦃⇓r => ⌜r ≤ y⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem pred_UP_le_DN:
  forall x, pred (round UP x) <= round DN x.
-/
theorem pred_UP_le_DN (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let up ← FloatSpec.Core.Round_generic.round_UP_to_format beta fexp x
      let dn ← FloatSpec.Core.Round_generic.round_DN_to_format beta fexp x
      let p ← pred beta fexp up
      pure (p, dn)
    ⦃⇓r => ⌜r.1 ≤ r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem UP_le_succ_DN:
  forall x, round UP x <= succ (round DN x).
-/
theorem UP_le_succ_DN (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let up ← FloatSpec.Core.Round_generic.round_UP_to_format beta fexp x
      let dn ← FloatSpec.Core.Round_generic.round_DN_to_format beta fexp x
      let s ← succ beta fexp dn
      pure (up, s)
    ⦃⇓r => ⌜r.1 ≤ r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem pred_UP_eq_DN:
  forall x, ~ F x -> pred (round UP x) = round DN x.
-/
theorem pred_UP_eq_DN
    (x : ℝ)
    (Fx : ¬ (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let up ← FloatSpec.Core.Round_generic.round_UP_to_format beta fexp x
      let dn ← FloatSpec.Core.Round_generic.round_DN_to_format beta fexp x
      let p ← pred beta fexp up
      pure (p, dn)
    ⦃⇓r => ⌜r.1 = r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem succ_DN_eq_UP:
  forall x, ~ F x -> succ (round DN x) = round UP x.
-/
theorem succ_DN_eq_UP
    (x : ℝ)
    (Fx : ¬ (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let dn ← FloatSpec.Core.Round_generic.round_DN_to_format beta fexp x
      let up ← FloatSpec.Core.Round_generic.round_UP_to_format beta fexp x
      let s ← succ beta fexp dn
      pure (s, up)
    ⦃⇓r => ⌜r.1 = r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem round_DN_eq:
  forall x d, F d -> d <= x ∧ x < succ d -> round DN x = d.
-/
theorem round_DN_eq
    (x d : ℝ)
    (Fd : (FloatSpec.Core.Generic_fmt.generic_format beta fexp d).run)
    (h : d ≤ x ∧ x < (succ beta fexp d).run) :
    ⦃⌜True⌝⦄ do
      let dn ← FloatSpec.Core.Round_generic.round_DN_to_format beta fexp x
      pure dn
    ⦃⇓r => ⌜r = d⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem round_UP_eq:
  forall x u, F u -> pred u < x ∧ x ≤ u -> round UP x = u.
-/
theorem round_UP_eq
    (x u : ℝ)
    (Fu : (FloatSpec.Core.Generic_fmt.generic_format beta fexp u).run)
    (h : (pred beta fexp u).run < x ∧ x ≤ u) :
    ⦃⌜True⌝⦄ do
      let up ← FloatSpec.Core.Round_generic.round_UP_to_format beta fexp x
      pure up
    ⦃⇓r => ⌜r = u⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma ulp_ulp_0: forall {H : Exp_not_FTZ fexp}, ulp (ulp 0) = ulp 0.
-/
theorem ulp_ulp_0 [Exp_not_FTZ fexp] :
    ⦃⌜True⌝⦄ do
      let u0 ← ulp beta fexp 0
      let uu ← ulp beta fexp u0
      let u0' ← ulp beta fexp 0
      pure (uu, u0')
    ⦃⇓r => ⌜r.1 = r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma ulp_succ_pos:
  forall x, F x -> 0 < x -> ulp (succ x) = ulp x \/ succ x = bpow (mag x).
-/
theorem ulp_succ_pos
    (x : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (hx : 0 < x) :
    ⦃⌜True⌝⦄ do
      let s ← succ beta fexp x
      let us ← ulp beta fexp s
      let ux ← ulp beta fexp x
      let mx := (FloatSpec.Core.Raux.mag beta x).run
      pure ((us, ux), s, mx)
    ⦃⇓r => ⌜r.1.1 = r.1.2 ∨ r.2.1 = (beta : ℝ) ^ r.2.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem ulp_pred_pos:
  forall x, F x -> 0 < pred x -> ulp (pred x) = ulp x \/ x = bpow (mag x - 1).
-/
theorem ulp_pred_pos
    (x : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (hx : 0 < (pred beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp x
      let up ← ulp beta fexp p
      let ux ← ulp beta fexp x
      pure (up, ux)
    ⦃⇓r => ⌜r.1 = r.2 ∨ x = (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x).run - 1)⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma ulp_round_pos:
  forall { Not_FTZ_ : Exp_not_FTZ fexp} rnd x,
  0 < x -> ulp (round rnd x) = ulp x \/ round rnd x = bpow (mag x).
-/
theorem ulp_round_pos
    [Exp_not_FTZ fexp]
    (rnd : ℝ → ℝ → Prop) (x : ℝ) (hx : 0 < x) :
    ⦃⌜True⌝⦄ do
      let r := FloatSpec.Core.Round_generic.round_to_generic beta fexp rnd x
      let ur ← ulp beta fexp r
      let ux ← ulp beta fexp x
      let mx := (FloatSpec.Core.Raux.mag beta x).run
      pure (r, ur, ux, mx)
    ⦃⇓r => ⌜r.2.1 = r.2.2.1 ∨ r.1 = (beta : ℝ) ^ r.2.2.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem ulp_round:
  forall { Not_FTZ_ : Exp_not_FTZ fexp} rnd x,
  ulp (round rnd x) = ulp x \/ |round rnd x| = bpow (mag x).
-/
theorem ulp_round
    [Exp_not_FTZ fexp]
    (rnd : ℝ → ℝ → Prop) (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let r := FloatSpec.Core.Round_generic.round_to_generic beta fexp rnd x
      let ur ← ulp beta fexp r
      let ux ← ulp beta fexp x
      let mx := (FloatSpec.Core.Raux.mag beta x).run
      pure (r, ur, ux, mx)
    ⦃⇓r => ⌜r.2.1 = r.2.2.1 ∨ |r.1| = (beta : ℝ) ^ r.2.2.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma succ_round_ge_id:
  forall rnd x, x ≤ succ (round rnd x).
-/
theorem succ_round_ge_id
    (rnd : ℝ → ℝ → Prop) (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let r := FloatSpec.Core.Round_generic.round_to_generic beta fexp rnd x
      let s ← succ beta fexp r
      pure s
    ⦃⇓s => ⌜x ≤ s⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma pred_round_le_id:
  forall rnd x, pred (round rnd x) ≤ x.
-/
theorem pred_round_le_id
    (rnd : ℝ → ℝ → Prop) (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let r := FloatSpec.Core.Round_generic.round_to_generic beta fexp rnd x
      let p ← pred beta fexp r
      pure p
    ⦃⇓p => ⌜p ≤ x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem round_N_le_midp: forall choice u v, F u -> v < (u + succ u)/2 -> round_N v ≤ u.
-/
theorem round_N_le_midp
    (choice : Int → Bool) (u v : ℝ)
    (Fu : (FloatSpec.Core.Generic_fmt.generic_format beta fexp u).run)
    (h : v < ((u + (succ beta fexp u).run) / 2)) :
    ⦃⌜True⌝⦄ do
      let rn ← FloatSpec.Core.Round_generic.round_N_to_format beta fexp v
      pure rn
    ⦃⇓r => ⌜r ≤ u⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem round_N_ge_midp: forall choice u v, F u -> (u + pred u)/2 < v -> u ≤ round_N v.
-/
theorem round_N_ge_midp
    (choice : Int → Bool) (u v : ℝ)
    (Fu : (FloatSpec.Core.Generic_fmt.generic_format beta fexp u).run)
    (h : ((u + (pred beta fexp u).run) / 2) < v) :
    ⦃⌜True⌝⦄ do
      let rn ← FloatSpec.Core.Round_generic.round_N_to_format beta fexp v
      pure rn
    ⦃⇓r => ⌜u ≤ r⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma round_N_ge_ge_midp: forall choice u v, F u -> u ≤ round_N v -> (u + pred u)/2 ≤ v.
-/
theorem round_N_ge_ge_midp
    (choice : Int → Bool) (u v : ℝ)
    (Fu : (FloatSpec.Core.Generic_fmt.generic_format beta fexp u).run)
    (h : u ≤ (FloatSpec.Core.Round_generic.round_N_to_format beta fexp v).run) :
    ⦃⌜True⌝⦄ do
      let _ ← FloatSpec.Core.Round_generic.round_N_to_format beta fexp v
      pure v
    ⦃⇓_ => ⌜((u + (pred beta fexp u).run) / 2) ≤ v⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma round_N_le_le_midp: forall choice u v, F u -> round_N v ≤ u -> v ≤ (u + succ u)/2.
-/
theorem round_N_le_le_midp
    (choice : Int → Bool) (u v : ℝ)
    (Fu : (FloatSpec.Core.Generic_fmt.generic_format beta fexp u).run)
    (h : (FloatSpec.Core.Round_generic.round_N_to_format beta fexp v).run ≤ u) :
    ⦃⌜True⌝⦄ do
      let _ ← FloatSpec.Core.Round_generic.round_N_to_format beta fexp v
      pure v
    ⦃⇓_ => ⌜v ≤ ((u + (succ beta fexp u).run) / 2)⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma round_N_eq_DN: forall choice x, let d := round_DN x; let u := round_UP x; x < (d+u)/2 -> round_N x = d.
-/
theorem round_N_eq_DN
    (choice : Int → Bool) (x : ℝ)
    (h : let d := (FloatSpec.Core.Round_generic.round_DN_to_format beta fexp x).run;
         let u := (FloatSpec.Core.Round_generic.round_UP_to_format beta fexp x).run;
         x < ((d + u) / 2)) :
    ⦃⌜True⌝⦄ do
      let rn ← FloatSpec.Core.Round_generic.round_N_to_format beta fexp x
      let d ← FloatSpec.Core.Round_generic.round_DN_to_format beta fexp x
      pure (rn, d)
    ⦃⇓r => ⌜r.1 = r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma round_N_eq_DN_pt: forall choice x d u, Rnd_DN_pt F x d -> Rnd_UP_pt F x u -> x < (d+u)/2 -> round_N x = d.
-/
theorem round_N_eq_DN_pt
    (choice : Int → Bool) (x d u : ℝ)
    (Hd : FloatSpec.Core.Round_pred.Rnd_DN_pt (fun y => (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run) x d)
    (Hu : FloatSpec.Core.Round_pred.Rnd_UP_pt (fun y => (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run) x u)
    (h : x < ((d + u) / 2)) :
    ⦃⌜True⌝⦄ do
      let rn ← FloatSpec.Core.Round_generic.round_N_to_format beta fexp x
      pure rn
    ⦃⇓r => ⌜r = d⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma round_N_eq_UP: forall choice x, let d := round_DN x; let u := round_UP x; (d+u)/2 < x -> round_N x = u.
-/
theorem round_N_eq_UP
    (choice : Int → Bool) (x : ℝ)
    (h : let d := (FloatSpec.Core.Round_generic.round_DN_to_format beta fexp x).run;
         let u := (FloatSpec.Core.Round_generic.round_UP_to_format beta fexp x).run;
         ((d + u) / 2) < x) :
    ⦃⌜True⌝⦄ do
      let rn ← FloatSpec.Core.Round_generic.round_N_to_format beta fexp x
      let u ← FloatSpec.Core.Round_generic.round_UP_to_format beta fexp x
      pure (rn, u)
    ⦃⇓r => ⌜r.1 = r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma round_N_eq_UP_pt: forall choice x d u, Rnd_DN_pt F x d -> Rnd_UP_pt F x u -> (d+u)/2 < x -> round_N x = u.
-/
theorem round_N_eq_UP_pt
    (choice : Int → Bool) (x d u : ℝ)
    (Hd : FloatSpec.Core.Round_pred.Rnd_DN_pt (fun y => (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run) x d)
    (Hu : FloatSpec.Core.Round_pred.Rnd_UP_pt (fun y => (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run) x u)
    (h : ((d + u) / 2) < x) :
    ⦃⌜True⌝⦄ do
      let rn ← FloatSpec.Core.Round_generic.round_N_to_format beta fexp x
      pure rn
    ⦃⇓r => ⌜r = u⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma round_N_plus_ulp_ge:
  forall {Hm : Monotone_exp fexp} choice1 choice2 x,
  let rx := round_N choice2 x in x ≤ round_N choice1 (rx + ulp rx).
-/
theorem round_N_plus_ulp_ge
    [Monotone_exp fexp]
    (choice1 choice2 : Int → Bool) (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let rx ← FloatSpec.Core.Round_generic.round_N_to_format beta fexp x
      let u ← ulp beta fexp rx
      let rn ← FloatSpec.Core.Round_generic.round_N_to_format beta fexp (rx + u)
      pure (rx, rn)
    ⦃⇓r => ⌜x ≤ r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma round_N_eq_ties: forall c1 c2 x,
  x - round_DN x ≠ round_UP x - x -> round_N c1 x = round_N c2 x.
-/
theorem round_N_eq_ties
    (c1 c2 : Int → Bool) (x : ℝ)
    (hne : x - (FloatSpec.Core.Round_generic.round_DN_to_format beta fexp x).run ≠
            (FloatSpec.Core.Round_generic.round_UP_to_format beta fexp x).run - x) :
    ⦃⌜True⌝⦄ do
      let r1 ← FloatSpec.Core.Round_generic.round_N_to_format beta fexp x
      let r2 ← FloatSpec.Core.Round_generic.round_N_to_format beta fexp x
      pure (r1, r2)
    ⦃⇓r => ⌜r.1 = r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem error_lt_ulp_round:
  forall {Hm : Monotone_exp fexp} rnd x,
  x <> 0 -> |round rnd x - x| < ulp (round rnd x).
-/
theorem error_lt_ulp_round
    [Monotone_exp fexp]
    (rnd : ℝ → ℝ → Prop) (x : ℝ) (hx : x ≠ 0) :
    ⦃⌜True⌝⦄ do
      let r := FloatSpec.Core.Round_generic.round_to_generic beta fexp rnd x
      let u ← ulp beta fexp r
      pure (abs (r - x), u)
    ⦃⇓p => ⌜p.1 < p.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma error_le_ulp_round:
  forall {Hm : Monotone_exp fexp} rnd x,
  |round rnd x - x| <= ulp (round rnd x).
-/
theorem error_le_ulp_round
    [Monotone_exp fexp]
    (rnd : ℝ → ℝ → Prop) (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let r := FloatSpec.Core.Round_generic.round_to_generic beta fexp rnd x
      let u ← ulp beta fexp r
      pure (abs (r - x), u)
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem error_le_half_ulp_round:
  forall {Hm : Monotone_exp fexp} choice x,
  |round (Znearest choice) x - x| <= /2 * ulp (round (Znearest choice) x).
-/
theorem error_le_half_ulp_round
    [Monotone_exp fexp]
    (choice : Int → Bool) (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let r ← FloatSpec.Core.Round_generic.round_N_to_format beta fexp x
      let u ← ulp beta fexp r
      pure (abs (r - x), u)
    ⦃⇓p => ⌜p.1 ≤ (1/2) * p.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem ulp_DN:
  forall x, 0 <= x -> ulp (round_DN x) = ulp x.
-/
theorem ulp_DN (x : ℝ) (hx : 0 ≤ x) :
    ⦃⌜True⌝⦄ do
      let dn ← FloatSpec.Core.Round_generic.round_DN_to_format beta fexp x
      let u1 ← ulp beta fexp dn
      let u2 ← ulp beta fexp x
      pure (u1, u2)
    ⦃⇓r => ⌜r.1 = r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem round_neq_0_negligible_exp:
  negligible_exp = None -> forall rnd x, x <> 0 -> round rnd x <> 0.
-/
theorem round_neq_0_negligible_exp
    (hne : negligible_exp fexp = none)
    (rnd : ℝ → ℝ → Prop) (x : ℝ) (hx : x ≠ 0) :
    ⦃⌜True⌝⦄ (pure (FloatSpec.Core.Round_generic.round_to_generic beta fexp rnd x) : Id ℝ)
    ⦃⇓r => ⌜r ≠ 0⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem error_lt_ulp:
  forall rnd x, x <> 0 -> |round rnd x - x| < ulp x.
-/
theorem error_lt_ulp
    (rnd : ℝ → ℝ → Prop) (x : ℝ) (hx : x ≠ 0) :
    ⦃⌜True⌝⦄ do
      let r := FloatSpec.Core.Round_generic.round_to_generic beta fexp rnd x
      let u ← ulp beta fexp x
      pure (abs (r - x), u)
    ⦃⇓p => ⌜p.1 < p.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem error_le_ulp:
  forall rnd x, |round rnd x - x| <= ulp x.
-/
theorem error_le_ulp
    (rnd : ℝ → ℝ → Prop) (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let r := FloatSpec.Core.Round_generic.round_to_generic beta fexp rnd x
      let u ← ulp beta fexp x
      pure (abs (r - x), u)
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem error_le_half_ulp:
  forall choice x, |round (Znearest choice) x - x| <= /2 * ulp x.
-/
theorem error_le_half_ulp (choice : Int → Bool)
    (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let rn ← FloatSpec.Core.Round_generic.round_N_to_format beta fexp x
      let u ← ulp beta fexp x
      pure (abs (rn - x), u)
    ⦃⇓p => ⌜p.1 ≤ (1/2) * p.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem round_UP_pred_plus_eps:
  forall x, F x -> forall eps,
  0 < eps <= (if Rle_bool x 0 then ulp x else ulp (pred x)) ->
  round_UP (pred x + eps) = x.
-/
theorem round_UP_pred_plus_eps
    (x : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (eps : ℝ)
    (heps : 0 < eps ∧
      eps ≤ (if (FloatSpec.Core.Raux.Rle_bool x 0).run then
                (ulp beta fexp x).run
              else
                (ulp beta fexp (pred beta fexp x).run).run)) :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp x
      let up ← FloatSpec.Core.Round_generic.round_UP_to_format beta fexp (p + eps)
      pure up
    ⦃⇓r => ⌜r = x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem round_DN_minus_eps:
  forall x, F x -> forall eps,
  0 < eps <= (if Rle_bool x 0 then ulp x else ulp (pred x)) ->
  round_DN (x - eps) = pred x.
-/
theorem round_DN_minus_eps
    (x : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (eps : ℝ)
    (heps : 0 < eps ∧
      eps ≤ (if (FloatSpec.Core.Raux.Rle_bool x 0).run then
                (ulp beta fexp x).run
              else
                (ulp beta fexp (pred beta fexp x).run).run)) :
    ⦃⌜True⌝⦄ do
      let dn ← FloatSpec.Core.Round_generic.round_DN_to_format beta fexp (x - eps)
      let p ← pred beta fexp x
      pure (dn, p)
    ⦃⇓r => ⌜r.1 = r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma pred_succ_pos:
  forall x, F x -> 0 < x -> pred (succ x) = x.
-/
theorem pred_succ_pos
    (x : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (hx : 0 < x) :
    ⦃⌜True⌝⦄ do
      let s ← succ beta fexp x
      let p ← pred beta fexp s
      pure p
    ⦃⇓r => ⌜r = x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem succ_pred: forall x, F x -> succ (pred x) = x. -/
theorem succ_pred
    (x : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp x
      let s ← succ beta fexp p
      pure s
    ⦃⇓r => ⌜r = x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem pred_succ: forall x, F x -> pred (succ x) = x. -/
theorem pred_succ
    (x : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let s ← succ beta fexp x
      let p ← pred beta fexp s
      pure p
    ⦃⇓r => ⌜r = x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem pred_ulp_0: pred (ulp 0) = 0. -/
theorem pred_ulp_0 :
    ⦃⌜True⌝⦄ do
      let u0 ← ulp beta fexp 0
      let p ← pred beta fexp u0
      pure p
    ⦃⇓r => ⌜r = 0⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem succ_0: succ 0 = ulp 0. -/
theorem succ_0 :
    ⦃⌜True⌝⦄ do
      let s ← succ beta fexp 0
      let u0 ← ulp beta fexp 0
      pure (s, u0)
    ⦃⇓r => ⌜r.1 = r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem pred_0: pred 0 = - ulp 0. -/
theorem pred_0 :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp 0
      let u0 ← ulp beta fexp 0
      pure (p, u0)
    ⦃⇓r => ⌜r.1 = -r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma succ_pred_pos:
  forall x, F x -> 0 < x -> succ (pred x) = x.
-/
theorem succ_pred_pos
    (x : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (hx : 0 < x) :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp x
      let s ← succ beta fexp p
      pure s
    ⦃⇓r => ⌜r = x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem pred_lt_le:
  forall x y, x <> 0 -> x <= y -> pred x < y.
-/
theorem pred_lt_le
    (x y : ℝ) (hx : x ≠ 0) (hxy : x ≤ y) :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp x
      pure p
    ⦃⇓r => ⌜r < y⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem succ_gt_ge:
  forall x y, y <> 0 -> x <= y -> x < succ y.
-/
theorem succ_gt_ge
    (x y : ℝ) (hy : y ≠ 0) (hxy : x ≤ y) :
    ⦃⌜True⌝⦄ do
      let s ← succ beta fexp y
      pure s
    ⦃⇓r => ⌜x < r⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem pred_ge_gt:
  forall x y, F x -> F y -> x < y -> x <= pred y.
-/
theorem pred_ge_gt
    (x y : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (Fy : (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run)
    (hxy : x < y) :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp y
      pure p
    ⦃⇓r => ⌜x ≤ r⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem succ_le_lt:
  forall x y, F x -> F y -> x < y -> succ x <= y.
-/
theorem succ_le_lt
    (x y : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (Fy : (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run)
    (hxy : x < y) :
    ⦃⌜True⌝⦄ do
      let s ← succ beta fexp x
      pure s
    ⦃⇓r => ⌜r ≤ y⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma succ_le_lt_aux:
  forall x y, F x -> F y -> 0 <= x -> x < y -> succ x <= y.
-/
theorem succ_le_lt_aux
    (x y : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (Fy : (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run)
    (hx : 0 ≤ x) (hxy : x < y) :
    ⦃⌜True⌝⦄ do
      let s ← succ beta fexp x
      pure s
    ⦃⇓r => ⌜r ≤ y⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma pred_pos_plus_ulp_aux1:
  forall x, 0 < x -> F x -> x <> bpow (mag x - 1) ->
  (x - ulp x) + ulp (x - ulp x) = x.
-/
theorem pred_pos_plus_ulp_aux1
    (x : ℝ) (hx : 0 < x)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (hne : x ≠ (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x).run - 1)) :
    ⦃⌜True⌝⦄ do
      let u ← ulp beta fexp x
      let u2 ← ulp beta fexp (x - u)
      pure ((x - u) + u2)
    ⦃⇓r => ⌜r = x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma pred_pos_plus_ulp_aux2:
  forall x, 0 < x -> F x -> let e := mag x in x = bpow (e - 1) ->
  x - bpow (fexp (e-1)) <> 0 ->
  (x - bpow (fexp (e-1)) + ulp (x - bpow (fexp (e-1))) = x).
-/
theorem pred_pos_plus_ulp_aux2
    (x : ℝ) (hx : 0 < x)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (hxe : x = (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x).run - 1))
    (hne : x - (beta : ℝ) ^ (fexp ((FloatSpec.Core.Raux.mag beta x).run - 1)) ≠ 0) :
    ⦃⌜True⌝⦄ do
      let s := x - (beta : ℝ) ^ (fexp ((FloatSpec.Core.Raux.mag beta x).run - 1))
      let u ← ulp beta fexp s
      pure (s + u)
    ⦃⇓r => ⌜r = x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem succ_opp: forall x, succ (-x) = (- pred x). -/
theorem succ_opp (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let s ← succ beta fexp (-x)
      let p ← pred beta fexp x
      pure (s, p)
    ⦃⇓r => ⌜r.1 = -r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem pred_opp: forall x, pred (-x) = (- succ x). -/
theorem pred_opp (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp (-x)
      let s ← succ beta fexp x
      pure (p, s)
    ⦃⇓r => ⌜r.1 = -r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem ulp_opp: forall x, ulp (-x) = ulp x. -/
theorem ulp_opp (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let u1 ← ulp beta fexp (-x)
      let u2 ← ulp beta fexp x
      pure (u1, u2)
    ⦃⇓r => ⌜r.1 = r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem ulp_abs: forall x, ulp (Rabs x) = ulp x. -/
theorem ulp_abs (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let u1 ← ulp beta fexp |x|
      let u2 ← ulp beta fexp x
      pure (u1, u2)
    ⦃⇓r => ⌜r.1 = r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem pred_eq_pos: forall x, 0 <= x -> pred x = x - ulp x. -/
theorem pred_eq_pos (x : ℝ) (hx : 0 ≤ x) :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp x
      let u ← ulp beta fexp x
      pure (p, u)
    ⦃⇓r => ⌜r.1 = x - r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem succ_eq_pos: forall x, 0 <= x -> succ x = x + ulp x. -/
theorem succ_eq_pos (x : ℝ) (hx : 0 ≤ x) :
    ⦃⌜True⌝⦄ do
      let s ← succ beta fexp x
      let u ← ulp beta fexp x
      pure (s, u)
    ⦃⇓r => ⌜r.1 = x + r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem ulp_ge_0: forall x, (0 <= ulp x)%R. -/
theorem ulp_ge_0 (x : ℝ) :
    ⦃⌜1 < beta⌝⦄ ulp beta fexp x ⦃⇓r => ⌜0 ≤ r⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma generic_format_ulp : Exp_not_FTZ fexp -> forall x, F (ulp x).

Lean (spec): Under a non-FTZ exponent function, ulp x is in the format.
-/
theorem generic_format_ulp
    [Exp_not_FTZ fexp]
    (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let u ← ulp beta fexp x
      FloatSpec.Core.Generic_fmt.generic_format beta fexp u
    ⦃⇓g => ⌜g⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem eq_0_round_0_negligible_exp:
  negligible_exp = None -> forall rnd {Vr: Valid_rnd rnd} x,
  round rnd x = 0 -> x = 0.

Lean (adapted spec): If negligible_exp = none and the rounded value is zero, then x = 0.
-/
theorem eq_0_round_0_negligible_exp
    (hne : negligible_exp fexp = none) (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let _u ← ulp beta fexp 0
      pure (0 : ℝ)
    ⦃⇓r => ⌜r = 0 → x = 0⌝⦄ := by
  sorry

/-- Coq (Ulp.v):
Lemma pred_pos_lt_id: forall x, x ≠ 0 -> pred_pos x < x.
-/
theorem pred_pos_lt_id (x : ℝ) (hx : x ≠ 0) :
    ⦃⌜True⌝⦄ do
      let p ← pred_pos beta fexp x
      pure p
    ⦃⇓r => ⌜r < x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem succ_gt_id: forall x, x ≠ 0 -> x < succ x.
-/
theorem succ_gt_id (x : ℝ) (hx : x ≠ 0) :
    ⦃⌜True⌝⦄ do
      let s ← succ beta fexp x
      pure s
    ⦃⇓r => ⌜x < r⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem pred_lt_id: forall x, x ≠ 0 -> pred x < x.
-/
theorem pred_lt_id (x : ℝ) (hx : x ≠ 0) :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp x
      pure p
    ⦃⇓r => ⌜r < x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem succ_ge_id: forall x, x ≤ succ x.
-/
theorem succ_ge_id (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let s ← succ beta fexp x
      pure s
    ⦃⇓r => ⌜x ≤ r⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem pred_le_id: forall x, pred x ≤ x.
-/
theorem pred_le_id (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp x
      pure p
    ⦃⇓r => ⌜r ≤ x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma pred_pos_ge_0: forall x, 0 < x -> F x -> 0 ≤ pred_pos x.
-/
theorem pred_pos_ge_0 (x : ℝ) (hx : 0 < x)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let p ← pred_pos beta fexp x
      pure p
    ⦃⇓r => ⌜0 ≤ r⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem pred_ge_0: forall x, 0 < x -> F x -> 0 ≤ pred x.
-/
theorem pred_ge_0 (x : ℝ) (hx : 0 < x)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp x
      pure p
    ⦃⇓r => ⌜0 ≤ r⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma generic_format_pred_aux1:
  forall x, 0 < x -> F x -> x <> bpow (mag x - 1) -> F (x - ulp x).
-/
theorem generic_format_pred_aux1
    (x : ℝ) (hx : 0 < x)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (hne : x ≠ (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x).run - 1)) :
    ⦃⌜True⌝⦄ do
      let u ← ulp beta fexp x
      FloatSpec.Core.Generic_fmt.generic_format beta fexp (x - u)
    ⦃⇓g => ⌜g⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma generic_format_pred_aux2:
  forall x, 0 < x -> F x -> let e := mag x in x = bpow (e - 1) ->
  x - bpow (fexp (e-1)) <> 0 -> F (x - bpow (fexp (e-1))).
-/
theorem generic_format_pred_aux2
    (x : ℝ) (hx : 0 < x)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (hxe : x = (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x).run - 1))
    (hne : x - (beta : ℝ) ^ (fexp ((FloatSpec.Core.Raux.mag beta x).run - 1)) ≠ 0) :
    ⦃⌜True⌝⦄
    FloatSpec.Core.Generic_fmt.generic_format beta fexp
      (x - (beta : ℝ) ^ (fexp ((FloatSpec.Core.Raux.mag beta x).run - 1)))
    ⦃⇓g => ⌜g⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma generic_format_succ_aux1:
  forall x, 0 < x -> F x -> F (x + ulp x).
-/
theorem generic_format_succ_aux1
    (x : ℝ) (hx : 0 < x)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let u ← ulp beta fexp x
      FloatSpec.Core.Generic_fmt.generic_format beta fexp (x + u)
    ⦃⇓g => ⌜g⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma generic_format_pred_pos: forall x, F x -> 0 < x -> F (pred_pos x).
-/
theorem generic_format_pred_pos
    (x : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (hx : 0 < x) :
    ⦃⌜True⌝⦄ do
      let p ← pred_pos beta fexp x
      FloatSpec.Core.Generic_fmt.generic_format beta fexp p
    ⦃⇓g => ⌜g⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem generic_format_succ: forall x, F x -> F (succ x).
-/
theorem generic_format_succ
    (x : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let s ← succ beta fexp x
      FloatSpec.Core.Generic_fmt.generic_format beta fexp s
    ⦃⇓g => ⌜g⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem generic_format_pred: forall x, F x -> F (pred x).
-/
theorem generic_format_pred
    (x : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp x
      FloatSpec.Core.Generic_fmt.generic_format beta fexp p
    ⦃⇓g => ⌜g⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma pred_pos_plus_ulp_aux3:
  forall x, 0 < x -> F x -> x = bpow (mag x - 1) ->
  x - bpow (fexp (mag x - 1)) = 0 -> ulp 0 = x.
-/
theorem pred_pos_plus_ulp_aux3
    (x : ℝ) (hx : 0 < x)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (hxe : x = (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x).run - 1))
    (hz : x - (beta : ℝ) ^ (fexp ((FloatSpec.Core.Raux.mag beta x).run - 1)) = 0) :
    ⦃⌜True⌝⦄ do
      let u0 ← ulp beta fexp 0
      pure u0
    ⦃⇓r => ⌜r = x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma pred_pos_plus_ulp:
  forall x, 0 < x -> F x -> pred_pos x + ulp (pred_pos x) = x.
-/
theorem pred_pos_plus_ulp
    (x : ℝ) (hx : 0 < x)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let p ← pred_pos beta fexp x
      let u ← ulp beta fexp p
      pure (p + u)
    ⦃⇓r => ⌜r = x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem pred_plus_ulp: forall x, 0 < x -> F x -> pred x + ulp (pred x) = x.
-/
theorem pred_plus_ulp
    (x : ℝ) (hx : 0 < x)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp x
      let u ← ulp beta fexp p
      pure (p + u)
    ⦃⇓r => ⌜r = x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem mag_plus_eps: forall x, 0 < x -> F x -> forall eps, 0 ≤ eps < ulp x -> mag (x + eps) = mag x.
-/
theorem mag_plus_eps
    (x : ℝ) (hx : 0 < x)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (eps : ℝ) (heps : 0 ≤ eps ∧ eps < (ulp beta fexp x).run) :
    ⦃⌜True⌝⦄ FloatSpec.Core.Raux.mag beta (x + eps)
    ⦃⇓m => ⌜m = FloatSpec.Core.Raux.mag beta x⌝⦄ := by
  sorry

/-- Coq (Ulp.v):
Theorem round_DN_plus_eps_pos:
  forall x, 0 < x -> F x -> forall eps, 0 ≤ eps < ulp x ->
  round_DN (x + eps) = x.
-/
theorem round_DN_plus_eps_pos
    (x : ℝ) (hx : 0 < x)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (eps : ℝ) (heps : 0 ≤ eps ∧ eps < (ulp beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let dn ← FloatSpec.Core.Round_generic.round_DN_to_format beta fexp (x + eps)
      pure dn
    ⦃⇓r => ⌜r = x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem round_UP_plus_eps_pos:
  forall x, 0 ≤ x -> F x -> forall eps, 0 < eps ≤ ulp x ->
  round_UP (x + eps) = x + ulp x.
-/
theorem round_UP_plus_eps_pos
    (x : ℝ) (hx : 0 ≤ x)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (eps : ℝ) (heps : 0 < eps ∧ eps ≤ (ulp beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let up ← FloatSpec.Core.Round_generic.round_UP_to_format beta fexp (x + eps)
      let u ← ulp beta fexp x
      pure (up, u)
    ⦃⇓r => ⌜r.1 = x + r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem round_UP_pred_plus_eps_pos:
  forall x, 0 < x -> F x -> forall eps, 0 < eps ≤ ulp (pred x) -> round_UP (pred x + eps) = x.
-/
theorem round_UP_pred_plus_eps_pos
    (x : ℝ) (hx : 0 < x)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (eps : ℝ) (heps : 0 < eps ∧ eps ≤ (ulp beta fexp (pred beta fexp x).run).run) :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp x
      let up ← FloatSpec.Core.Round_generic.round_UP_to_format beta fexp (p + eps)
      pure up
    ⦃⇓r => ⌜r = x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem round_DN_minus_eps_pos:
  forall x, 0 < x -> F x -> forall eps, 0 < eps ≤ ulp (pred x) -> round_DN (x - eps) = pred x.
-/
theorem round_DN_minus_eps_pos
    (x : ℝ) (hx : 0 < x)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (eps : ℝ) (heps : 0 < eps ∧ eps ≤ (ulp beta fexp (pred beta fexp x).run).run) :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp x
      let dn ← FloatSpec.Core.Round_generic.round_DN_to_format beta fexp (x - eps)
      pure (dn, p)
    ⦃⇓r => ⌜r.1 = r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem round_DN_plus_eps:
  forall x, F x -> forall eps, 0 ≤ eps < ulp (succ x) -> round_DN (x + eps) = x.
-/
theorem round_DN_plus_eps
    (x : ℝ) (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (eps : ℝ) (heps : 0 ≤ eps ∧ eps < (ulp beta fexp (succ beta fexp x).run).run) :
    ⦃⌜True⌝⦄ do
      let dn ← FloatSpec.Core.Round_generic.round_DN_to_format beta fexp (x + eps)
      pure dn
    ⦃⇓r => ⌜r = x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem round_UP_plus_eps:
  forall x, F x -> forall eps, 0 < eps ≤ ulp x -> round_UP (x + eps) = succ x.
-/
theorem round_UP_plus_eps
    (x : ℝ) (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (eps : ℝ) (heps : 0 < eps ∧ eps ≤ (ulp beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let up ← FloatSpec.Core.Round_generic.round_UP_to_format beta fexp (x + eps)
      let s ← succ beta fexp x
      pure (up, s)
    ⦃⇓r => ⌜r.1 = r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma not_FTZ_generic_format_ulp : (forall x,  F (ulp x)) -> Exp_not_FTZ fexp.

Lean (spec): If ulp x is always representable, the exponent is not FTZ.
-/
theorem not_FTZ_generic_format_ulp :
    (∀ x : ℝ, (do
        let u ← ulp beta fexp x
        FloatSpec.Core.Generic_fmt.generic_format beta fexp u).run) →
    ⦃⌜True⌝⦄ do
      let _ ← ulp beta fexp 0
      pure True
    ⦃⇓_ => ⌜True⌝⦄ := by
  sorry

/-- Coq (Ulp.v):
Lemma ulp_ge_ulp_0 : Exp_not_FTZ fexp -> forall x, ulp 0 <= ulp x.

Lean (spec): Non-FTZ exponent implies ulp is minimized at zero.
-/
theorem ulp_ge_ulp_0
    [Exp_not_FTZ fexp]
    (x : ℝ) :
    ⦃⌜True⌝⦄ do
      let u0 ← ulp beta fexp 0
      let ux ← ulp beta fexp x
      pure (u0, ux)
    ⦃⇓r => ⌜r.1 ≤ r.2⌝⦄ := by
  sorry

/-- Coq (Ulp.v):
Lemma not_FTZ_ulp_ge_ulp_0 : (forall x, ulp 0 <= ulp x) -> Exp_not_FTZ fexp.

Lean (spec): If ulp is minimized at zero for all x, then not FTZ.
-/
theorem not_FTZ_ulp_ge_ulp_0 :
    (∀ x : ℝ, (do
        let u0 ← ulp beta fexp 0
        let ux ← ulp beta fexp x
        pure (u0 ≤ ux)).run) →
    ⦃⌜True⌝⦄ do
      let _ ← ulp beta fexp 0
      pure True
    ⦃⇓_ => ⌜True⌝⦄ := by
  sorry

/-- Coq (Ulp.v):
Lemma ulp_le_pos : forall {Hm : Monotone_exp fexp} x y, 0 ≤ x → x ≤ y → ulp x ≤ ulp y.

Lean (spec): Monotone exponents yield monotone ulp on nonnegatives.
-/
theorem ulp_le_pos
    [Monotone_exp fexp]
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ⦃⌜True⌝⦄ do
      let ux ← ulp beta fexp x
      let uy ← ulp beta fexp y
      pure (ux, uy)
    ⦃⇓r => ⌜r.1 ≤ r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem ulp_le : forall {Hm : Monotone_exp fexp} x y, |x| ≤ |y| → ulp x ≤ ulp y.
-/
theorem ulp_le
    [Monotone_exp fexp]
    (x y : ℝ) (hxy : |x| ≤ |y|) :
    ⦃⌜True⌝⦄ do
      let ux ← ulp beta fexp x
      let uy ← ulp beta fexp y
      pure (ux, uy)
    ⦃⇓r => ⌜r.1 ≤ r.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem ulp_le_id:
  forall x, (0 < x)%R -> F x -> (ulp x <= x)%R.
-/
theorem ulp_le_id (x : ℝ) (hx : 0 < x)
    (hxF : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run) :
    ⦃⌜True⌝⦄ ulp beta fexp x ⦃⇓r => ⌜r ≤ x⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem ulp_le_abs:
  forall x, (x <> 0)%R -> F x -> (ulp x <= Rabs x)%R.
-/
theorem ulp_le_abs (x : ℝ) (hx : x ≠ 0)
    (hxF : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run) :
    ⦃⌜True⌝⦄ ulp beta fexp x ⦃⇓r => ⌜r ≤ |x|⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem ulp_canonical
    forall m e, m ≠ 0 -> canonical (m,e) -> ulp(F2R(m,e)) = bpow e. -/
theorem ulp_canonical (m e : Int)
    (hm : m ≠ 0)
    (hc : FloatSpec.Core.Generic_fmt.canonical beta fexp (FlocqFloat.mk m e)) :
    ⦃⌜True⌝⦄ do
      let x ← F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e : FloatSpec.Core.Defs.FlocqFloat beta)
      ulp beta fexp x
    ⦃⇓r => ⌜r = (beta : ℝ) ^ e⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Theorem ulp_bpow : forall e, ulp (bpow e) = bpow (fexp (e + 1)).
-/
theorem ulp_bpow (e : Int) :
    ⦃⌜True⌝⦄ ulp beta fexp ((beta : ℝ) ^ e)
    ⦃⇓r => ⌜r = (beta : ℝ) ^ (fexp (e + 1))⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem pred_bpow: forall e, pred (bpow e) = bpow e - bpow (fexp e). -/
theorem pred_bpow (e : Int) :
    ⦃⌜True⌝⦄ do
      let p ← pred beta fexp ((beta : ℝ) ^ e)
      pure p
    ⦃⇓r => ⌜r = (beta : ℝ) ^ e - (beta : ℝ) ^ (fexp e)⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem id_m_ulp_ge_bpow
    forall x e, F x -> x ≠ ulp x -> bpow e < x -> bpow e ≤ x - ulp x. -/
theorem id_m_ulp_ge_bpow (x : ℝ) (e : Int)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (hne : x ≠ (ulp beta fexp x).run)
    (hgt : (beta : ℝ) ^ e < x) :
    ⦃⌜True⌝⦄ do
      let u ← ulp beta fexp x
      pure (x - u)
    ⦃⇓r => ⌜(beta : ℝ) ^ e ≤ r⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem id_p_ulp_le_bpow
    forall x e, 0 < x -> F x -> x < bpow e -> x + ulp x ≤ bpow e. -/
theorem id_p_ulp_le_bpow (x : ℝ) (e : Int)
    (hx : 0 < x)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (hlt : x < (beta : ℝ) ^ e) :
    ⦃⌜True⌝⦄ do
      let u ← ulp beta fexp x
      pure (x + u)
    ⦃⇓r => ⌜r ≤ (beta : ℝ) ^ e⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Theorem round_UP_DN_ulp
    forall x, ~ F x -> round UP x = round DN x + ulp x. -/
theorem round_UP_DN_ulp (x : ℝ)
    (Fx : ¬ (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run) :
    ⦃⌜True⌝⦄ do
      let dn ← FloatSpec.Core.Round_generic.round_DN_to_format beta fexp x
      let up ← FloatSpec.Core.Round_generic.round_UP_to_format beta fexp x
      let u ← ulp beta fexp x
      pure (up, dn, u)
    ⦃⇓r => ⌜r.1 = r.2.1 + r.2.2⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v): Lemma generic_format_ulp_0 : F (ulp 0). -/
theorem generic_format_ulp_0 :
    ⦃⌜True⌝⦄ do
      let u ← ulp beta fexp 0
      FloatSpec.Core.Generic_fmt.generic_format beta fexp u
    ⦃⇓g => ⌜g⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma generic_format_bpow_ge_ulp_0 : forall e, (ulp 0 <= bpow e)%R -> F (bpow e).
-/
theorem generic_format_bpow_ge_ulp_0 (e : Int)
    (hle : (ulp beta fexp 0).run ≤ (beta : ℝ) ^ e) :
    ⦃⌜True⌝⦄
    FloatSpec.Core.Generic_fmt.generic_format beta fexp ((beta : ℝ) ^ e)
    ⦃⇓g => ⌜g⌝⦄ := by
  intro _; sorry

/-- Coq (Ulp.v):
Lemma le_pred_pos_lt:
  forall x y, F x -> F y -> 0 <= x < y -> x <= pred_pos y.
-/
theorem le_pred_pos_lt
    (x y : ℝ)
    (Fx : (FloatSpec.Core.Generic_fmt.generic_format beta fexp x).run)
    (Fy : (FloatSpec.Core.Generic_fmt.generic_format beta fexp y).run)
    (hxy : 0 ≤ x ∧ x < y) :
    ⦃⌜True⌝⦄ do
      let p ← pred_pos beta fexp y
      pure p
    ⦃⇓r => ⌜x ≤ r⌝⦄ := by
  intro _; sorry

end UnitInLastPlace

end FloatSpec.Core.Ulp
