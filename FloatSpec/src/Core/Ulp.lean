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
import FloatSpec.src.Core.Float_prop
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Std.Do
open FloatSpec.Core.Generic_fmt

namespace FloatSpec.Core.Ulp

section UnitInLastPlace

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

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

/-- Coq (Ulp.v):
Lemma ulp_neq_0 : forall x, x <> 0%R -> ulp x = bpow (cexp beta fexp x).
-/
theorem ulp_neq_0 (x : ℝ) (hx : x ≠ 0) :
    ⦃⌜True⌝⦄
    ulp beta fexp x
    ⦃⇓r => ⌜r = (beta : ℝ) ^ ((FloatSpec.Core.Generic_fmt.cexp beta fexp x).run)⌝⦄ := by
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

/-- Coq (Ulp.v): Theorem ulp_ge_0: forall x, (0 <= ulp x)%R. -/
theorem ulp_ge_0 (x : ℝ) :
    ⦃⌜1 < beta⌝⦄ ulp beta fexp x ⦃⇓r => ⌜0 ≤ r⌝⦄ := by
  intro hβ
  unfold ulp
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  by_cases hx : x = 0
  · have : 0 < (beta : ℝ) ^ (fexp 1) := zpow_pos hbpos _
    simp [hx, le_of_lt this]
  · have : 0 < (beta : ℝ) ^ (fexp (mag beta x)) := zpow_pos hbpos _
    simp [hx, FloatSpec.Core.Generic_fmt.cexp, le_of_lt this]

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

/-- Coq (Ulp.v):
Theorem ulp_bpow : forall e, ulp (bpow e) = bpow (fexp (e + 1)).
-/
theorem ulp_bpow (e : Int) :
    ⦃⌜True⌝⦄ ulp beta fexp ((beta : ℝ) ^ e)
    ⦃⇓r => ⌜r = (beta : ℝ) ^ (fexp (e + 1))⌝⦄ := by
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

end UnitInLastPlace

end FloatSpec.Core.Ulp
