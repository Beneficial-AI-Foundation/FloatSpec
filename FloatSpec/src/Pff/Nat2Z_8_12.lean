module


-- Mirror of Coq file: flocq/src/Pff/Nat2Z_8_12.v
-- Provides Nat → Int compatibility lemma for division.

public import Std.Do.Triple
public import FloatSpec.src.Core
public import FloatSpec.src.Compat
public import FloatSpec.src.SimprocWP



@[expose] public section

open Std.Do
open FloatSpec.Core

namespace FloatSpec.Pff.Nat2Z

/-- Auxiliary: return {lit}`Int.ofNat (n / m)` as an {name}`Id` computation
    so we can state a Hoare-style specification mirroring Coq.

-/
def inj_div_eval (n m : Nat) : Int :=
  Int.ofNat (n / m)

/-- Coq lemma {lit}`Nat2Z.inj_div`:
    {lit}`Z.of_nat (n / m) = (Z.of_nat n / Z.of_nat m)`

    We express it with the project's Hoare triple style.

-/
theorem inj_div (n m : Nat) :
    ⦃⌜True⌝⦄
    (pure (inj_div_eval n m) : Id Int)
    ⦃⇓result => ⌜result = Int.ofNat n / Int.ofNat m⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure, inj_div_eval]

end FloatSpec.Pff.Nat2Z

end
