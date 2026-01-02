-- Mirror of Coq file: flocq/src/Pff/Nat2Z_8_12.v
-- Provides Nat → Int compatibility lemma for division.

import Std.Do.Triple
import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.SimprocWP
open Std.Do
open FloatSpec.Core

namespace FloatSpec.Pff.Nat2Z

/-- Auxiliary: return `Int.ofNat (n / m)` as an `Id` computation
    so we can state a Hoare-style specification mirroring Coq. -/
def inj_div_eval (n m : Nat) : Int :=
  Int.ofNat (n / m)

/-- Coq lemma `Nat2Z.inj_div`:
    `Z.of_nat (n / m) = (Z.of_nat n / Z.of_nat m)`

    We express it with the project’s Hoare triple style. -/
theorem inj_div (n m : Nat) :
    ⦃⌜True⌝⦄
    inj_div_eval n m
    ⦃⇓result => ⌜result = Int.ofNat n / Int.ofNat m⌝⦄ := by
  intro _
  simp [ inj_div_eval]

end FloatSpec.Pff.Nat2Z
