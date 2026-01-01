import Lean
import FloatSpec.src.Core.Generic_fmt

open Lean Meta Simp

/-- Definitional simproc: unfold `cexp` to its `Id`/`pure` form. -/
dsimproc [simp] reduceCexp (FloatSpec.Core.Generic_fmt.cexp _ _ _) := fun e => do
  unless e.isAppOfArity ``FloatSpec.Core.Generic_fmt.cexp 3 do
    return .continue
  let e' ← whnf e
  return .done e'

/-- Definitional simproc: unfold `scaled_mantissa` to its `Id`/`pure` form. -/
dsimproc [simp] reduceScaledMantissa (FloatSpec.Core.Generic_fmt.scaled_mantissa _ _ _) := fun e => do
  unless e.isAppOfArity ``FloatSpec.Core.Generic_fmt.scaled_mantissa 3 do
    return .continue
  let e' ← whnf e
  return .done e'
