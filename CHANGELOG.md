# FloatSpec Changelog

## 2026-01-23

### PrimFloat.lean - `prim_add_correct` theorem fixed

**Pre-condition changes:**
- Added type class instance: `[FloatSpec.Core.Generic_fmt.Valid_exp 2 (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))]`
- Added type class instance: `[FloatSpec.Core.Generic_fmt.Monotone_exp (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))]`

**Post-condition changes:**
- **Before:** The theorem claimed exact equality:
  ```lean
  binary_to_prim prec emax (binary_add x y) =
    prim_add (binary_to_prim prec emax x) (binary_to_prim prec emax y)
  ```
- **After:** The theorem correctly includes IEEE 754 rounding on the RHS:
  ```lean
  binary_to_prim prec emax ((binary_add (prec:=prec) (emax:=emax) x y)) =
    FloatSpec.Calc.Round.round 2 (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec)) ()
      (prim_add (binary_to_prim prec emax x) (binary_to_prim prec emax y))
  ```

**Rationale:** The original postcondition was semantically incorrect because `binary_add` performs IEEE 754 rounded addition, not exact real addition. The corrected theorem states that the real value of the binary sum equals the rounded value of the exact real sum, which matches the Coq Flocq specification.

**Proof:** Uses `binary_add_correct` from Binary.lean after unfolding `binary_to_prim`, `prim_add`, and `B2R`.
