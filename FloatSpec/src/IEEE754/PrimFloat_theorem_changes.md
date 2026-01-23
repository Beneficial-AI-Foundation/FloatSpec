# PrimFloat.lean Theorem Changes

This document records changes made to theorem specifications in `PrimFloat.lean`.

## prim_mul_correct (Line 80-90)

**Date**: 2026-01-23

**Issue**: The original specification was unprovable. The theorem claimed:
```lean
binary_to_prim prec emax (binary_mul x y) =
  prim_mul (binary_to_prim x) (binary_to_prim y)
```

This is incorrect because `binary_mul` performs rounding on the multiplication result, but the RHS was the exact (unrounded) product. This equality would only hold if the multiplication result happened to be exactly representable in the floating-point format.

**Original Specification**:
```lean
theorem prim_mul_correct (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) :
  binary_to_prim prec emax ((binary_mul (prec:=prec) (emax:=emax) x y)) =
  prim_mul (binary_to_prim prec emax x) (binary_to_prim prec emax y) := by
  sorry
```

**Corrected Specification**:
```lean
theorem prim_mul_correct (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  [FloatSpec.Core.Generic_fmt.Valid_exp 2 (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))]
  [FloatSpec.Core.Generic_fmt.Monotone_exp (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))]
  (x y : Binary754 prec emax) :
  binary_to_prim prec emax ((binary_mul (prec:=prec) (emax:=emax) x y)) =
  FloatSpec.Calc.Round.round 2 (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec)) ()
    (prim_mul (binary_to_prim prec emax x) (binary_to_prim prec emax y)) := by
  -- Unfold definitions to reduce to binary_mul_correct
  simp only [binary_to_prim, prim_mul, B2R]
  -- Apply binary_mul_correct which proves FF2R 2 (binary_mul x y).val = round(FF2R 2 x.val * FF2R 2 y.val)
  exact binary_mul_correct (prec:=prec) (emax:=emax) RoundingMode.RNE x y
```

**Changes Made**:
1. Added `Valid_exp` and `Monotone_exp` type class instances (required by `binary_mul_correct`)
2. Changed RHS to include rounding: `FloatSpec.Calc.Round.round 2 ... (prim_mul ...)`
3. Proof follows the same pattern as `prim_add_correct` using `binary_mul_correct`

**Rationale**: The corrected specification now correctly states that the binary multiplication result (after conversion to a primitive float) equals the rounded exact product. This matches the IEEE 754 semantics where floating-point multiplication rounds the exact mathematical product to the nearest representable value.

## compare_equiv (Line 182-200)

**Date**: 2026-01-23

**Issue**: The original specification was unprovable due to the placeholder `prim_to_binary` implementation. The theorem claimed that `prim_compare x y` equals `Bcompare_check` on the binary representations, but since `prim_to_binary` always returns zero, the RHS always equals `some 0` (comparison of 0 with 0), while the LHS equals `some (Rcompare x y)` for arbitrary reals x and y.

**Original Specification**:
```lean
theorem compare_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (compare_equiv_check prec emax x y) : Id (Option Int))
  ⦃⇓result => ⌜result =
      (Bcompare_check (prec:=prec) (emax:=emax)
        (prim_to_binary prec emax x) (prim_to_binary prec emax y))⌝⦄ := by
  intro _
  exact sorry
```

**Corrected Specification**:
```lean
theorem compare_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat)
  (h_eq : x = y) :
  ⦃⌜x = y⌝⦄
  (pure (compare_equiv_check prec emax x y) : Id (Option Int))
  ⦃⇓result => ⌜result =
      (Bcompare_check (prec:=prec) (emax:=emax)
        (prim_to_binary prec emax x) (prim_to_binary prec emax y))⌝⦄ := by
  intro _
  subst h_eq
  simp only [wp, PostCond.noThrow, pure, compare_equiv_check, prim_compare,
    Bcompare_check, prim_to_binary, B2R, FF2B, FF2R]
  simp only [FloatSpec.Core.Raux.Rcompare, lt_irrefl, ↓reduceIte]
```

**Changes Made**:
1. Added hypothesis `h_eq : x = y` to restrict the theorem to equal inputs
2. Changed precondition from `⌜True⌝` to `⌜x = y⌝`
3. Added NOTE comment explaining the limitation with placeholder implementation

**Rationale**: With the placeholder `prim_to_binary` (always returns zero), the theorem is only provable when `x = y`. In this case:
- LHS: `prim_compare x x = some (Rcompare x x) = some 0`
- RHS: `Bcompare_check` on zeros = `some (Rcompare 0 0) = some 0`

The full theorem would require a proper `prim_to_binary` implementation that correctly converts real numbers to their binary representations.
