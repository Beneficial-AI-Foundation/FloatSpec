# Changes to Pff2Flocq.lean

## Date: 2025-01-28

## Summary of Issues Found

### 1. `pff_round_equiv` theorem (line 145)

**Problem**: The theorem claims an equivalence between Pff rounding and Flocq rounding for all rounding modes, but the current implementation of `FloatSpec.Calc.Round.round` ignores the mode parameter and always uses `Ztrunc` (round toward zero).

**Root Cause**:
- `FloatSpec.Calc.Round.round` calls `round_to_generic` which uses `Ztrunc` internally
- The mode parameter is of type `Unit` and is completely ignored
- This is a simplification in the current implementation

**Theorem Statement**:
```lean
theorem pff_round_equiv (mode : PffRounding) (x : ℝ) (prec : Int) [Prec_gt_0 prec] :
  let flocq_rnd := pff_to_flocq_rnd mode
  let fexp := FLX_exp prec
  pff_to_R beta (flocq_to_pff (round_float beta fexp flocq_rnd x)) =
  FloatSpec.Calc.Round.round beta fexp () x
```

**Why it cannot be proven as-is**:
- LHS uses `pff_to_flocq_rnd mode` which returns:
  - `Znearest (fun _ => true)` for RN
  - `Ztrunc` for RZ
  - `Zceil` for RP
  - `Zfloor` for RM
- RHS always uses `Ztrunc` regardless of mode

**Proposed Fix**:
1. Add a specialized theorem `pff_round_equiv_RZ` that works for RZ mode
2. Keep the general `pff_round_equiv` as sorry pending a proper mode-aware implementation of `round_to_generic`

**Changes Made**:
1. Implemented `pff_to_flocq_rnd` in Pff.lean (was previously `sorry`)
2. Implemented `round_float` in Compat.lean (was previously a stub returning 0)
3. Added helper lemma `round_float_F2R`
4. **Added and PROVED `pff_round_equiv_RZ`** (2025-01-28): Fully proved theorem for RZ mode
   - Uses bijection `pff_flocq_bijection` and unfolds definitions
   - Proof works because both sides use `Ztrunc`
5. Kept `pff_round_equiv` as sorry stub with documentation explaining the limitation

## Files Modified

1. `/data/hantao/FloatSpec/FloatSpec/src/Pff/Pff.lean`:
   - Implemented `pff_to_flocq_rnd` function

2. `/data/hantao/FloatSpec/FloatSpec/src/Compat.lean`:
   - Implemented `round_float` function properly

3. `/data/hantao/FloatSpec/FloatSpec/src/Pff/Pff2Flocq.lean`:
   - Added helper lemma `round_float_F2R`
   - Added `pff_round_equiv_RZ` theorem (for RZ mode specifically)
   - Added detailed comments explaining why general theorem cannot be proven

## Recommendations for Future Work

1. **Mode-aware rounding**: Update `FloatSpec.Core.Generic_fmt.round_to_generic` to accept a proper rounding function parameter instead of ignoring the mode
2. **Consistent abstractions**: Ensure that `FloatSpec.Calc.Round.round` properly propagates the mode to the underlying implementation
3. **Complete the bijection chain**: Verify that `flocq_to_pff` followed by `pff_to_flocq` returns the original float

---

## Date: 2026-01-28

### 2. `rounding_error_in_format` lemma (line 334)

**Status**: Contains sorry at line 809 (in the `case pos` branch where `e_r ≥ e_min`)

**Goal at sorry**:
```lean
cexp 2 (FLT_exp emin prec) (F2R { Fnum := R, Fexp := e_min }) ≤ e_min
```

**Context**: This lemma states that the rounding error `a - (x + y)` is in `generic_format`. The proof structure:

1. Handles the zero error case directly (already complete)
2. For nonzero error, splits on whether `e_r ≥ e_min` or `e_r < e_min`
3. The `e_r < e_min` case is complete (error is zero by construction)
4. The `e_r ≥ e_min` case requires proving `cexp(R * 2^e_min) ≤ e_min`

**Mathematical Analysis**:

To prove `cexp(R * 2^e_min) ≤ e_min`, we need `mag(R * 2^e_min) ≤ e_min + prec`.

From Ztrunc bounds: `|R| < 2^d` where `d = e_r - e_min`.

This gives `|error| < 2^e_r`, so `mag(error) ≤ e_r`.

For `cexp(error) ≤ e_min`, we need `e_r - prec ≤ e_min`, i.e., `e_r ≤ e_min + prec`.

**Why this fails from format bounds alone**:

- `e_r = max(mag(x+y) - prec, emin)`
- From format: `|x+y| ≤ 2^(max(ex, ey) + prec + 1)`
- So `mag(x+y) ≤ max(ex, ey) + prec + 2`
- With `e_min = min(ex, ey)`: `mag(x+y) ≤ e_min + |ex - ey| + prec + 2`

For `e_r ≤ e_min + prec`, we need `|ex - ey| < prec - 2`, which is NOT guaranteed.

**The Coq Approach**:

The original Coq proof uses the round-to-nearest property:
- `|error| ≤ min(|x|, |y|)` (nearest rounding optimality)
- This gives `mag(error) ≤ e_min + prec` (from format bounds on min operand)
- Hence `cexp(error) ≤ e_min`

**Current Implementation Issue**:

The `FloatSpec.Calc.Round.round` function ignores the mode parameter and always uses `Ztrunc` (round-toward-zero), not round-to-nearest. The bound `|error| ≤ min(|x|, |y|)` does NOT hold for Ztrunc in general.

**Dependencies (all sorry stubs)**:
- `plus_error_le_l` (Plus_error.lean:171)
- `plus_error_le_r` (Plus_error.lean:177)
- These require nearest-rounding properties from `Znearest`

**Detailed Mathematical Analysis (2026-01-28)**:

The key constraint is `d ≤ prec` where `d = e_r - e_min`:

1. From Ztrunc property (`abs_Ztrunc_sub_lt_one`): `|R| < 2^d`
2. For `cexp(R * 2^e_min) ≤ e_min`, need `mag(R) ≤ prec`
3. From `|R| < 2^d` and R ≠ 0: `mag(R) ≤ d` (via `mag_le_bpow`)
4. So need: `d ≤ prec`, i.e., `e_r ≤ e_min + prec`

When does `d ≤ prec` fail?
- When `e_r = mag(x+y) - prec` and `mag(x+y) > e_min + 2*prec`
- From format bounds: `mag(x+y) ≤ prec + 1 + |ex - ey| + e_min`
- Constraint holds when: `|ex - ey| ≤ prec - 2`

For Znearest:
- The property `|error| ≤ min(|x|, |y|)` bounds the error independently of exponent difference
- This always gives `mag(error) ≤ e_min + prec`

For Ztrunc:
- The error can be as large as `ulp(x+y) = 2^e_r`
- When `|ex - ey| ≥ prec`, this exceeds `min(|x|, |y|)` and the format bound fails

**Changes Made**:
1. Enhanced the comment at the sorry location (now lines 796-824) to document:
   - The Ztrunc error bound derivation
   - The constraint `d ≤ prec` and when it fails
   - The difference between Ztrunc and Znearest behavior
2. No changes to theorem statement or function definitions
3. Build still succeeds (warnings only)

**Resolution Options**:

1. **Fix rounding infrastructure** (recommended):
   - Make `round_to_generic` mode-aware, using `Znearest` when mode = `Znearest`
   - This enables the `|error| ≤ min(|x|, |y|)` property needed for the proof

2. **Weaken theorem**:
   - Add hypothesis `|ex - ey| ≤ prec - 2` (or equivalently `d ≤ prec`)
   - This constrains operand exponents to be "close enough"

3. **Prove conditional version**:
   - Add case split on `d ≤ prec` vs `d > prec`
   - Prove the `d ≤ prec` case directly
   - The `d > prec` case requires nearest-rounding

4. **Use axiom**: Accept `plus_error_le_l/r` as axioms and proceed
