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
