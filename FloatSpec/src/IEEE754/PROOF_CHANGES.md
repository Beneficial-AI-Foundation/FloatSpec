# IEEE754 Proof Changes Log

This file documents changes to theorems and proofs in the IEEE754 module.

## 2026-01-15: B2R_Bsign_inj theorem modification

### Original Issue
The theorem `B2R_Bsign_inj` at line 578 had a `sorry` that could not be resolved because the hypotheses were insufficient.

### Problem Analysis
The original theorem assumed that `valid_FF` (which only requires `m > 0` for finite floats) was sufficient to prove equality of two `Binary754` floats given equal `B2R` values and equal signs.

However, this is mathematically FALSE without canonical representation:
- Counterexample: `4 * 2^1 = 2 * 2^2 = 8`
- Different (mantissa, exponent) pairs can represent the same real value

### Coq Reference
In the original Coq Flocq library, `B754_finite` constructor requires a proof of `bounded m e = true`, which implies canonical representation. The Coq proof uses `canonical_bounded` and `canonical_unique`.

### Solution
Added canonical representation hypotheses to the theorem:
- `hcx`: x.val is canonical under the FLT exponent function
- `hcy`: y.val is canonical under the FLT exponent function

With these hypotheses, we can use `canonical_unique` from `Generic_fmt.lean` to complete the proof.

### Changes Made
1. Added import for `Generic_fmt` canonical definitions (already present via Compat)
2. Added helper function `FF_to_FlocqFloat` to convert `FullFloat.F754_finite` to `FlocqFloat`
3. Added canonical hypotheses to `B2R_Bsign_inj` theorem
4. Completed the proof using `canonical_unique`
