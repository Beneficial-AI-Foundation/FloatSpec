# Changes to Beqb and Beqb_correct Theorem

## Date: 2026-01-26

## Summary

Fixed the `Beqb_correct` theorem proof in `FloatSpec/src/IEEE754/PrimFloat.lean` by modifying the `Beqb` definition to align with the Coq semantics.

## Issue

The original `Beqb` definition compared structural representations via `B2SF`, checking if signs, mantissas, and exponents were equal. However, this didn't match the semantics required by `Beqb_correct`, which states:

```lean
Beqb x y = decide (B2R x = B2R y)
```

The problems were:
1. For zeros with different signs (+0 vs -0): The original `Beqb` returned `false` (different signs), but `B2R (+0) = B2R (-0) = 0`, so `decide (B2R x = B2R y) = true`.
2. For finite floats with `m = 0` (degenerate zeros): Similar issue where structural comparison didn't match real value comparison.

## Changes Made

### 1. Modified `Beqb` Definition (lines 814-831)

**Old definition:**
```lean
noncomputable def Beqb (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Bool :=
  match B2SF x, B2SF y with
  | StandardFloat.S754_zero sx, StandardFloat.S754_zero sy => decide (sx = sy)
  | StandardFloat.S754_infinity sx, StandardFloat.S754_infinity sy => decide (sx = sy)
  | StandardFloat.S754_nan, StandardFloat.S754_nan => true
  | StandardFloat.S754_finite sx mx ex, StandardFloat.S754_finite sy my ey =>
      decide (sx = sy ∧ mx = my ∧ ex = ey)
  | _, _ => false
```

**New definition:**
```lean
noncomputable def Beqb (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Bool :=
  if is_finite_B x && is_finite_B y then
    -- Both finite: check if Rcompare returns 0 (equal)
    FloatSpec.Core.Raux.Rcompare (B2R x) (B2R y) == 0
  else
    -- At least one is not finite: compare structurally
    match B2SF x, B2SF y with
    | StandardFloat.S754_infinity sx, StandardFloat.S754_infinity sy => decide (sx = sy)
    | StandardFloat.S754_nan, StandardFloat.S754_nan => true
    | _, _ => false
```

**Rationale:** The new definition uses `Rcompare` (which compares real values) for finite floats, directly matching the Coq semantics where `SFeqb` checks if `SFcompare` returns `Eq`.

### 2. Added Helper Lemma `Rcompare_eq_zero_iff` (lines 839-854)

```lean
private lemma Rcompare_eq_zero_iff (x y : ℝ) :
    FloatSpec.Core.Raux.Rcompare x y = 0 ↔ x = y
```

This lemma proves that `Rcompare x y = 0` if and only if `x = y`, which is the key property needed for the proof.

### 3. Completed `Beqb_correct_aux` Proof (lines 856-871)

The proof now works directly:
1. Unfold `Beqb` and use the finiteness hypotheses
2. Show that `(Rcompare x y == 0) = decide (x = y)` using `Bool.eq_iff_iff.mpr`
3. Apply `Rcompare_eq_zero_iff`

## Coq Reference

In Coq's Flocq library (`BinarySingleNaN.v`):
- `Beqb f1 f2 = SFeqb (B2SF f1) (B2SF f2)`
- `Bcompare_correct` shows that for finite floats, `Bcompare = Some (Rcompare (B2R f1) (B2R f2))`
- `Beqb_correct` uses this to show `Beqb = Req_bool (B2R f1) (B2R f2)`

Our Lean implementation now matches this semantic behavior.

## Verification

The file compiles successfully with no errors. The theorem `Beqb_correct` is now fully proven.

## Impact

This change may affect other theorems that depend on `Beqb`. In particular:
- `Beqb_refl` (still has sorry)
- `Bltb_correct` (still has sorry)
- `Bleb_correct` (still has sorry)

These may need similar approaches using `Rcompare`-based definitions.
