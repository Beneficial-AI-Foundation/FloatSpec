# Code Examples from Float → ℝ Transformation

## 1. Type Signature Changes

### Before:
```lean
def Rle_bool (x y : Float) : Bool := x <= y
def Rcompare (x y : Float) : Int :=
  if x < y then -1
  else if x == y then 0
  else 1
def F2R (f : FlocqFloat beta) : Float := sorry
```

### After:
```lean
def Rle_bool (x y : ℝ) : Bool := x <= y
noncomputable def Rcompare (x y : ℝ) : Int :=
  if x < y then -1
  else if x == y then 0
  else 1
noncomputable def F2R (f : FlocqFloat beta) : ℝ := sorry
```

## 2. Absolute Value Changes

### Before:
```lean
def Rabs (x : Float) : Float := Float.abs x

theorem F2R_Zabs (m e : Int) :
  F2R (FlocqFloat.mk (Int.natAbs m) e : FlocqFloat beta) = Float.abs (F2R (FlocqFloat.mk m e : FlocqFloat beta)) := by
  sorry
```

### After:
```lean
def Rabs (x : ℝ) : ℝ := |x|

theorem F2R_Zabs (m e : Int) :
  F2R (FlocqFloat.mk (Int.natAbs m) e : FlocqFloat beta) = |F2R (FlocqFloat.mk m e : FlocqFloat beta)| := by
  sorry
```

## 3. Function Computability

### Before:
```lean
def cexp (x : Float) : Int :=
  fexp (mag beta x)

def scaled_mantissa (x : Float) : Float :=
  x * (beta : Float) ^ (-(cexp beta fexp x))
```

### After:
```lean
noncomputable def cexp (x : ℝ) : Int :=
  fexp (mag beta x)

noncomputable def scaled_mantissa (x : ℝ) : ℝ :=
  x * (beta : ℝ) ^ (-(cexp beta fexp x))
```

## 4. Import Additions

### Added to every file:
```lean
import Mathlib.Data.Real.Basic
open Real
```

### Some files also added:
```lean
import Mathlib.Data.Real.Sqrt  -- For files using square root
```

## 5. Predicate Definitions

### Before:
```lean
def Rnd_DN_pt (F : ℝ → Prop) (x f : Float) : Prop :=
  F f ∧ (f <= x)%R ∧ ∀ g : Float, F g → (g <= x)%R → (g <= f)%R
```

### After:
```lean
def Rnd_DN_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ (f <= x)%R ∧ ∀ g : ℝ, F g → (g <= x)%R → (g <= f)%R
```

## 6. Complex Type Signatures

### Before:
```lean
def round_float (rnd : ℝ → Int) (x : Float) : FlocqFloat beta :=
  let m := rnd (scaled_mantissa beta fexp x)
  let e := cexp beta fexp x
  if m == 0 then FlocqFloat.mk 0 fexp 0
  else FlocqFloat.mk m e
```

### After:
```lean
noncomputable def round_float (rnd : ℝ → Int) (x : ℝ) : FlocqFloat beta :=
  let m := rnd (scaled_mantissa beta fexp x)
  let e := cexp beta fexp x
  if m == 0 then FlocqFloat.mk 0 fexp 0
  else FlocqFloat.mk m e
```

## 7. List Operations (Pff.lean)

### Before:
```lean
def list_sum (l : List Float) : Float :=
  l.foldr (· + ·) 0

def list_prod (l : List Float) : Float :=
  l.foldr (· * ·) 1
```

### After:
```lean
def list_sum (l : List Float) : ℝ :=
  l.foldr (· + ·) 0

def list_prod (l : List Float) : ℝ :=
  l.foldr (· * ·) 1
```

## 8. Error Bound Definitions

### Before:
```lean
def pff_error_bound (prec : Int) : Float :=
  (2 : Float)^(-prec)
```

### After:
```lean
def pff_error_bound (prec : Int) : ℝ :=
  (2 : ℝ)^(-prec)
```