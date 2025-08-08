-- Error of the multiplication is in the FLX/FLT format
-- Translated from Coq file: flocq/src/Prop/Mult_error.v

import FloatSpec.src.Core
import FloatSpec.src.Prop.Plus_error

variable (beta : Int)
variable (prec : Int)
variable [Prec_gt_0 prec]

-- Section: FLX multiplication error

variable (rnd : Float → Int)
variable [Valid_rnd rnd]

/-- Auxiliary result that provides the exponent for FLX multiplication error -/
lemma mult_error_FLX_aux (x y : Float)
  (hx : generic_format beta (FLX_exp prec) x) (hy : generic_format beta (FLX_exp prec) y)
  (h_nonzero : round beta (FLX_exp prec) rnd (x * y) - (x * y) ≠ 0) :
  ∃ f : FlocqFloat beta, F2R f = round beta (FLX_exp prec) rnd (x * y) - (x * y) ∧
    cexp beta (FLX_exp prec) (F2R f) ≤ f.Fexp ∧
    f.Fexp = cexp beta (FLX_exp prec) x + cexp beta (FLX_exp prec) y := by
  sorry

/-- Error of the multiplication in FLX -/
theorem mult_error_FLX (x y : Float)
  (hx : generic_format beta (FLX_exp prec) x) (hy : generic_format beta (FLX_exp prec) y) :
  generic_format beta (FLX_exp prec) (round beta (FLX_exp prec) rnd (x * y) - (x * y)) := by
  sorry

/-- Multiplication by power of beta is exact in FLX -/
lemma mult_bpow_exact_FLX (x : Float) (e : Int)
  (hx : generic_format beta (FLX_exp prec) x) :
  generic_format beta (FLX_exp prec) (x * (Int.natAbs beta : Float) ^ (Int.natAbs e : Nat)) := by
  sorry

-- Section: FLT multiplication error

variable (emin : Int)

/-- Error of the multiplication in FLT with underflow requirements -/
theorem mult_error_FLT (x y : Float)
  (hx : generic_format beta (FLT_exp emin prec) x) (hy : generic_format beta (FLT_exp emin prec) y)
  (h_underflow : x * y ≠ 0 → 
    (Int.natAbs beta : Float) ^ (Int.natAbs (emin + 2 * prec - 1) : Nat) ≤ Float.abs (x * y)) :
  generic_format beta (FLT_exp emin prec) (round beta (FLT_exp emin prec) rnd (x * y) - (x * y)) := by
  sorry

/-- F2R greater than or equal to power bound -/
lemma F2R_ge (f : FlocqFloat beta) (h_nonzero : F2R f ≠ 0) :
  (Int.natAbs beta : Float) ^ (Int.natAbs f.Fexp : Nat) ≤ Float.abs (F2R f) := by
  sorry

/-- FLT multiplication error greater than or equal to power bound -/
theorem mult_error_FLT_ge_bpow (x y : Float) (e : Int)
  (hx : generic_format beta (FLT_exp emin prec) x) (hy : generic_format beta (FLT_exp emin prec) y)
  (h_bound : (Int.natAbs beta : Float) ^ (Int.natAbs (e + 2 * prec - 1) : Nat) ≤ Float.abs (x * y))
  (h_nonzero : round beta (FLT_exp emin prec) rnd (x * y) - (x * y) ≠ 0) :
  (Int.natAbs beta : Float) ^ (Int.natAbs e : Nat) ≤ 
    Float.abs (round beta (FLT_exp emin prec) rnd (x * y) - (x * y)) := by
  sorry

/-- Multiplication by power of beta is exact in FLT -/
lemma mult_bpow_exact_FLT (x : Float) (e : Int)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (h_bound : emin + prec - mag beta x ≤ e) :
  generic_format beta (FLT_exp emin prec) (x * (Int.natAbs beta : Float) ^ (Int.natAbs e : Nat)) := by
  sorry

/-- Multiplication by positive power of beta is exact in FLT -/
lemma mult_bpow_pos_exact_FLT (x : Float) (e : Int)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (h_nonneg : 0 ≤ e) :
  generic_format beta (FLT_exp emin prec) (x * (Int.natAbs beta : Float) ^ (Int.natAbs e : Nat)) := by
  sorry