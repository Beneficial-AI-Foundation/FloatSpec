/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import FloatSpec.src.IEEE754.Binary
import FloatSpec.src.IEEE754.Bits
import Mathlib.Data.Real.Basic

/-!
# Pure-Lean IEEE-754 Binary64 Decoder

A verified decoder from `UInt64` bit patterns to `ℝ`, using FloatSpec's
`bits_to_binary` and `B2R` infrastructure. This replaces the opaque
`Float.ofBits` path used in `FPRBridge.toReal` with a pure-Lean definition
that the kernel can reason about.

## Main Definitions

- `Binary64.ofBits`: decode a `UInt64` into `Binary754 53 1023`
- `Binary64.toReal`: decode a `UInt64` into `ℝ`

## Main Results

- `Binary64.toReal_zero`: the all-zeros pattern decodes to `0`
- `Binary64.toReal_one`: the pattern `0x3FF0000000000000` decodes to `1`
- `Binary64.negated_toReal`: decoded `Bopp` negation negates the real value
-/

open FloatSpec.Core.Defs

noncomputable section

namespace Binary64

instance : Prec_gt_0 (53 : Int) := ⟨by grind⟩
instance : Prec_lt_emax (53 : Int) (1023 : Int) := ⟨by grind⟩

/-- Decode a `UInt64` bit pattern into a `Binary754 53 1023` (binary64 format). -/
def ofBits (w : UInt64) : Binary754 53 1023 :=
  bits_to_binary 53 1023 (w.toNat : Int)

/-- Decode a `UInt64` bit pattern into `ℝ` via the IEEE-754 binary64 format.
Non-finite bit patterns (infinities, NaNs) map to `0`. -/
def toReal (w : UInt64) : ℝ := B2R (ofBits w)

/-! ### Constants -/

/-- The sign bit mask for binary64: bit 63. -/
def signBitMask : UInt64 := 0x8000000000000000

/-- The bit pattern for IEEE-754 binary64 `+1.0`: biased exponent 1023, zero mantissa. -/
def oneBits : UInt64 := 0x3FF0000000000000

/-! ### Zero decoding -/

/-- The all-zeros `UInt64` decodes to the `+0` float. -/
theorem ofBits_zero_val : (ofBits 0).val = FullFloat.F754_zero false := by
  native_decide

/-- The all-zeros `UInt64` decodes to `0 : ℝ`. -/
theorem toReal_zero : toReal 0 = 0 := by
  simp [toReal, B2R, ofBits_zero_val, FF2R]

/-! ### One decoding -/

/-- The `0x3FF0000000000000` pattern decodes to a finite float with
mantissa `2^52` and exponent `-52`, representing `1.0`. -/
theorem ofBits_one_val :
    (ofBits oneBits).val =
      FullFloat.F754_finite false (2 ^ 52) (-52) := by
  native_decide

/-- The `0x3FF0000000000000` pattern decodes to `1 : ℝ`. -/
theorem toReal_one : toReal oneBits = 1 := by
  simp [toReal, B2R, ofBits_one_val, FF2R, _root_.F2R]
  norm_num

/-! ### Negation -/

/-- Flip the sign bit of a `UInt64` to negate the IEEE-754 value.

This is the executable bit operation. The proof that this raw `UInt64` XOR is
equivalent to `Bopp` on decoded binary64 values is intentionally not claimed
here; the decoder-level semantic negation lemma below uses `Bopp` directly. -/
def flipSign (w : UInt64) : UInt64 := w ^^^ signBitMask

/-- Semantic negation of a decoded binary64 value. -/
def negated (w : UInt64) : Binary754 53 1023 :=
  FF2B (prec:=53) (emax:=1023) (Bopp (ofBits w).val)

/-- Decoder-level semantic negation via FloatSpec's verified `Bopp`.

This proves the real-value negation property without asserting the still-missing
raw bit theorem relating `UInt64.xor` by `signBitMask` to `Bopp`. -/
theorem negated_toReal (w : UInt64) : B2R (negated w) = -toReal w := by
  have hopp := B2R_Bopp ((ofBits w).val) True.intro
  change FF2R 2 (Bopp (ofBits w).val) = -FF2R 2 (ofBits w).val
  exact hopp

end Binary64

end
