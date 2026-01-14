-- IEEE-754 encoding of binary floating-point data
-- Translated from Coq file: flocq/src/IEEE754/Bits.v

import FloatSpec.src.Core
import Std.Do.Triple
import Std.Tactic.Do
import FloatSpec.src.IEEE754.Binary
import Mathlib.Data.Real.Basic

open Real
open Std.Do

-- Number of bits for the fraction and exponent
variable (mw ew : Nat)

-- Join bits into IEEE 754 bit representation
def join_bits (mw ew : Nat) (s : Bool) (m e : Int) : Int :=
  let two : Int := 2
  let sign_bit := if s then two ^ ew else 0
  (sign_bit + e) * (two ^ mw) + m

-- Join bits range theorem
theorem join_bits_range (s : Bool) (m e : Int)
  (hm : 0 ≤ m ∧ m < ((2 : Int) ^ mw)) (he : 0 ≤ e ∧ e < ((2 : Int) ^ ew)) :
  0 ≤ join_bits mw ew s m e ∧ join_bits mw ew s m e < (2 : Int) ^ (mw + ew + 1) := by
  classical
  set mm : Int := (2 : Int) ^ mw with hmm
  set em : Int := (2 : Int) ^ ew with hem

  have h2 : (0 : Int) < 2 := by decide
  have hmm_pos : 0 < mm := by
    simpa [hmm] using (pow_pos h2 mw)
  have hem_pos : 0 < em := by
    simpa [hem] using (pow_pos h2 ew)
  have hmm_nonneg : 0 ≤ mm := le_of_lt hmm_pos
  have hem_nonneg : 0 ≤ em := le_of_lt hem_pos
  have hm_lt : m < mm := by simpa [hmm] using hm.2
  have he_lt : e < em := by simpa [hem] using he.2

  have hsign_nonneg : 0 ≤ (if s then em else 0) := by
    cases s <;> simp [hem_nonneg]
  have ht_nonneg : 0 ≤ (if s then em else 0) + e :=
    add_nonneg hsign_nonneg he.1

  have hnonneg : 0 ≤ join_bits mw ew s m e := by
    have hmul : 0 ≤ ((if s then em else 0) + e) * mm :=
      mul_nonneg ht_nonneg hmm_nonneg
    simpa [join_bits, hmm.symm, hem.symm, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
      mul_left_comm] using add_nonneg hmul hm.1

  have hem_le_twoem : em ≤ 2 * em := by
    simpa [two_mul, add_assoc, add_comm, add_left_comm] using
      (le_add_of_nonneg_right hem_nonneg : em ≤ em + em)
  have ht_lt : (if s then em else 0) + e < 2 * em := by
    cases s with
    | false =>
        simpa using (lt_of_lt_of_le he_lt hem_le_twoem)
    | true =>
        -- Note: `add_lt_add_left`/`add_lt_add_right` are easy to mix up; keep this
        -- version robust by rewriting via commutativity.
        have h : e + em < em + em := add_lt_add_left he_lt em
        have : em + e < em + em := by simpa [add_comm] using h
        simpa [two_mul, add_assoc, add_comm, add_left_comm] using this

  let t : Int := (if s then em else 0) + e
  have hstep1 : join_bits mw ew s m e < t * mm + mm := by
    have h := add_lt_add_left hm_lt (t * mm)
    simpa [join_bits, t, hmm.symm, hem.symm, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
      mul_left_comm] using h
  have ht_mul_eq : t * mm + mm = (t + 1) * mm := by
    have : (t + 1) * mm = t * mm + mm := by
      simpa [one_mul] using (Int.add_mul t (1 : Int) mm)
    exact this.symm
  have hstep2 : join_bits mw ew s m e < (t + 1) * mm := by
    simpa [ht_mul_eq] using hstep1

  have ht1_le : t + 1 ≤ 2 * em := Int.add_one_le_of_lt (by simpa [t] using ht_lt)
  have hle : (t + 1) * mm ≤ (2 * em) * mm :=
    mul_le_mul_of_nonneg_right ht1_le hmm_nonneg
  have hlt_twoem : join_bits mw ew s m e < (2 * em) * mm :=
    lt_of_lt_of_le hstep2 hle

  have htwoem : 2 * em = (2 : Int) ^ (ew + 1) := by
    have hsucc : (2 : Int) ^ (ew + 1) = (2 : Int) ^ ew * 2 := by
      simpa using (pow_succ (2 : Int) ew)
    calc
      2 * em = em * 2 := by simp [mul_comm]
      _ = (2 : Int) ^ ew * 2 := by simp [hem.symm]
      _ = (2 : Int) ^ (ew + 1) := by simpa using hsucc.symm

  have hpow : (2 * em) * mm = (2 : Int) ^ (mw + ew + 1) := by
    have hpow_add :
        (2 : Int) ^ (mw + ew + 1) = mm * (2 : Int) ^ (ew + 1) := by
      simpa [Nat.add_assoc, hmm.symm] using (pow_add (2 : Int) mw (ew + 1))
    calc
      (2 * em) * mm = ((2 : Int) ^ (ew + 1)) * mm := by simp [htwoem]
      _ = mm * (2 : Int) ^ (ew + 1) := by simp [mul_comm, mul_left_comm, mul_assoc]
      _ = (2 : Int) ^ (mw + ew + 1) := by
        simpa using hpow_add.symm

  refine ⟨hnonneg, ?_⟩
  simpa [hpow] using hlt_twoem

-- Split bits from IEEE 754 bit representation
def split_bits (mw ew : Nat) (x : Int) : Bool × Int × Int :=
  let two : Int := 2
  let mm := two ^ mw
  let em := two ^ ew
  (mm * em ≤ x, x % mm, (x / mm) % em)

-- Split-join consistency
theorem split_join_bits (s : Bool) (m e : Int)
  (hm : 0 ≤ m ∧ m < ((2 : Int) ^ mw)) (he : 0 ≤ e ∧ e < ((2 : Int) ^ ew)) :
  split_bits mw ew (join_bits mw ew s m e) = (s, m, e) := by
  classical
  set mm : Int := (2 : Int) ^ mw with hmm
  set em : Int := (2 : Int) ^ ew with hem
  have h2 : (0 : Int) < 2 := by decide
  have hmm_pos : 0 < mm := by
    simpa [hmm] using (pow_pos h2 mw)
  have hem_pos : 0 < em := by
    simpa [hem] using (pow_pos h2 ew)
  have hmm_nonneg : 0 ≤ mm := le_of_lt hmm_pos
  have hem_nonneg : 0 ≤ em := le_of_lt hem_pos
  have hmm_ne : mm ≠ 0 := ne_of_gt hmm_pos

  -- Unfold and simplify to the arithmetic statement on components.
  -- (The first component is a `Bool`; the Prop is coerced via `decide`.)
  ext <;> simp [split_bits, join_bits, hmm.symm, hem.symm]
  · -- sign bit
    cases s
    · -- s = false
      have hx_lt : e * mm + m < mm * em := by
        have he_lt : e < em := by simpa [hem] using he.2
        have hm_lt : m < mm := by simpa [hmm] using hm.2
        have hmul_lt : e * mm < em * mm := by
          exact mul_lt_mul_of_pos_right he_lt hmm_pos
        have h1 : e * mm + m < e * mm + mm := add_lt_add_right hm_lt (e * mm)
        have h2' : e * mm + mm ≤ em * mm := by
          have : e + 1 ≤ em := Int.add_one_le_of_lt he_lt
          have : (e + 1) * mm ≤ em * mm := mul_le_mul_of_nonneg_right this hmm_nonneg
          simpa [Int.add_mul, one_mul, add_assoc, add_left_comm, add_comm] using this
        have h3 : e * mm + m < em * mm := lt_of_lt_of_le h1 h2'
        simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using h3
      simpa [mul_comm, mul_left_comm, mul_assoc] using hx_lt
    · -- s = true
      have hx_le : mm * em ≤ (em + e) * mm + m := by
        have hem_le : em ≤ em + e := le_add_of_nonneg_right he.1
        have hmul : em * mm ≤ (em + e) * mm := mul_le_mul_of_nonneg_right hem_le hmm_nonneg
        have : em * mm ≤ (em + e) * mm + m := le_trans hmul (le_add_of_nonneg_right hm.1)
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      simpa [mul_comm, mul_left_comm, mul_assoc] using hx_le
  · -- mantissa
    have hm_lt : m < mm := by simpa [hmm] using hm.2
    have hm_emod : m % mm = m := Int.emod_eq_of_lt hm.1 hm_lt
    -- Normalize to `m + mm * k` so we can use `add_mul_emod_self_left`.
    simpa [Int.add_mul_emod_self_left, hm_emod, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc]
  · -- exponent
    have hm_lt : m < mm := by simpa [hmm] using hm.2
    have hm_div : m / mm = 0 := Int.ediv_eq_zero_of_lt hm.1 hm_lt
    have he_lt : e < em := by simpa [hem] using he.2
    have he_emod : e % em = e := Int.emod_eq_of_lt he.1 he_lt
    -- Compute the quotient by `mm` and then mod by `em`.
    -- For `s = true`, the quotient is `em + e` and `(em + e) % em = e`.
    -- For `s = false`, the quotient is `e` and `e % em = e`.
    cases s
    · -- s = false
      -- (m + e * mm) / mm = m/mm + e
      have hquot : (m + e * mm) / mm = e := by
        have := Int.add_mul_ediv_right (a := m) (b := e) (c := mm) hmm_ne
        simpa [hm_div, add_comm, add_left_comm, add_assoc] using this
      have hquot' : (e * mm + m) / mm = e := by
        simpa [add_comm, add_left_comm, add_assoc] using hquot
      simpa [hquot', he_emod]
    · -- s = true
      have hquot : ((em + e) * mm + m) / mm = em + e := by
        have h := Int.add_mul_ediv_right (a := m) (b := em + e) (c := mm) hmm_ne
        have h' : (m + (em + e) * mm) / mm = em + e := by
          simpa [hm_div, add_assoc] using h
        simpa [add_comm, add_left_comm, add_assoc] using h'
      have hmod : (em + e) % em = e := by
        have hshift : (e + em * 1) % em = e % em := by
          simpa using (Int.add_mul_emod_self_left (a := e) (b := em) (c := 1))
        have : (e + em) % em = e := by
          simpa [mul_one, add_assoc, he_emod] using hshift
        simpa [add_comm] using this
      simpa [hquot, hmod]

-- Join-split consistency
theorem join_split_bits (x : Int) (hx : 0 ≤ x ∧ x < (2 : Int) ^ (mw + ew + 1)) :
  let (s, m, e) := split_bits mw ew x
  join_bits mw ew s m e = x := by
  classical
  set mm : Int := (2 : Int) ^ mw with hmm
  set em : Int := (2 : Int) ^ ew with hem
  have h2 : (0 : Int) < 2 := by decide
  have hmm_pos : 0 < mm := by simpa [hmm] using (pow_pos h2 mw)
  have hmm_nonneg : 0 ≤ mm := le_of_lt hmm_pos
  have hmm_ne : mm ≠ 0 := ne_of_gt hmm_pos

  -- Reduce the `let` and fold powers into `mm`/`em`.
  simp [split_bits, join_bits, hmm.symm, hem.symm]

  -- Work with the quotient `q = x / mm`.
  set q : Int := x / mm with hq
  have hq_nonneg : 0 ≤ q := by
    simpa [hq] using (Int.ediv_nonneg hx.1 hmm_nonneg)

  -- Bound: `q < 2 * em`, derived from the global range on `x`.
  have hx_lt_mul : x < mm * ((2 : Int) ^ (ew + 1)) := by
    have hpow_eq :
        (2 : Int) ^ (mw + ew + 1) = mm * (2 : Int) ^ (ew + 1) := by
      -- 2^(mw + (ew+1)) = 2^mw * 2^(ew+1)
      simpa [Nat.add_assoc, hmm.symm] using (pow_add (2 : Int) mw (ew + 1))
    simpa [hpow_eq] using hx.2

  have hq_lt_pow : q < (2 : Int) ^ (ew + 1) := by
    have hx_lt_mul' : x < ((2 : Int) ^ (ew + 1)) * mm := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hx_lt_mul
    have :=
        Int.ediv_lt_of_lt_mul (a := x) (b := (2 : Int) ^ (ew + 1)) (c := mm) hmm_pos hx_lt_mul'
    simpa [hq] using this

  have hq_lt_twoem : q < 2 * em := by
    have hpow_succ : (2 : Int) ^ (ew + 1) = em * 2 := by
      simpa [hem.symm] using (pow_succ (2 : Int) ew)
    have : q < em * 2 := by simpa [hpow_succ] using hq_lt_pow
    simpa [mul_comm, mul_left_comm, mul_assoc] using this

  -- Now split by the sign bit.
  by_cases hsign : mm * em ≤ x
  · have hq_ge : em ≤ q := by
      have hsign' : em * mm ≤ x := by simpa [mul_comm, mul_left_comm, mul_assoc] using hsign
      have := Int.le_ediv_of_mul_le (a := em) (b := x) (c := mm) hmm_pos hsign'
      simpa [hq] using this
    have hq_lt' : q < em + em := by
      -- q < 2*em and 2*em = em+em
      simpa [two_mul, add_comm, add_left_comm, add_assoc] using hq_lt_twoem
    have hr_nonneg : 0 ≤ q - em := sub_nonneg.mpr hq_ge
    have hr_lt : q - em < em := (sub_lt_iff_lt_add).2 hq_lt'
    have hq_mod : q % em = q - em := by
      have hq_eq : q = (q - em) + em := by
        simpa [add_comm, add_left_comm, add_assoc] using (sub_add_cancel q em).symm
      have hshift : ((q - em) + em) % em = (q - em) % em := by
        simpa [mul_one, add_assoc] using (Int.add_mul_emod_self_left (a := q - em) (b := em) (c := 1))
      have hq_mod' : q % em = (q - em) % em := by
        simpa [hq_eq.symm] using hshift
      have hrem : (q - em) % em = q - em := Int.emod_eq_of_lt hr_nonneg hr_lt
      exact hq_mod'.trans hrem
    have hsum : em + q % em = q := by
      calc
        em + q % em = em + (q - em) := by simp [hq_mod]
        _ = (q - em) + em := by simp [add_comm, add_left_comm, add_assoc]
        _ = q := by simpa using (sub_add_cancel q em)
    have hexp : em + x / mm % em = x / mm := by
      simpa [hq] using hsum
    calc
      ((if mm * em ≤ x then em else 0) + x / mm % em) * mm + x % mm
          = (em + x / mm % em) * mm + x % mm := by simp [hsign]
      _ = (x / mm) * mm + x % mm := by simp [hexp]
      _ = mm * (x / mm) + x % mm := by simp [mul_comm, mul_left_comm, mul_assoc]
      _ = x := by simpa using (Int.ediv_add_emod x mm)
  · have hx_lt : x < em * mm := by
      have : x < mm * em := lt_of_not_ge hsign
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hq_lt_em : q < em := by
      have := Int.ediv_lt_of_lt_mul (a := x) (b := em) (c := mm) hmm_pos hx_lt
      simpa [hq] using this
    have hq_mod : q % em = q := Int.emod_eq_of_lt hq_nonneg hq_lt_em
    have hexp : x / mm % em = x / mm := by
      simpa [hq, hq_mod]
    calc
      ((if mm * em ≤ x then em else 0) + x / mm % em) * mm + x % mm
          = (0 + x / mm % em) * mm + x % mm := by simp [hsign]
      _ = (x / mm) * mm + x % mm := by simp [hexp]
      _ = mm * (x / mm) + x % mm := by simp [mul_comm, mul_left_comm, mul_assoc]
      _ = x := by simpa using (Int.ediv_add_emod x mm)

-- IEEE 754 bit-level operations
section IEEE754_Bits

variable (prec emax : Int)
variable [Prec_gt_0 prec]
variable [Prec_lt_emax prec emax]

-- Mantissa width (including implicit bit)
def mant_width (prec : Int) : Nat := Int.toNat (prec - 1)

-- Exponent width
def exp_width (emax : Int) : Nat :=
  -- IEEE formats in this project use `emax` as the exponent bias (e.g. 127, 1023).
  -- The number of exponent bits is therefore `log2 (emax + 1) + 1`,
  -- which we compute via the base-2 digit count.
  Int.toNat (FloatSpec.Core.Digits.Zdigits (beta := 2) (emax + 1))

-- Convert Binary754 to bit representation
def binary_to_bits (x : Binary754 prec emax) : Int :=
  let mw := mant_width prec
  let ew := exp_width emax
  let mm : Int := (2 : Int) ^ mw
  let em : Int := (2 : Int) ^ ew
  let expMax : Int := em - 1
  let subExp : Int := (1 - emax) - (mw : Int)
  match x.val with
  | FullFloat.F754_zero s =>
      join_bits mw ew s 0 0
  | FullFloat.F754_infinity s =>
      join_bits mw ew s 0 expMax
  | FullFloat.F754_nan s payload =>
      let payload : Int := (payload : Int) % mm
      let payload : Int := if payload = 0 then (if 1 < mm then 1 else 0) else payload
      join_bits mw ew s payload expMax
  | FullFloat.F754_finite s m e =>
      let m : Int := (m : Int)
      if hzero : m = 0 then
        join_bits mw ew s 0 0
      else
        -- Canonical IEEE encoding (normal/subnormal) when the input matches the
        -- representable shape; otherwise fall back to a NaN payload.
        if hsub : (e = subExp ∧ m < mm) then
          join_bits mw ew s m 0
        else
          let E : Int := e + (mw : Int) + emax
          if hnorm : (1 ≤ E ∧ E < expMax ∧ mm ≤ m ∧ m < 2 * mm) then
            join_bits mw ew s (m - mm) E
          else
            let nanPayload : Int := if 1 < mm then 1 else 0
            join_bits mw ew s nanPayload expMax

-- Convert bit representation to Binary754
def bits_to_binary (bits : Int) : Binary754 prec emax :=
  let mw := mant_width prec
  let ew := exp_width emax
  let modulus : Int := (2 : Int) ^ (mw + ew + 1)
  let bits : Int := bits % modulus
  let mm : Int := (2 : Int) ^ mw
  let em : Int := (2 : Int) ^ ew
  let expMax : Int := em - 1
  let (s, mField, eField) := split_bits mw ew bits
  if hAllOnes : eField = expMax then
    if hM0 : mField = 0 then
      FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_infinity s)
    else
      FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_nan s (Int.toNat mField))
  else if hE0 : eField = 0 then
    if hM0 : mField = 0 then
      FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_zero s)
    else
      FF2B (prec:=prec) (emax:=emax)
        (FullFloat.F754_finite s (Int.toNat mField) ((1 - emax) - (mw : Int)))
  else
    FF2B (prec:=prec) (emax:=emax)
      (FullFloat.F754_finite s (Int.toNat (mm + mField)) ((eField - emax) - (mw : Int)))

theorem bits_binary_roundtrip (bits : Int) 
  (h_valid : 0 ≤ bits ∧ bits < (2 : Int) ^ (mant_width prec + exp_width emax + 1)) :
  binary_to_bits prec emax (bits_to_binary prec emax bits) = bits := by
  classical
  set mw : Nat := mant_width prec with hmw
  set ew : Nat := exp_width emax with hew
  set mm : Int := (2 : Int) ^ mw with hmm
  set em : Int := (2 : Int) ^ ew with hem
  set expMax : Int := em - 1 with hexpMax

  -- The decoder normalizes via `% modulus`, which is identity on the valid range.
  have hmod : bits % (2 : Int) ^ (mw + ew + 1) = bits := by
    exact Int.emod_eq_of_lt h_valid.1 (by simpa [hmw.symm, hew.symm] using h_valid.2)

  -- Split fields for `bits`.
  rcases hsplit : split_bits mw ew bits with ⟨s, mField, eField⟩

  have hmField_eq : mField = bits % mm := by
    have := congrArg (fun t => t.2.1) hsplit
    -- `split_bits`'s second component is `bits % mm`.
    simpa [split_bits, hmm] using this.symm

  have heField_eq : eField = (bits / mm) % em := by
    have := congrArg (fun t => t.2.2) hsplit
    simpa [split_bits, hmm, hem] using this.symm

  have hmField_ge0 : 0 ≤ mField := by
    -- modulo is always non-negative
    have h2 : (0 : Int) < 2 := by decide
    have hmm_pos : 0 < mm := by simpa [hmm] using (pow_pos h2 mw)
    simpa [hmField_eq] using (Int.emod_nonneg bits (ne_of_gt hmm_pos))

  have hmField_lt_mm : mField < mm := by
    have h2 : (0 : Int) < 2 := by decide
    have hmm_pos : 0 < mm := by simpa [hmm] using (pow_pos h2 mw)
    simpa [hmField_eq] using (Int.emod_lt_of_pos bits hmm_pos)

  have heField_ge0 : 0 ≤ eField := by
    have h2 : (0 : Int) < 2 := by decide
    have hem_pos : 0 < em := by simpa [hem] using (pow_pos h2 ew)
    -- eField is a modulo, hence non-negative
    simpa [heField_eq] using
      (Int.emod_nonneg (bits / mm) (ne_of_gt hem_pos))

  have heField_lt_em : eField < em := by
    have h2 : (0 : Int) < 2 := by decide
    have hem_pos : 0 < em := by simpa [hem] using (pow_pos h2 ew)
    simpa [heField_eq] using
      (Int.emod_lt_of_pos (bits / mm) hem_pos)

  -- Reconstructing `bits` from its fields.
  have hjoin :
      join_bits mw ew s mField eField = bits := by
    have := join_split_bits (mw:=mw) (ew:=ew) (x:=bits) (by simpa [hmw.symm, hew.symm] using h_valid)
    simpa [hsplit] using this

  -- Now compute encoder(decoder(bits)) by cases on `eField` and `mField`.
  by_cases hAllOnes : eField = expMax
  · -- exponent all ones (Inf/NaN)
    by_cases hM0 : mField = 0
    · -- infinity
      have : binary_to_bits prec emax (bits_to_binary prec emax bits) =
          join_bits mw ew s mField eField := by
        simp [bits_to_binary, binary_to_bits, FF2B, hmw.symm, hew.symm, hmod, hmm, hem, hexpMax,
          hsplit, hAllOnes, hM0]
      exact this.trans hjoin
    · -- NaN
      have hmcast : (Int.toNat mField : Int) = mField := by
        simpa [Int.toNat_of_nonneg hmField_ge0]
      have hPayload : (Int.toNat mField : Int) % mm = mField := by
        -- cast-back is identity since `mField ≥ 0`, and the modulo is small since `mField < mm`.
        have hsmall : mField % mm = mField := Int.emod_eq_of_lt hmField_ge0 hmField_lt_mm
        have hsmall' : (Int.toNat mField : Int) % mm = (Int.toNat mField : Int) := by
          -- Rewrite `mField` into `↑mField.toNat` in `hsmall`.
          have := hsmall
          -- `rw` avoids `simp` recursion issues here.
          rw [hmcast.symm] at this
          exact this
        -- Rewrite back to `mField`.
        simpa [hmcast] using hsmall'
      have : binary_to_bits prec emax (bits_to_binary prec emax bits) =
          join_bits mw ew s mField eField := by
        -- In the NaN branch, the encoder's payload normalization is a no-op since `mField ≠ 0` and `mField < mm`.
        have hm_mod2 : mField % (2 : Int) ^ mw = mField := by
          simpa [hmm] using (Int.emod_eq_of_lt hmField_ge0 hmField_lt_mm)
        have hnotdiv2 : ¬ ((2 : Int) ^ mw ∣ mField) := by
          intro hd
          have hzero : mField % (2 : Int) ^ mw = 0 := (Int.dvd_iff_emod_eq_zero).1 hd
          have : mField = 0 := by simpa [hm_mod2] using hzero
          exact hM0 this
        simp [bits_to_binary, binary_to_bits, FF2B, hmw.symm, hew.symm, hmod, hmm, hem, hexpMax,
          hsplit, hAllOnes, hM0, hmcast, hPayload, hm_mod2, hnotdiv2]
      exact this.trans hjoin
  · -- exponent not all ones
    by_cases hE0 : eField = 0
    · -- exponent zero (zero/subnormal)
      by_cases hM0 : mField = 0
      · -- zero
        have : binary_to_bits prec emax (bits_to_binary prec emax bits) =
            join_bits mw ew s mField eField := by
          have h0ne : (0 : Int) ≠ (2 : Int) ^ ew - 1 := by
            intro h0
            apply hAllOnes
            have hex : expMax = (2 : Int) ^ ew - 1 := by
              -- `expMax = em - 1` and `em = 2^ew`
              simpa [hexpMax, hem]
            have hExpMax0 : expMax = 0 := by
              have : (2 : Int) ^ ew - 1 = 0 := by simpa [eq_comm] using h0
              simpa [hex] using this
            -- `eField = 0` in this branch, so `eField = expMax`.
            simpa [hE0, hExpMax0]
          simp [bits_to_binary, binary_to_bits, FF2B, hmw.symm, hew.symm, hmod, hmm, hem, hexpMax,
            hsplit, hAllOnes, hE0, hM0, h0ne]
        exact this.trans hjoin
      · -- subnormal
        have hmcast : (Int.toNat mField : Int) = mField := by
          simpa [Int.toNat_of_nonneg hmField_ge0]
        have hsub : ((1 - emax) - (mw : Int) = (1 - emax) - (mw : Int) ∧ mField < mm) := by
          exact ⟨rfl, by simpa [hmm] using hmField_lt_mm⟩
        have : binary_to_bits prec emax (bits_to_binary prec emax bits) =
            join_bits mw ew s mField eField := by
          -- The encoder detects the subnormal shape via exponent `subExp` and `mField < mm`.
          have h0ne : (0 : Int) ≠ expMax := by
            intro h0
            apply hAllOnes
            calc
              eField = 0 := hE0
              _ = expMax := h0
          simp [bits_to_binary, binary_to_bits, FF2B, hmw.symm, hew.symm, hmod,
            hmm.symm, hem.symm, hexpMax.symm, hsplit, hAllOnes, hE0, hM0, hmcast, hsub, h0ne]
        exact this.trans hjoin
    · -- normal
      have hePos : 1 ≤ eField := by
        -- `eField ≠ 0` and `0 ≤ eField`
        have he : 0 < eField := lt_of_le_of_ne' heField_ge0 (by simpa [eq_comm] using hE0)
        -- turn `0 < eField` into `1 ≤ eField`
        simpa using (Int.add_one_le_of_lt he)
      have heLtExpMax : eField < expMax := by
        have heLe : eField ≤ expMax := by
          -- eField < em implies eField ≤ em-1 = expMax
          have : eField ≤ em - 1 := Int.le_sub_one_of_lt heField_lt_em
          simpa [hexpMax] using this
        exact lt_of_le_of_ne' heLe (by simpa [eq_comm] using hAllOnes)
      have hmNormal : mm ≤ mm + mField := le_add_of_nonneg_right hmField_ge0
      have hmNormalLt : mm + mField < 2 * mm := by
        -- since mField < mm
        have h := add_lt_add_left hmField_lt_mm mm
        simpa [two_mul, add_assoc, add_comm, add_left_comm] using h
      have hnorm :
          (1 ≤ eField ∧ eField < expMax ∧ mm ≤ mm + mField ∧ mm + mField < 2 * mm) := by
        exact ⟨hePos, heLtExpMax, hmNormal, hmNormalLt⟩
      have hmcast : (Int.toNat (mm + mField) : Int) = mm + mField := by
        -- non-negativity is obvious
        have hnonneg : 0 ≤ mm + mField := add_nonneg (by
          have h2 : (0 : Int) < 2 := by decide
          have hmm_pos : 0 < mm := by simpa [hmm] using (pow_pos h2 mw)
          exact le_of_lt hmm_pos) hmField_ge0
        simpa [Int.toNat_of_nonneg hnonneg]
      have : binary_to_bits prec emax (bits_to_binary prec emax bits) =
          join_bits mw ew s mField eField := by
        simp [bits_to_binary, binary_to_bits, FF2B, hmw.symm, hew.symm, hmod,
          hmm.symm, hem.symm, hexpMax.symm, hsplit, hAllOnes, hE0, hmField_ge0, hmField_lt_mm, hmcast, hnorm]
        have h2 : (0 : Int) < 2 := by decide
        have hmm_pos : 0 < mm := by simpa [hmm] using (pow_pos h2 mw)
        have hmsum_ne : mm + mField ≠ 0 := by
          have hge : mm ≤ mm + mField := le_add_of_nonneg_right hmField_ge0
          have hpos : 0 < mm + mField := lt_of_lt_of_le hmm_pos hge
          exact ne_of_gt hpos
        have hmField_not_lt0 : ¬ mField < 0 := not_lt_of_ge hmField_ge0
        simp [hmsum_ne, hmField_not_lt0]
      exact this.trans hjoin

-- Round-trip property for bit operations (decoder range)
theorem binary_bits_roundtrip (bits : Int) :
  bits_to_binary prec emax (binary_to_bits prec emax (bits_to_binary prec emax bits)) =
    bits_to_binary prec emax bits := by
  classical
  set mw : Nat := mant_width prec with hmw
  set ew : Nat := exp_width emax with hew
  set modulus : Int := (2 : Int) ^ (mw + ew + 1) with hmodulus
  set b : Int := bits % modulus with hb
  have hb_range : 0 ≤ b ∧ b < modulus := by
    have h2 : (0 : Int) < 2 := by decide
    have hpos : 0 < modulus := by simpa [hmodulus] using (pow_pos h2 (mw + ew + 1))
    refine ⟨Int.emod_nonneg bits (ne_of_gt hpos), Int.emod_lt_of_pos bits hpos⟩

  have hb_bits : binary_to_bits prec emax (bits_to_binary prec emax b) = b := by
    simpa [hmw, hew, hmodulus] using
      (bits_binary_roundtrip (prec:=prec) (emax:=emax) b (by simpa [hmw, hew, hmodulus] using hb_range))

  -- `bits_to_binary` only depends on the normalized bits.
  have hdecode_eq : bits_to_binary prec emax bits = bits_to_binary prec emax b := by
    simp [bits_to_binary, hmw, hew, hmodulus, hb]

  calc
    bits_to_binary prec emax (binary_to_bits prec emax (bits_to_binary prec emax bits))
        = bits_to_binary prec emax (binary_to_bits prec emax (bits_to_binary prec emax b)) := by
            simpa [hdecode_eq]
    _ = bits_to_binary prec emax b := by
          simpa [hb_bits]
    _ = bits_to_binary prec emax bits := by
          simpa [hdecode_eq]

-- Auxillary constructor used in Coq: binary_float_of_bits_aux
-- We expose it here as a pure computation wrapped in Id to
-- mirror the hoare-triple specification pattern used across the project.
def binary_float_of_bits_aux (bits : Int) : (Binary754 prec emax) :=
  (bits_to_binary prec emax bits)

-- Coq lemma: binary_float_of_bits_aux_correct
-- We state it in hoare-triple style around the pure computation above.
theorem binary_float_of_bits_aux_correct (bits : Int) :
  ⦃⌜True⌝⦄
  (pure (binary_float_of_bits_aux (prec:=prec) (emax:=emax) bits) : Id (Binary754 prec emax))
  ⦃⇓result => ⌜result = bits_to_binary prec emax bits⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold binary_float_of_bits_aux
  rfl

-- Extract components from bits
def extract_sign (prec emax : Int) (bits : Int) : Bool :=
  let mw := mant_width prec
  let ew := exp_width emax
  let mm : Int := (2 : Int) ^ mw
  let em : Int := (2 : Int) ^ ew
  mm * em ≤ bits

def extract_exponent (prec emax : Int) (bits : Int) : Int :=
  (bits / ((2 : Int) ^ (mant_width prec))) % ((2 : Int) ^ (exp_width emax))

def extract_mantissa (prec : Int) (bits : Int) : Int :=
  bits % ((2 : Int) ^ (mant_width prec))

-- IEEE 754 special values in bit representation
def zero_bits (prec emax : Int) (sign : Bool) : Int :=
  join_bits (mant_width prec) (exp_width emax) sign 0 0

def infinity_bits (prec emax : Int) (sign : Bool) : Int :=
  join_bits (mant_width prec) (exp_width emax) sign 0 (((2 : Int) ^ (exp_width emax)) - 1)

def nan_bits (prec emax : Int) (sign : Bool) (payload : Int) : Int :=
  join_bits (mant_width prec) (exp_width emax) sign payload (((2 : Int) ^ (exp_width emax)) - 1)

-- Check for special values
def is_zero_bits (prec emax : Int) (bits : Int) : Bool :=
  extract_exponent prec emax bits = 0 ∧ extract_mantissa prec bits = 0

def is_infinity_bits (prec emax : Int) (bits : Int) : Bool :=
  extract_exponent prec emax bits = ((2 : Int) ^ (exp_width emax)) - 1 ∧ 
  extract_mantissa prec bits = 0

def is_nan_bits (prec emax : Int) (bits : Int) : Bool :=
  extract_exponent prec emax bits = ((2 : Int) ^ (exp_width emax)) - 1 ∧ 
  extract_mantissa prec bits ≠ 0

end IEEE754_Bits

-- Split bits of binary float correctness
theorem split_bits_of_binary_float_correct
  {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) :
  split_bits (mant_width prec) (exp_width emax)
    (binary_to_bits prec emax x) =
  let s := extract_sign prec emax (binary_to_bits prec emax x)
  let m := extract_mantissa prec (binary_to_bits prec emax x)
  let e := extract_exponent prec emax (binary_to_bits prec emax x)
  (s, m, e) := by
  -- All three extracted components are definitionally the same as `split_bits`.
  simp [split_bits, extract_sign, extract_mantissa, extract_exponent]

-- Bits of binary float range
theorem bits_of_binary_float_range
  {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) :
  0 ≤ binary_to_bits prec emax x ∧
    binary_to_bits prec emax x <
      (2 : Int) ^ (mant_width prec + exp_width emax + 1) := by
  classical
  set mw : Nat := mant_width prec with hmw
  set ew : Nat := exp_width emax with hew
  set mm : Int := (2 : Int) ^ mw with hmm
  set em : Int := (2 : Int) ^ ew with hem
  set expMax : Int := em - 1 with hexpMax

  have h2 : (0 : Int) < 2 := by decide
  have hmm_pos : 0 < mm := by simpa [hmm] using (pow_pos h2 mw)
  have hem_pos : 0 < em := by simpa [hem] using (pow_pos h2 ew)

  have hm0 : 0 ≤ (0 : Int) ∧ (0 : Int) < (2 : Int) ^ mw := by
    refine ⟨le_rfl, ?_⟩
    simpa [hmm] using hmm_pos

  have he0 : 0 ≤ (0 : Int) ∧ (0 : Int) < (2 : Int) ^ ew := by
    refine ⟨le_rfl, ?_⟩
    simpa [hem] using hem_pos

  have hExpMax_em : 0 ≤ expMax ∧ expMax < em := by
    have one_le_em : 1 ≤ em := Int.add_one_le_of_lt hem_pos
    have hnonneg : 0 ≤ expMax := by
      have : 0 ≤ em - 1 := sub_nonneg.mpr one_le_em
      simpa [hexpMax] using this
    have hlt : expMax < em := by
      have : em - 1 < em := by simpa using (sub_one_lt em)
      simpa [hexpMax] using this
    exact ⟨hnonneg, hlt⟩

  have hExpMax : 0 ≤ expMax ∧ expMax < (2 : Int) ^ ew := by
    simpa [hem] using hExpMax_em

  have hm_nanPayload_mm :
      0 ≤ (if 1 < mm then (1 : Int) else 0) ∧ (if 1 < mm then (1 : Int) else 0) < mm := by
    by_cases h1 : 1 < mm
    · refine ⟨by simp [h1], by simpa [h1] using h1⟩
    · have hm_le1 : mm ≤ 1 := le_of_not_gt h1
      have one_le_mm : 1 ≤ mm := Int.add_one_le_of_lt hmm_pos
      have hm_eq1 : mm = 1 := le_antisymm hm_le1 one_le_mm
      refine ⟨by simp [h1], ?_⟩
      -- payload is `0` in this branch and `mm = 1`
      simpa [h1, hm_eq1] using (show (0 : Int) < 1 by decide)

  have hm_nanPayload : 0 ≤ (if 1 < mm then (1 : Int) else 0) ∧
      (if 1 < mm then (1 : Int) else 0) < (2 : Int) ^ mw := by
    simpa [hmm] using hm_nanPayload_mm

  -- We always construct bits via `join_bits`, so use `join_bits_range`.
  cases hx : x.val with
  | F754_zero s =>
      simpa [binary_to_bits, hx, hmw, hew] using
        (join_bits_range (mw:=mw) (ew:=ew) (s:=s) (m:=0) (e:=0) hm0 he0)
  | F754_infinity s =>
      simpa [binary_to_bits, hx, hmw, hew, hexpMax] using
        (join_bits_range (mw:=mw) (ew:=ew) (s:=s) (m:=0) (e:=expMax) hm0 hExpMax)
  | F754_nan s payload =>
      -- For NaNs, the mantissa field is `(payload % mm)` unless that is zero, in which case we
      -- use a canonical nonzero payload when `mm > 1`.
      have hm_mod_mm : 0 ≤ (payload : Int) % mm ∧ (payload : Int) % mm < mm := by
        refine ⟨Int.emod_nonneg (payload : Int) (ne_of_gt hmm_pos),
          Int.emod_lt_of_pos (payload : Int) hmm_pos⟩

      have hmField_mm :
          0 ≤ (if mm ∣ (payload : Int) then (if 1 < mm then (1 : Int) else 0) else (payload : Int) % mm) ∧
            (if mm ∣ (payload : Int) then (if 1 < mm then (1 : Int) else 0) else (payload : Int) % mm) < mm := by
        by_cases hd : mm ∣ (payload : Int)
        · simp [hd, hm_nanPayload_mm]
        · simp [hd, hm_mod_mm]

      have hmField : 0 ≤ (if mm ∣ (payload : Int) then (if 1 < mm then (1 : Int) else 0) else (payload : Int) % mm) ∧
          (if mm ∣ (payload : Int) then (if 1 < mm then (1 : Int) else 0) else (payload : Int) % mm) < (2 : Int) ^ mw := by
        simpa [hmm] using hmField_mm

      simpa [binary_to_bits, hx, hmw, hew, hmm, hem, hexpMax] using
        (join_bits_range (mw:=mw) (ew:=ew) (s:=s)
          (m:=if mm ∣ (payload : Int) then (if 1 < mm then (1 : Int) else 0) else (payload : Int) % mm)
          (e:=expMax) hmField hExpMax)
  | F754_finite s m e =>
      set mInt : Int := (m : Int) with hmInt
      by_cases hzero : mInt = 0
      · have hzeroNat : m = 0 := by
          have : (m : Int) = 0 := by simpa [hmInt] using hzero
          exact (Int.ofNat_eq_zero).1 this
        simpa [binary_to_bits, hx, hmw, hew, hzeroNat] using
          (join_bits_range (mw:=mw) (ew:=ew) (s:=s) (m:=0) (e:=0) hm0 he0)
      · set subExp : Int := (1 - emax) - (mw : Int) with hsubExp
        by_cases hsub : (e = subExp ∧ mInt < mm)
        · have hm_range : 0 ≤ mInt ∧ mInt < (2 : Int) ^ mw := by
            refine ⟨by simp [hmInt], by simpa [hmm] using hsub.2⟩
          have hzeroNat : m ≠ 0 := by
            intro hm0
            apply hzero
            have : (m : Int) = 0 := (Int.ofNat_eq_zero).2 hm0
            simpa [hmInt] using this
          have hsub_e : e = subExp := hsub.1
          have hsub_m : (m : Int) < (2 : Int) ^ (mant_width prec) := by
            simpa [hmInt, hmm, hmw] using hsub.2
          simpa [binary_to_bits, hx, hmw, hew, hmInt, hzeroNat, hsubExp, hsub_e, hsub_m] using
            (join_bits_range (mw:=mw) (ew:=ew) (s:=s) (m:=mInt) (e:=0) hm_range he0)
        · set E : Int := e + (mw : Int) + emax with hE
          by_cases hnorm : (1 ≤ E ∧ E < expMax ∧ mm ≤ mInt ∧ mInt < 2 * mm)
          · have hm_range : 0 ≤ (mInt - mm) ∧ mInt - mm < (2 : Int) ^ mw := by
              refine ⟨sub_nonneg.mpr hnorm.2.2.1, ?_⟩
              have hlt : mInt - mm < mm := by
                have : mInt < mm + mm := by
                  simpa [two_mul, add_assoc, add_comm, add_left_comm] using hnorm.2.2.2
                exact (sub_lt_iff_lt_add).2 (by simpa [add_assoc] using this)
              simpa [hmm] using hlt

            have he_range : 0 ≤ E ∧ E < (2 : Int) ^ ew := by
              refine ⟨le_trans (by decide : (0 : Int) ≤ 1) hnorm.1, ?_⟩
              have hlt_em : E < em := lt_of_lt_of_le hnorm.2.1 (le_of_lt hExpMax_em.2)
              simpa [hem] using hlt_em
            have hzeroNat : m ≠ 0 := by
              intro hm0
              apply hzero
              have : (m : Int) = 0 := (Int.ofNat_eq_zero).2 hm0
              simpa [hmInt] using this
            have hsub' :
                ¬ (e = (1 - emax) - (mant_width prec : Int) ∧ (m : Int) < (2 : Int) ^ (mant_width prec)) := by
              intro hsub''
              apply hsub
              have hsub_m : (m : Int) < (2 : Int) ^ mw := by
                simpa [hmInt, hmm, hmw] using hsub''.2
              exact ⟨by simpa [hsubExp, hmw] using hsub''.1, hsub_m⟩
            have hnormFull :
                1 ≤ e + (mant_width prec : Int) + emax ∧
                  e + (mant_width prec : Int) + emax < (2 : Int) ^ (exp_width emax) - 1 ∧
                    (2 : Int) ^ (mant_width prec) ≤ (m : Int) ∧
                      (m : Int) < 2 * (2 : Int) ^ (mant_width prec) := by
              have h1 : 1 ≤ e + (mant_width prec : Int) + emax := by
                simpa [hE, hmw] using hnorm.1
              have h2 :
                  e + (mant_width prec : Int) + emax < (2 : Int) ^ (exp_width emax) - 1 := by
                simpa [hE, hmw, hexpMax, hem, hew] using hnorm.2.1
              have h3 : (2 : Int) ^ (mant_width prec) ≤ (m : Int) := by
                simpa [hmInt, hmm, hmw] using hnorm.2.2.1
              have h4 : (m : Int) < 2 * (2 : Int) ^ (mant_width prec) := by
                simpa [hmInt, hmm, hmw] using hnorm.2.2.2
              exact ⟨h1, h2, h3, h4⟩
            simpa [binary_to_bits, hx, hmw, hew, hmInt, hzeroNat, hsubExp, hsub', hnormFull, hmm] using
              (join_bits_range (mw:=mw) (ew:=ew) (s:=s) (m:=mInt - mm) (e:=E) hm_range he_range)
          · -- fallback NaN payload
            have hzeroNat : m ≠ 0 := by
              intro hm0
              apply hzero
              have : (m : Int) = 0 := (Int.ofNat_eq_zero).2 hm0
              simpa [hmInt] using this
            have hsub' :
                ¬ (e = (1 - emax) - (mant_width prec : Int) ∧ (m : Int) < (2 : Int) ^ (mant_width prec)) := by
              intro hsub''
              apply hsub
              have hsub_m : (m : Int) < (2 : Int) ^ mw := by
                simpa [hmInt, hmm, hmw] using hsub''.2
              exact ⟨by simpa [hsubExp, hmw] using hsub''.1, hsub_m⟩
            have hnorm' :
                ¬ (1 ≤ e + (mant_width prec : Int) + emax ∧
                    e + (mant_width prec : Int) + emax < (2 : Int) ^ (exp_width emax) - 1 ∧
                      (2 : Int) ^ (mant_width prec) ≤ (m : Int) ∧
                        (m : Int) < 2 * (2 : Int) ^ (mant_width prec)) := by
              intro hnorm''
              apply hnorm
              have hE' : E < expMax := by
                simpa [hE, hmw, hexpMax, hem, hew] using hnorm''.2.1
              have h1 : 1 ≤ E := by
                simpa [hE, hmw] using hnorm''.1
              have hm_lo : mm ≤ mInt := by
                simpa [hmInt, hmm, hmw] using hnorm''.2.2.1
              have hm_hi : mInt < 2 * mm := by
                simpa [hmInt, hmm, hmw] using hnorm''.2.2.2
              exact ⟨h1, hE', hm_lo, hm_hi⟩
            simpa [binary_to_bits, hx, hmw, hew, hmInt, hzeroNat, hsubExp, hsub', hnorm', hmm, hem, hexpMax] using
              (join_bits_range (mw:=mw) (ew:=ew) (s:=s)
                (m:=if 1 < mm then (1 : Int) else 0) (e:=expMax) hm_nanPayload hExpMax)

-- Roundtrip: constructing from bits and back
theorem binary_float_of_bits_of_binary_float
  {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (bits : Int) :
  bits_to_binary prec emax (binary_to_bits prec emax (bits_to_binary prec emax bits)) =
    bits_to_binary prec emax bits := by
  simpa using (binary_bits_roundtrip (prec:=prec) (emax:=emax) bits)

-- Roundtrip: bits_of_binary_float_of_bits
theorem bits_of_binary_float_of_bits
  {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (bits : Int)
  (h : 0 ≤ bits ∧ bits < (2 : Int) ^ (mant_width prec + exp_width emax + 1)) :
  binary_to_bits prec emax (bits_to_binary prec emax bits) = bits := by
  -- Alias of bits_binary_roundtrip
  simpa using (bits_binary_roundtrip (prec:=prec) (emax:=emax) bits h)

-- Injectivity of split_bits within range
theorem split_bits_inj (x y : Int)
  (hx : 0 ≤ x ∧ x < (2 : Int) ^ (mw + ew + 1))
  (hy : 0 ≤ y ∧ y < (2 : Int) ^ (mw + ew + 1))
  (hxy : split_bits mw ew x = split_bits mw ew y) :
  x = y := by
  -- Follows Coq: deduce from join_split_bits on both sides
  -- using computed components equality.
  have hx_join :
      join_bits mw ew (split_bits mw ew x).1 (split_bits mw ew x).2.1 (split_bits mw ew x).2.2 = x := by
    simpa using (join_split_bits (mw := mw) (ew := ew) (x := x) hx)
  have hy_join :
      join_bits mw ew (split_bits mw ew y).1 (split_bits mw ew y).2.1 (split_bits mw ew y).2.2 = y := by
    simpa using (join_split_bits (mw := mw) (ew := ew) (x := y) hy)
  calc
    x = join_bits mw ew (split_bits mw ew x).1 (split_bits mw ew x).2.1 (split_bits mw ew x).2.2 := by
          simpa using hx_join.symm
    _ = join_bits mw ew (split_bits mw ew y).1 (split_bits mw ew y).2.1 (split_bits mw ew y).2.2 := by
          simpa [hxy]
    _ = y := by
          simpa using hy_join
