import FloatSpec.src.IEEE754.Bits

/-!
# Exact FLoCq `IEEE754/Bits.v` surface

The existing implementation uses natural-number widths.  FLoCq exposes
integer widths, including the defined negative-width behavior of `Z.shiftl`
and `Zpower`; this namespace keeps that boundary exact and reuses the existing
implementation once the source hypotheses establish positive widths.
-/

namespace FloatSpec.IEEE754.Bits.Source

local notation "Zpower" => FloatSpec.Core.Zaux.Zpower

private theorem zpower_eq_pow_toNat {w : Int} (hw : 0 ≤ w) :
    Zpower 2 w = (2 : Int) ^ w.toNat := by
  simp [FloatSpec.Core.Zaux.Zpower, hw]

private theorem zpower_eq_zero_of_neg {w : Int} (hw : w < 0) :
    Zpower 2 w = 0 := by
  simp [FloatSpec.Core.Zaux.Zpower, hw]

/-- Coq `Z.shiftl`, including right shift for a negative count. -/
private def zshiftl (x n : Int) : Int :=
  if 0 ≤ n then x * Zpower 2 n else x / Zpower 2 (-n)

/-- Coq `Bits.join_bits`; both widths remain integers. -/
def join_bits (mw ew : Int) (s : Bool) (m e : Int) : Int :=
  zshiftl ((if s then Zpower 2 ew else 0) + e) mw + m

/-- Coq `Bits.split_bits`; both widths remain integers. -/
def split_bits (mw ew x : Int) : Bool × Int × Int :=
  let mm := Zpower 2 mw
  let em := Zpower 2 ew
  (decide (mm * em ≤ x), x % mm, (x / mm) % em)

private theorem nonneg_width_of_range {w x : Int}
    (hx : 0 ≤ x ∧ x < Zpower 2 w) : 0 ≤ w := by
  by_contra hw
  have hw' : w < 0 := lt_of_not_ge hw
  have hp : Zpower 2 w = 0 := zpower_eq_zero_of_neg hw'
  omega

private theorem join_bits_eq_nat {mw ew : Int} (hmw : 0 ≤ mw)
    (hew : 0 ≤ ew) (s : Bool) (m e : Int) :
    join_bits mw ew s m e = _root_.join_bits mw.toNat ew.toNat s m e := by
  unfold join_bits zshiftl
  rw [show Zpower 2 mw = (2 : Int) ^ mw.toNat from zpower_eq_pow_toNat hmw,
    show Zpower 2 ew = (2 : Int) ^ ew.toNat from zpower_eq_pow_toNat hew]
  simp [hmw, _root_.join_bits]

private theorem split_bits_eq_nat {mw ew x : Int} (hmw : 0 ≤ mw)
    (hew : 0 ≤ ew) :
    split_bits mw ew x = _root_.split_bits mw.toNat ew.toNat x := by
  unfold split_bits
  rw [show Zpower 2 mw = (2 : Int) ^ mw.toNat from zpower_eq_pow_toNat hmw,
    show Zpower 2 ew = (2 : Int) ^ ew.toNat from zpower_eq_pow_toNat hew]
  rfl

private theorem zpower_add_widths {mw ew : Int} (hmw : 0 ≤ mw)
    (hew : 0 ≤ ew) :
    Zpower 2 (mw + ew + 1) = (2 : Int) ^ (mw.toNat + ew.toNat + 1) := by
  have hsum : 0 ≤ mw + ew + 1 := by omega
  have hnat : (mw + ew + 1).toNat = mw.toNat + ew.toNat + 1 := by omega
  rw [zpower_eq_pow_toNat hsum, hnat]

/-- Coq `Bits.join_bits_range`. -/
theorem join_bits_range (mw ew : Int) (s : Bool) (m e : Int)
    (hm : 0 ≤ m ∧ m < Zpower 2 mw)
    (he : 0 ≤ e ∧ e < Zpower 2 ew) :
    0 ≤ join_bits mw ew s m e ∧
      join_bits mw ew s m e < Zpower 2 (mw + ew + 1) := by
  have hmw : 0 ≤ mw := nonneg_width_of_range hm
  have hew : 0 ≤ ew := nonneg_width_of_range he
  have h := _root_.join_bits_range (mw := mw.toNat) (ew := ew.toNat)
    s m e (by simpa [zpower_eq_pow_toNat hmw] using hm)
      (by simpa [zpower_eq_pow_toNat hew] using he)
  rw [join_bits_eq_nat (mw:=mw) (ew:=ew) hmw hew,
    zpower_add_widths hmw hew]
  exact h

/-- Coq `Bits.split_join_bits`. -/
theorem split_join_bits (mw ew : Int) (s : Bool) (m e : Int)
    (hm : 0 ≤ m ∧ m < Zpower 2 mw)
    (he : 0 ≤ e ∧ e < Zpower 2 ew) :
    split_bits mw ew (join_bits mw ew s m e) = (s, m, e) := by
  have hmw : 0 ≤ mw := nonneg_width_of_range hm
  have hew : 0 ≤ ew := nonneg_width_of_range he
  rw [join_bits_eq_nat (mw:=mw) (ew:=ew) hmw hew,
    split_bits_eq_nat (mw:=mw) (ew:=ew)
      (x:=_root_.join_bits mw.toNat ew.toNat s m e) hmw hew]
  exact _root_.split_join_bits (mw := mw.toNat) (ew := ew.toNat) s m e
    (by simpa [zpower_eq_pow_toNat hmw] using hm)
    (by simpa [zpower_eq_pow_toNat hew] using he)

/-- Coq `Bits.join_split_bits`. -/
theorem join_split_bits (mw ew : Int) (Hmw : 0 < mw) (Hew : 0 < ew)
    (x : Int) (hx : 0 ≤ x ∧ x < Zpower 2 (mw + ew + 1)) :
    let (s, m, e) := split_bits mw ew x
    join_bits mw ew s m e = x := by
  have hmw : 0 ≤ mw := le_of_lt Hmw
  have hew : 0 ≤ ew := le_of_lt Hew
  have h := _root_.join_split_bits (mw := mw.toNat) (ew := ew.toNat) x
    (by simpa [zpower_add_widths hmw hew] using hx)
  rw [split_bits_eq_nat (mw:=mw) (ew:=ew) (x:=x) hmw hew]
  rcases hs : _root_.split_bits mw.toNat ew.toNat x with ⟨s, m, e⟩
  simp only [hs] at h ⊢
  rw [join_bits_eq_nat (mw:=mw) (ew:=ew) hmw hew]
  exact h

/-- Coq `Bits.split_bits_inj`. -/
theorem split_bits_inj (mw ew : Int) (Hmw : 0 < mw) (Hew : 0 < ew)
    (x y : Int)
    (hx : 0 ≤ x ∧ x < Zpower 2 (mw + ew + 1))
    (hy : 0 ≤ y ∧ y < Zpower 2 (mw + ew + 1))
    (hxy : split_bits mw ew x = split_bits mw ew y) : x = y := by
  have hmw : 0 ≤ mw := le_of_lt Hmw
  have hew : 0 ≤ ew := le_of_lt Hew
  apply _root_.split_bits_inj (mw := mw.toNat) (ew := ew.toNat) x y
    (by simpa [zpower_add_widths hmw hew] using hx)
    (by simpa [zpower_add_widths hmw hew] using hy)
  simpa [split_bits_eq_nat (mw:=mw) (ew:=ew) (x:=x) hmw hew,
    split_bits_eq_nat (mw:=mw) (ew:=ew) (x:=y) hmw hew] using hxy

private def sourcePrec (mw : Int) : Int := mw + 1
private def sourceEmax (ew : Int) : Int := Zpower 2 (ew - 1)
private def sourceEmin (mw ew : Int) : Int := 3 - sourceEmax ew - sourcePrec mw

/-- Coq `Bits.bits_of_binary_float`. -/
def bits_of_binary_float (mw ew : Int)
    (x : binary_float (mw + 1) (Zpower 2 (ew - 1))) : Int :=
  match x with
  | binary_float.B754_zero s => join_bits mw ew s 0 0
  | binary_float.B754_infinity s =>
      join_bits mw ew s 0 (Zpower 2 ew - 1)
  | binary_float.B754_nan s payload _ =>
      join_bits mw ew s (FloatSpec.Core.Zaux.Zpos payload) (Zpower 2 ew - 1)
  | binary_float.B754_finite s mantissa exponent _ =>
      let m := FloatSpec.Core.Zaux.Zpos mantissa - Zpower 2 mw
      if 0 ≤ m then
        join_bits mw ew s m (exponent - sourceEmin mw ew + 1)
      else
        join_bits mw ew s (FloatSpec.Core.Zaux.Zpos mantissa) 0

/-- Coq `Bits.split_bits_of_binary_float`. -/
def split_bits_of_binary_float (mw ew : Int)
    (x : binary_float (mw + 1) (Zpower 2 (ew - 1))) : Bool × Int × Int :=
  match x with
  | binary_float.B754_zero s => (s, 0, 0)
  | binary_float.B754_infinity s => (s, 0, Zpower 2 ew - 1)
  | binary_float.B754_nan s payload _ =>
      (s, FloatSpec.Core.Zaux.Zpos payload, Zpower 2 ew - 1)
  | binary_float.B754_finite s mantissa exponent _ =>
      let m := FloatSpec.Core.Zaux.Zpos mantissa - Zpower 2 mw
      if 0 ≤ m then (s, m, exponent - sourceEmin mw ew + 1)
      else (s, FloatSpec.Core.Zaux.Zpos mantissa, 0)

private theorem bits_eq_join_split (mw ew : Int)
    (x : binary_float (sourcePrec mw) (sourceEmax ew)) :
    bits_of_binary_float mw ew x =
      let (s, m, e) := split_bits_of_binary_float mw ew x
      join_bits mw ew s m e := by
  cases x with
  | B754_zero s => simp [bits_of_binary_float, split_bits_of_binary_float]
  | B754_infinity s => simp [bits_of_binary_float, split_bits_of_binary_float]
  | B754_nan s p hp => simp [bits_of_binary_float, split_bits_of_binary_float]
  | B754_finite s p e hp =>
      by_cases h : 0 ≤ FloatSpec.Core.Zaux.Zpos p - Zpower 2 mw
      · have h' : Zpower 2 mw ≤ FloatSpec.Core.Zaux.Zpos p := sub_nonneg.mp h
        simp [bits_of_binary_float, split_bits_of_binary_float, h, h']
      · have h' : ¬ Zpower 2 mw ≤ FloatSpec.Core.Zaux.Zpos p := by omega
        simp [bits_of_binary_float, split_bits_of_binary_float, h, h']

private theorem zpower_ew_eq_two_emax {ew : Int} (Hew : 0 < ew) :
    Zpower 2 ew = 2 * sourceEmax ew := by
  have hew : 0 ≤ ew := le_of_lt Hew
  have hpred : 0 ≤ ew - 1 := by omega
  have hnat : (ew - 1).toNat + 1 = ew.toNat := by omega
  rw [zpower_eq_pow_toNat hew, show sourceEmax ew = Zpower 2 (ew - 1) from rfl,
    zpower_eq_pow_toNat hpred, ← hnat, pow_succ]
  ring

private theorem positive_lt_zpower_of_nan_pl {mw : Int} (Hmw : 0 < mw)
    (p : FloatSpec.Core.Zaux.Positive)
    (hp : nan_pl (sourcePrec mw) p = true) :
    FloatSpec.Core.Zaux.Zpos p < Zpower 2 mw := by
  let n := FloatSpec.Core.Zaux.positiveToNat p
  have hn : 0 < n := FloatSpec.Core.Zaux.positiveToNat_pos p
  have hdigits := FloatSpec.Core.Digits.digits2_Pnat_correct n hn
  have hd : FloatSpec.Core.Digits.digits2_pos n < mw + 1 := by
    simpa [nan_pl, sourcePrec, FloatSpec.Core.Zaux.Zlt_bool, n,
      Std.Do.PostCond.noThrow, pure] using hp
  have hdNat : FloatSpec.Core.Digits.digits2_Pnat n + 1 ≤ mw.toNat := by
    have hmwCast : (mw.toNat : Int) = mw := Int.toNat_of_nonneg (le_of_lt Hmw)
    have hd' : ((FloatSpec.Core.Digits.digits2_Pnat n + 1 : Nat) : Int) ≤ mw := by
      simpa [FloatSpec.Core.Digits.digits2_pos] using (show
        FloatSpec.Core.Digits.digits2_pos n ≤ mw by omega)
    exact_mod_cast (show ((FloatSpec.Core.Digits.digits2_Pnat n + 1 : Nat) : Int) ≤
      (mw.toNat : Int) by simpa [hmwCast] using hd')
  have hnlt : n < 2 ^ mw.toNat :=
    lt_of_lt_of_le hdigits.2 (Nat.pow_le_pow_right (by norm_num) hdNat)
  rw [zpower_eq_pow_toNat (le_of_lt Hmw)]
  change (n : Int) < ((2 ^ mw.toNat : Nat) : Int)
  exact_mod_cast hnlt

private theorem finite_source_facts {mw ew : Int} (Hmw : 0 < mw)
    {m : FloatSpec.Core.Zaux.Positive} {e : Int}
    (h : specFloat_bounded (prec:=sourcePrec mw) (emax:=sourceEmax ew)
      (FloatSpec.Core.Zaux.positiveToNat m) e = true) :
    sourceEmin mw ew ≤ e ∧
      FloatSpec.Core.Digits.Zdigits 2
        (FloatSpec.Core.Zaux.positiveToNat m : Int) ≤ sourcePrec mw := by
  simp only [specFloat_bounded, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨hc, _⟩
  simp only [canonical_mantissa, beq_iff_eq] at hc
  unfold FLT_exp FloatSpec.Core.FLT.FLT_exp at hc
  constructor
  · unfold sourceEmin
    rw [hc]
    exact le_max_right _ _
  · have hle := le_max_left
        (FloatSpec.Core.Digits.Zdigits 2
          (FloatSpec.Core.Zaux.positiveToNat m : Int) + e - sourcePrec mw)
        (sourceEmin mw ew)
    unfold sourceEmin at hle
    rw [← hc] at hle
    omega

private theorem positive_lt_two_pow_prec {mw : Int} (Hmw : 0 < mw)
    (p : FloatSpec.Core.Zaux.Positive)
    (hd : FloatSpec.Core.Digits.Zdigits 2
      (FloatSpec.Core.Zaux.positiveToNat p : Int) ≤ sourcePrec mw) :
    FloatSpec.Core.Zaux.Zpos p < Zpower 2 (mw + 1) := by
  let n := FloatSpec.Core.Zaux.positiveToNat p
  have hn : 0 < n := FloatSpec.Core.Zaux.positiveToNat_pos p
  have hbits := FloatSpec.Core.Digits.digits2_Pnat_correct n hn
  have hzdigits := FloatSpec.Core.Digits.Z_of_nat_S_digits2_Pnat n hn
  have hdNat : FloatSpec.Core.Digits.digits2_Pnat n + 1 ≤ (mw + 1).toNat := by
    have hmw1 : 0 ≤ mw + 1 := by omega
    have hd' : ((FloatSpec.Core.Digits.digits2_Pnat n + 1 : Nat) : Int) ≤
        ((mw + 1).toNat : Int) := by
      rw [Int.toNat_of_nonneg hmw1]
      rw [hzdigits]
      simpa [sourcePrec] using hd
    exact_mod_cast hd'
  have hnlt : n < 2 ^ (mw + 1).toNat :=
    lt_of_lt_of_le hbits.2 (Nat.pow_le_pow_right (by norm_num) hdNat)
  rw [zpower_eq_pow_toNat (by omega : 0 ≤ mw + 1)]
  change (n : Int) < ((2 ^ (mw + 1).toNat : Nat) : Int)
  exact_mod_cast hnlt

private theorem source_fields_range (mw ew : Int) (Hmw : 0 < mw) (Hew : 0 < ew)
    (x : binary_float (sourcePrec mw) (sourceEmax ew)) :
    let fields := split_bits_of_binary_float mw ew x
    (0 ≤ fields.2.1 ∧ fields.2.1 < Zpower 2 mw) ∧
      (0 ≤ fields.2.2 ∧ fields.2.2 < Zpower 2 ew) := by
  have hmw : 0 ≤ mw := le_of_lt Hmw
  have hew : 0 ≤ ew := le_of_lt Hew
  have hpowMw : 0 < Zpower 2 mw := by
    rw [zpower_eq_pow_toNat hmw]
    positivity
  have hpowEw : 0 < Zpower 2 ew := by
    rw [zpower_eq_pow_toNat hew]
    positivity
  have hpowEwOne : 1 ≤ Zpower 2 ew := by omega
  cases x with
  | B754_zero s =>
      simp [split_bits_of_binary_float, hpowMw, hpowEw]
  | B754_infinity s =>
      simp [split_bits_of_binary_float, hpowMw, hpowEw, hpowEwOne]
  | B754_nan s p hp =>
      have hpPos : 0 < FloatSpec.Core.Zaux.Zpos p := by
        simpa [FloatSpec.Core.Zaux.Zpos] using
          FloatSpec.Core.Zaux.positiveToNat_pos p
      have hpLt := positive_lt_zpower_of_nan_pl Hmw p hp
      simp [split_bits_of_binary_float, hpPos.le, hpLt, hpowEw, hpowEwOne]
  | B754_finite s p e hp =>
      have hpPos : 0 < FloatSpec.Core.Zaux.Zpos p := by
        simpa [FloatSpec.Core.Zaux.Zpos] using
          FloatSpec.Core.Zaux.positiveToNat_pos p
      have hfacts := finite_source_facts Hmw hp
      have hpPrec := positive_lt_two_pow_prec Hmw p hfacts.2
      have hpowSucc : Zpower 2 (mw + 1) = 2 * Zpower 2 mw := by
        simpa [sourceEmax] using zpower_ew_eq_two_emax (ew:=mw + 1) (by omega)
      have hpTwo : FloatSpec.Core.Zaux.Zpos p < 2 * Zpower 2 mw := by
        simpa [hpowSucc] using hpPrec
      by_cases hf : 0 ≤ FloatSpec.Core.Zaux.Zpos p - Zpower 2 mw
      · have hmLt : FloatSpec.Core.Zaux.Zpos p - Zpower 2 mw < Zpower 2 mw := by
          omega
        have heNonneg : 0 ≤ e - sourceEmin mw ew + 1 := by omega
        have hps := hp
        simp only [specFloat_bounded, Bool.and_eq_true, decide_eq_true_eq] at hps
        have heUpper : e ≤ sourceEmax ew - sourcePrec mw := hps.2
        have hPowRel := zpower_ew_eq_two_emax Hew
        have heLt : e - sourceEmin mw ew + 1 < Zpower 2 ew := by
          unfold sourceEmin
          omega
        have hf' : Zpower 2 mw ≤ FloatSpec.Core.Zaux.Zpos p := sub_nonneg.mp hf
        simp [split_bits_of_binary_float, hf, hf', hmLt, heNonneg, heLt]
      · have hmLt : FloatSpec.Core.Zaux.Zpos p < Zpower 2 mw := by omega
        have hf' : ¬ Zpower 2 mw ≤ FloatSpec.Core.Zaux.Zpos p := by omega
        simp [split_bits_of_binary_float, hf, hf', hpPos.le, hmLt, hpowEw]

/-- Coq `Bits.split_bits_of_binary_float_correct`. -/
theorem split_bits_of_binary_float_correct (mw ew : Int)
    (Hmw : 0 < mw) (Hew : 0 < ew)
    (x : binary_float (mw + 1) (Zpower 2 (ew - 1))) :
    split_bits mw ew (bits_of_binary_float mw ew x) =
      split_bits_of_binary_float mw ew x := by
  have hbits := bits_eq_join_split mw ew x
  simp only [sourcePrec, sourceEmax] at hbits
  rw [hbits]
  rcases hs : split_bits_of_binary_float mw ew x with ⟨s, m, e⟩
  have hr := source_fields_range mw ew Hmw Hew x
  simp only [hs] at hr ⊢
  exact split_join_bits mw ew s m e hr.1 hr.2

/-- Coq `Bits.bits_of_binary_float_range`. -/
theorem bits_of_binary_float_range (mw ew : Int)
    (Hmw : 0 < mw) (Hew : 0 < ew)
    (x : binary_float (mw + 1) (Zpower 2 (ew - 1))) :
    0 ≤ bits_of_binary_float mw ew x ∧
      bits_of_binary_float mw ew x < Zpower 2 (mw + ew + 1) := by
  have hbits := bits_eq_join_split mw ew x
  simp only [sourcePrec, sourceEmax] at hbits
  rw [hbits]
  rcases hs : split_bits_of_binary_float mw ew x with ⟨s, m, e⟩
  have hr := source_fields_range mw ew Hmw Hew x
  simp only [hs] at hr ⊢
  exact join_bits_range mw ew s m e hr.1 hr.2

private def positiveOfNat (n : Nat) (h : 0 < n) : FloatSpec.Core.Zaux.Positive :=
  binaryPositiveOfNat n h

private theorem positiveOfNat_spec (n : Nat) (h : 0 < n) :
    FloatSpec.Core.Zaux.positiveToNat (positiveOfNat n h) = n :=
  binaryPositiveOfNat_spec n h

@[simp] private theorem Zpos_positiveOfNat (n : Nat) (h : 0 < n) :
    FloatSpec.Core.Zaux.Zpos (positiveOfNat n h) = (n : Int) := by
  simp [FloatSpec.Core.Zaux.Zpos, positiveOfNat_spec]

/-- Coq `Bits.binary_float_of_bits_aux`, before attaching the validity proof. -/
def binary_float_of_bits_aux (mw ew x : Int) : full_float :=
  let (s, m, e) := split_bits mw ew x
  if e = 0 then
    match m with
    | .ofNat 0 => full_float.F754_zero s
    | .ofNat (n + 1) =>
        full_float.F754_finite s (positiveOfNat (n + 1) (by omega))
          (sourceEmin mw ew)
    | .negSucc _ => full_float.F754_nan false .xH
  else if e = Zpower 2 ew - 1 then
    match m with
    | .ofNat 0 => full_float.F754_infinity s
    | .ofNat (n + 1) =>
        full_float.F754_nan s (positiveOfNat (n + 1) (by omega))
    | .negSucc _ => full_float.F754_nan false .xH
  else
    match m + Zpower 2 mw with
    | .ofNat 0 => full_float.F754_nan false .xH
    | .ofNat (n + 1) =>
        full_float.F754_finite s (positiveOfNat (n + 1) (by omega))
          (e + sourceEmin mw ew - 1)
    | .negSucc _ => full_float.F754_nan false .xH

private theorem split_fields_range (mw ew : Int) (Hmw : 0 < mw) (Hew : 0 < ew)
    (x : Int) :
    let fields := split_bits mw ew x
    (0 ≤ fields.2.1 ∧ fields.2.1 < Zpower 2 mw) ∧
      (0 ≤ fields.2.2 ∧ fields.2.2 < Zpower 2 ew) := by
  have hm : 0 < Zpower 2 mw := by
    rw [zpower_eq_pow_toNat (le_of_lt Hmw)]
    positivity
  have he : 0 < Zpower 2 ew := by
    rw [zpower_eq_pow_toNat (le_of_lt Hew)]
    positivity
  simp [split_bits, Int.emod_nonneg _ (ne_of_gt hm), Int.emod_lt_of_pos _ hm,
    Int.emod_nonneg _ (ne_of_gt he), Int.emod_lt_of_pos _ he]

private theorem digits2_pos_le_of_lt_pow_two {n k : Nat}
    (hnpos : 0 < n) (hn : n < 2 ^ k) :
    FloatSpec.Core.Digits.digits2_Pnat n + 1 ≤ k := by
  have htrip := FloatSpec.Core.Digits.Zdigits_le_Zpower
    (beta := 2) (x := (n : Int)) (e := (k : Int)) (by decide)
  simp only [Std.Do.PostCond.noThrow, pure] at htrip
  have hzd : FloatSpec.Core.Digits.Zdigits 2 (n : Int) ≤ (k : Int) := by
    apply htrip
    constructor
    · exact Int.natCast_nonneg k
    · simp
      exact_mod_cast hn
  have heq := FloatSpec.Core.Digits.Z_of_nat_S_digits2_Pnat n hnpos
  have hle : ((FloatSpec.Core.Digits.digits2_Pnat n + 1 : Nat) : Int) ≤
      (k : Int) := by
    rw [heq]
    exact hzd
  exact_mod_cast hle

private theorem nan_payload_valid_of_lt_pow {prec : Int} {k n : Nat}
    (hnpos : 0 < n) (hnlt : n < 2 ^ k) (hk : (k : Int) < prec) :
    nan_pl prec (positiveOfNat n hnpos) = true := by
  have hd := digits2_pos_le_of_lt_pow_two hnpos hnlt
  have hd' : ((FloatSpec.Core.Digits.digits2_Pnat n + 1 : Nat) : Int) < prec :=
    lt_of_le_of_lt (by exact_mod_cast hd) hk
  simpa [nan_pl, positiveOfNat_spec, FloatSpec.Core.Digits.digits2_pos,
    FloatSpec.Core.Zaux.Zlt_bool] using hd'

private theorem spec_bounded_subnormal {prec emax : Int} {k n : Nat}
    (hk : (k : Int) < prec) (hnlt : n < 2 ^ k)
    (he : 3 - emax - prec ≤ emax - prec) :
    specFloat_bounded (prec:=prec) (emax:=emax) n (3 - emax - prec) = true := by
  unfold specFloat_bounded canonical_mantissa
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
    have hd : FloatSpec.Core.Digits.Zdigits 2 (n : Int) ≤ (k : Int) := by
      have htrip := FloatSpec.Core.Digits.Zdigits_le_Zpower
        (beta:=2) (x:=(n:Int)) (e:=(k:Int)) (by decide)
      simp only [Std.Do.PostCond.noThrow, pure] at htrip
      apply htrip
      constructor
      · exact Int.natCast_nonneg k
      · simp
        exact_mod_cast hnlt
    apply le_antisymm
    · exact le_max_right _ _
    · apply max_le
      · omega
      · omega
  · exact he

private theorem spec_bounded_normal {prec emax : Int} {k n : Nat} {e : Int}
    (hp : prec = (k : Int) + 1)
    (hnlow : 2 ^ k ≤ n) (hnlt : n < 2 ^ (k + 1))
    (hel : 3 - emax - prec ≤ e) (heu : e ≤ emax - prec) :
    specFloat_bounded (prec:=prec) (emax:=emax) n e = true := by
  unfold specFloat_bounded canonical_mantissa
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
    have hzd : FloatSpec.Core.Digits.Zdigits 2 (n : Int) = prec := by
      have htrip := FloatSpec.Core.Digits.Zdigits_unique_from_nonzero_payload
        (beta:=2) (n:=(n:Int)) (e:=prec) (by decide)
      simp only [Std.Do.PostCond.noThrow, pure] at htrip
      apply htrip
      constructor
      · have : 0 < (2 : Nat) ^ k := pow_pos (by norm_num) k
        omega
      constructor
      · have hleft : ((2 : Int) ^ k : Int) ≤ (n : Int) := by exact_mod_cast hnlow
        have hp' : prec - 1 = (k : Int) := by omega
        simpa [Int.natAbs_of_nonneg (show 0 ≤ prec - 1 by omega), hp'] using hleft
      · have hright : (n : Int) < ((2 : Int) ^ (k + 1) : Int) := by exact_mod_cast hnlt
        have hnatAbs : Int.natAbs prec = k + 1 := by
          apply Int.ofNat.inj
          change ((prec.natAbs : Int) = ((k + 1 : Nat) : Int))
          rw [Int.natAbs_of_nonneg (show 0 ≤ prec by omega), hp]
          simp
        simpa [hnatAbs] using hright
    rw [hzd]
    apply le_antisymm
    · simpa using (le_max_left (prec + e - prec) (3 - emax - prec))
    · apply max_le <;> omega
  · exact heu

/-- Coq `Bits.binary_float_of_bits_aux_correct`. -/
theorem binary_float_of_bits_aux_correct (mw ew : Int)
    (Hmw : 0 < mw) (Hew : 0 < ew)
    (Hmax : mw + 1 < Zpower 2 (ew - 1)) (x : Int) :
    valid_full_float_binary (prec:=mw + 1) (emax:=Zpower 2 (ew - 1))
      (binary_float_of_bits_aux mw ew x) = true := by
  rcases hs : split_bits mw ew x with ⟨s, m, e⟩
  have hr := split_fields_range mw ew Hmw Hew x
  simp only [hs] at hr
  have hm := hr.1
  have he := hr.2
  have hmw : 0 ≤ mw := le_of_lt Hmw
  have hpowMw : 0 < Zpower 2 mw := by
    rw [zpower_eq_pow_toNat hmw]
    positivity
  have hprec : sourcePrec mw = (mw.toNat : Int) + 1 := by
    simp [sourcePrec, Int.toNat_of_nonneg hmw]
  have Hmax' : sourcePrec mw < sourceEmax ew := by
    simpa [sourcePrec, sourceEmax] using Hmax
  have hmaxBound : 3 - sourceEmax ew - sourcePrec mw ≤
      sourceEmax ew - sourcePrec mw := by omega
  unfold binary_float_of_bits_aux
  rw [hs]
  dsimp only
  by_cases he0 : e = 0
  · simp only [ite_eq_left he0]
    cases m with
    | ofNat n =>
        cases n with
        | zero => rfl
        | succ n =>
            simp only [valid_full_float_binary, positiveOfNat_spec]
            apply spec_bounded_subnormal
                (prec:=sourcePrec mw) (emax:=sourceEmax ew) (k:=mw.toNat) (n:=n+1)
            · omega
            · rw [zpower_eq_pow_toNat hmw] at hm
              change 0 ≤ Int.ofNat (n + 1) ∧
                Int.ofNat (n + 1) < Int.ofNat (2 ^ mw.toNat) at hm
              have hm' : ((n + 1 : Nat) : Int) < ((2 ^ mw.toNat : Nat) : Int) := by
                exact hm.2
              exact_mod_cast hm'
            · simpa [sourceEmin] using hmaxBound
    | negSucc n => omega
  · simp only [ite_eq_right he0]
    by_cases heMax : e = Zpower 2 ew - 1
    · simp only [ite_eq_left heMax]
      cases m with
      | ofNat n =>
          cases n with
          | zero => rfl
          | succ n =>
              apply nan_payload_valid_of_lt_pow
                  (prec:=sourcePrec mw) (k:=mw.toNat) (n:=n+1)
              · rw [zpower_eq_pow_toNat hmw] at hm
                change 0 ≤ Int.ofNat (n + 1) ∧
                  Int.ofNat (n + 1) < Int.ofNat (2 ^ mw.toNat) at hm
                have hm' : ((n + 1 : Nat) : Int) < ((2 ^ mw.toNat : Nat) : Int) := by
                  exact hm.2
                exact_mod_cast hm'
              · rw [hprec]
                omega
      | negSucc n => omega
    · simp only [ite_eq_right heMax]
      have hmSumPos : 0 < m + Zpower 2 mw := by omega
      cases hsum : m + Zpower 2 mw with
      | ofNat n =>
          cases n with
          | zero =>
              exfalso
              rw [hsum] at hmSumPos
              norm_num at hmSumPos
          | succ n =>
              simp only [valid_full_float_binary, positiveOfNat_spec]
              apply spec_bounded_normal
                  (prec:=sourcePrec mw) (emax:=sourceEmax ew) (k:=mw.toNat)
                  (n:=n+1) (e:=e + sourceEmin mw ew - 1)
              · exact hprec
              · have hlow : Zpower 2 mw ≤ m + Zpower 2 mw := by omega
                rw [hsum, zpower_eq_pow_toNat hmw] at hlow
                change Int.ofNat (2 ^ mw.toNat) ≤ Int.ofNat (n + 1) at hlow
                have hlow' : ((2 ^ mw.toNat : Nat) : Int) ≤ ((n + 1 : Nat) : Int) := by
                  exact hlow
                exact_mod_cast hlow'
              · have hmUpper : m + Zpower 2 mw < 2 * Zpower 2 mw := by omega
                rw [hsum, zpower_eq_pow_toNat hmw] at hmUpper
                change Int.ofNat (n + 1) <
                  Int.ofNat (2 * 2 ^ mw.toNat) at hmUpper
                have hp : (2 : Nat) ^ (mw.toNat + 1) = 2 * 2 ^ mw.toNat := by
                  rw [pow_succ]
                  ring
                rw [hp]
                have hmUpper' : ((n + 1 : Nat) : Int) <
                    ((2 * 2 ^ mw.toNat : Nat) : Int) := by
                  exact hmUpper
                exact_mod_cast hmUpper'
              · unfold sourceEmin
                omega
              · have hpow := zpower_ew_eq_two_emax Hew
                unfold sourceEmin
                omega
      | negSucc n => omega

/-- Coq `Bits.binary_float_of_bits`, attaching the validity proof to the
proof-free decoder result. -/
def binary_float_of_bits (mw ew : Int)
    (Hmw : 0 < mw) (Hew : 0 < ew)
    (Hmax : mw + 1 < Zpower 2 (ew - 1)) (x : Int) :
    binary_float (mw + 1) (Zpower 2 (ew - 1)) :=
  fullFloatToBinaryFloat (binary_float_of_bits_aux mw ew x)
    (binary_float_of_bits_aux_correct mw ew Hmw Hew Hmax x)

private theorem positiveOfNat_roundtrip (p : FloatSpec.Core.Zaux.Positive)
    (h : 0 < FloatSpec.Core.Zaux.positiveToNat p) :
    positiveOfNat (FloatSpec.Core.Zaux.positiveToNat p) h = p := by
  apply FloatSpec.Core.Zaux.positiveToNat_injective
  exact positiveOfNat_spec _ h

private theorem match_Zpos {α : Type} (zero neg : α)
    (f : FloatSpec.Core.Zaux.Positive → α)
    (p : FloatSpec.Core.Zaux.Positive) :
    (match FloatSpec.Core.Zaux.Zpos p with
      | .ofNat 0 => zero
      | .ofNat (n + 1) => f (positiveOfNat (n + 1) (by omega))
      | .negSucc _ => neg) = f p := by
  have hp : 0 < FloatSpec.Core.Zaux.positiveToNat p :=
    FloatSpec.Core.Zaux.positiveToNat_pos p
  unfold FloatSpec.Core.Zaux.Zpos
  generalize hnEq : FloatSpec.Core.Zaux.positiveToNat p = n
  cases n with
  | zero => omega
  | succ n =>
      simp only
      congr 1
      apply FloatSpec.Core.Zaux.positiveToNat_injective
      rw [positiveOfNat_spec]
      omega

private theorem finite_subnormal_exp_eq {mw ew : Int} (Hmw : 0 < mw)
    {p : FloatSpec.Core.Zaux.Positive} {e : Int}
    (hp : specFloat_bounded (prec:=sourcePrec mw) (emax:=sourceEmax ew)
      (FloatSpec.Core.Zaux.positiveToNat p) e = true)
    (hsmall : FloatSpec.Core.Zaux.Zpos p < Zpower 2 mw) :
    e = sourceEmin mw ew := by
  let n := FloatSpec.Core.Zaux.positiveToNat p
  have hn : 0 < n := FloatSpec.Core.Zaux.positiveToNat_pos p
  have hmw : 0 ≤ mw := le_of_lt Hmw
  have hnlt : n < 2 ^ mw.toNat := by
    rw [zpower_eq_pow_toNat hmw] at hsmall
    change (n : Int) < ((2 ^ mw.toNat : Nat) : Int) at hsmall
    exact_mod_cast hsmall
  have hdNat := digits2_pos_le_of_lt_pow_two hn hnlt
  have hzd := FloatSpec.Core.Digits.Z_of_nat_S_digits2_Pnat n hn
  have hd : FloatSpec.Core.Digits.Zdigits 2 (n : Int) ≤ mw := by
    have hmwCast : (mw.toNat : Int) = mw := Int.toNat_of_nonneg hmw
    have hdInt : ((FloatSpec.Core.Digits.digits2_Pnat n + 1 : Nat) : Int) ≤ mw := by
      rw [← hmwCast]
      exact_mod_cast hdNat
    rw [← hzd]
    exact hdInt
  have hfacts := finite_source_facts Hmw hp
  have hc := hp
  simp only [specFloat_bounded, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hcanon := hc.1
  simp only [canonical_mantissa, beq_iff_eq] at hcanon
  unfold FLT_exp FloatSpec.Core.FLT.FLT_exp at hcanon
  have hfirst : FloatSpec.Core.Digits.Zdigits 2 (n : Int) + e - sourcePrec mw < e := by
    unfold sourcePrec
    omega
  by_contra hne
  have heminLt : sourceEmin mw ew < e := by omega
  have hmaxLt : max
      (FloatSpec.Core.Digits.Zdigits 2 (n : Int) + e - sourcePrec mw)
      (sourceEmin mw ew) < e := max_lt hfirst heminLt
  dsimp [n] at hmaxLt
  unfold sourceEmin at hmaxLt
  omega

private theorem binaryFloatToFullFloat_injective {prec emax : Int} :
    Function.Injective
      (binaryFloatToFullFloat : binary_float prec emax → full_float) := by
  intro x y h
  cases x <;> cases y <;>
    simp_all [binaryFloatToFullFloat]

/-- Coq `Bits.binary_float_of_bits_of_binary_float`. -/
theorem binary_float_of_bits_of_binary_float (mw ew : Int)
    (Hmw : 0 < mw) (Hew : 0 < ew)
    (Hmax : mw + 1 < Zpower 2 (ew - 1))
    (x : binary_float (mw + 1) (Zpower 2 (ew - 1))) :
    binary_float_of_bits mw ew Hmw Hew Hmax (bits_of_binary_float mw ew x) = x := by
  apply binaryFloatToFullFloat_injective
  unfold binary_float_of_bits
  rw [binaryFloatToFullFloat_fullFloatToBinaryFloat]
  unfold binary_float_of_bits_aux
  rw [split_bits_of_binary_float_correct mw ew Hmw Hew x]
  cases x with
  | B754_zero s => rfl
  | B754_infinity s =>
      have hpow : 1 < Zpower 2 ew := by
        rw [zpower_eq_pow_toNat (le_of_lt Hew)]
        have hewNat : 0 < ew.toNat := by omega
        exact_mod_cast (Nat.one_lt_two_pow (by omega : ew.toNat ≠ 0))
      have hExp : Zpower 2 ew - 1 ≠ 0 := by omega
      simpa only [split_bits_of_binary_float, hExp, ite_false, ite_true,
        binaryFloatToFullFloat]
  | B754_nan s p hp =>
      have hpow : 1 < Zpower 2 ew := by
        rw [zpower_eq_pow_toNat (le_of_lt Hew)]
        have hewNat : 0 < ew.toNat := by omega
        exact_mod_cast (Nat.one_lt_two_pow (by omega : ew.toNat ≠ 0))
      have hExp : Zpower 2 ew - 1 ≠ 0 := by omega
      simp only [split_bits_of_binary_float, hExp, ite_false,
        binaryFloatToFullFloat]
      exact match_Zpos (full_float.F754_infinity s)
        (full_float.F754_nan false .xH) (full_float.F754_nan s) p
  | B754_finite s p e hp =>
      by_cases hnormal : 0 ≤ FloatSpec.Core.Zaux.Zpos p - Zpower 2 mw
      · have he0 : e - sourceEmin mw ew + 1 ≠ 0 := by
          have hf := finite_source_facts Hmw hp
          omega
        have heMax : e - sourceEmin mw ew + 1 ≠ Zpower 2 ew - 1 := by
          have hps := hp
          simp only [specFloat_bounded, Bool.and_eq_true, decide_eq_true_eq] at hps
          have heUpper := hps.2
          have hpow := zpower_ew_eq_two_emax Hew
          unfold sourceEmax at hpow
          unfold sourceEmin
          unfold sourceEmax sourcePrec
          omega
        have hnormal' : Zpower 2 mw ≤ FloatSpec.Core.Zaux.Zpos p :=
          sub_nonneg.mp hnormal
        simp only [split_bits_of_binary_float, hnormal, ite_true, he0, heMax,
          ite_false, binaryFloatToFullFloat]
        rw [show FloatSpec.Core.Zaux.Zpos p - Zpower 2 mw + Zpower 2 mw =
          FloatSpec.Core.Zaux.Zpos p by ring]
        calc
          (match FloatSpec.Core.Zaux.Zpos p with
            | .ofNat 0 => full_float.F754_nan false .xH
            | .ofNat (n + 1) => full_float.F754_finite s
                (positiveOfNat (n + 1) (by omega))
                (e - sourceEmin mw ew + 1 + sourceEmin mw ew - 1)
            | .negSucc _ => full_float.F754_nan false .xH) =
              full_float.F754_finite s p
                (e - sourceEmin mw ew + 1 + sourceEmin mw ew - 1) :=
            match_Zpos (α:=full_float) (full_float.F754_nan false .xH)
              (full_float.F754_nan false .xH)
              (fun q => full_float.F754_finite s q
                (e - sourceEmin mw ew + 1 + sourceEmin mw ew - 1)) p
          _ = full_float.F754_finite s p e := by congr 1 <;> omega
      · have hsmall : FloatSpec.Core.Zaux.Zpos p < Zpower 2 mw := by omega
        have heq := finite_subnormal_exp_eq Hmw hp hsmall
        have hnormal' : ¬ Zpower 2 mw ≤ FloatSpec.Core.Zaux.Zpos p := by omega
        simp only [split_bits_of_binary_float, hnormal, ite_false, ite_true,
          binaryFloatToFullFloat]
        calc
          (match FloatSpec.Core.Zaux.Zpos p with
            | .ofNat 0 => full_float.F754_zero s
            | .ofNat (n + 1) => full_float.F754_finite s
                (positiveOfNat (n + 1) (by omega)) (sourceEmin mw ew)
            | .negSucc _ => full_float.F754_nan false .xH) =
              full_float.F754_finite s p (sourceEmin mw ew) :=
            match_Zpos (α:=full_float) (full_float.F754_zero s)
              (full_float.F754_nan false .xH)
              (fun q => full_float.F754_finite s q (sourceEmin mw ew)) p
          _ = full_float.F754_finite s p e :=
            congrArg (full_float.F754_finite s p) heq.symm

private def bits_of_full_float (mw ew : Int) : full_float → Int
  | .F754_zero s => join_bits mw ew s 0 0
  | .F754_infinity s => join_bits mw ew s 0 (Zpower 2 ew - 1)
  | .F754_nan s p =>
      join_bits mw ew s (FloatSpec.Core.Zaux.Zpos p) (Zpower 2 ew - 1)
  | .F754_finite s p e =>
      let m := FloatSpec.Core.Zaux.Zpos p - Zpower 2 mw
      if 0 ≤ m then join_bits mw ew s m (e - sourceEmin mw ew + 1)
      else join_bits mw ew s (FloatSpec.Core.Zaux.Zpos p) 0

private theorem bits_of_fullFloatToBinaryFloat (mw ew : Int) (y : full_float)
    (hy : valid_full_float_binary (prec:=sourcePrec mw) (emax:=sourceEmax ew) y = true) :
    bits_of_binary_float mw ew (fullFloatToBinaryFloat y hy) =
      bits_of_full_float mw ew y := by
  cases y <;> rfl

/-- Coq `Bits.bits_of_binary_float_of_bits`. -/
theorem bits_of_binary_float_of_bits (mw ew : Int)
    (Hmw : 0 < mw) (Hew : 0 < ew)
    (Hmax : mw + 1 < Zpower 2 (ew - 1)) (x : Int)
    (hx : 0 ≤ x ∧ x < Zpower 2 (mw + ew + 1)) :
    bits_of_binary_float mw ew (binary_float_of_bits mw ew Hmw Hew Hmax x) = x := by
  have hj := join_split_bits mw ew Hmw Hew x hx
  rcases hs : split_bits mw ew x with ⟨s, m, e⟩
  simp only [hs] at hj
  have hr := split_fields_range mw ew Hmw Hew x
  simp only [hs] at hr
  have hm := hr.1
  have he := hr.2
  unfold binary_float_of_bits
  have hbits := bits_of_fullFloatToBinaryFloat mw ew
    (binary_float_of_bits_aux mw ew x)
    (binary_float_of_bits_aux_correct mw ew Hmw Hew Hmax x)
  rw [hbits]
  unfold binary_float_of_bits_aux
  nth_rewrite 2 [← hj]
  rw [hs]
  dsimp only
  by_cases he0 : e = 0
  · simp only [ite_eq_left he0]
    cases m with
    | ofNat n =>
        cases n with
        | zero => simp [bits_of_full_float, he0]
        | succ n =>
            have hfrac : ¬ 0 ≤ ((n + 1 : Nat) : Int) - Zpower 2 mw := by
              have hm' : ((n + 1 : Nat) : Int) < Zpower 2 mw := by
                simpa only [Int.ofNat_eq_natCast] using hm.2
              omega
            have hfrac' : ¬ Zpower 2 mw ≤ ((n + 1 : Nat) : Int) := by omega
            simp [bits_of_full_float, positiveOfNat_spec, hfrac, hfrac', he0]
            omega
    | negSucc n => omega
  · simp only [ite_eq_right he0]
    by_cases heMax : e = Zpower 2 ew - 1
    · simp only [ite_eq_left heMax]
      cases m with
      | ofNat n =>
          cases n with
          | zero => simp [bits_of_full_float, heMax]
          | succ n =>
              simp [bits_of_full_float, positiveOfNat_spec, heMax]
      | negSucc n => omega
    · simp only [ite_eq_right heMax]
      have hsumPos : 0 < m + Zpower 2 mw := by
        have hp : 0 < Zpower 2 mw := by
          rw [zpower_eq_pow_toNat (le_of_lt Hmw)]
          positivity
        omega
      cases hsum : m + Zpower 2 mw with
      | ofNat n =>
          cases n with
          | zero =>
              exfalso
              rw [hsum] at hsumPos
              norm_num at hsumPos
          | succ n =>
              have hMant : ((n + 1 : Nat) : Int) = m + Zpower 2 mw := by
                simpa only [Int.ofNat_eq_natCast] using hsum.symm
              have hfrac : 0 ≤ ((n + 1 : Nat) : Int) - Zpower 2 mw := by omega
              have hfrac' : Zpower 2 mw ≤ ((n + 1 : Nat) : Int) := by omega
              simp [bits_of_full_float, positiveOfNat_spec, hfrac, hfrac', hMant,
                hm.1]
              ring_nf
      | negSucc n => omega

end FloatSpec.IEEE754.Bits.Source
