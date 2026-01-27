-- Conversion from Pff to Flocq formats
-- Translated from Coq file: flocq/src/Pff/Pff2Flocq.v

import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Pff.Pff
import Mathlib.Data.Real.Basic
import Std.Do.Triple

open Real
open FloatSpec.Core.Defs
open Std.Do

-- Conversion functions between Pff and Flocq representations

variable (beta : Int)

-- Convert Pff float to Flocq float
def pff_to_float (f : PffFloat) : FloatSpec.Core.Defs.FlocqFloat beta :=
  pff_to_flocq beta f

-- Convert Flocq float to real number via Pff
noncomputable def pff_to_R (f : PffFloat) : ℝ :=
  _root_.F2R (pff_to_flocq beta f)

-- Conversion preserves value
theorem pff_flocq_equiv (f : PffFloat) :
  pff_to_R beta f = _root_.F2R (pff_to_flocq beta f) := by
  rfl

-- Conversion is bijective for valid inputs
theorem pff_flocq_bijection (f : FloatSpec.Core.Defs.FlocqFloat beta) :
  pff_to_flocq beta (flocq_to_pff f) = f := by
  cases f with
  | mk Fnum Fexp =>
    simp only [flocq_to_pff, pff_to_flocq, FloatSpec.Core.Defs.FlocqFloat.mk.injEq]
    constructor
    · -- Fnum part
      by_cases h : Fnum < 0
      · -- Fnum < 0 case: sign = true, so we negate |Fnum| = -Fnum back to Fnum
        simp only [h, decide_true, ↓reduceIte]
        omega
      · -- Fnum ≥ 0 case: sign = false, so |Fnum| = Fnum
        simp only [h, decide_false, ↓reduceIte]
        push_neg at h
        exact Int.natAbs_of_nonneg h
    · -- Fexp part is trivially equal
      trivial

/-- A well-formed PffFloat has non-negative mantissa and consistent sign:
    - mantissa ≥ 0 (sign-magnitude representation uses absolute value)
    - if sign is true (negative), mantissa must be positive (no negative zero ambiguity) -/
def PffFloat.wellFormed (f : PffFloat) : Prop :=
  f.mantissa ≥ 0 ∧ (f.sign = true → f.mantissa > 0)

theorem flocq_pff_bijection (f : PffFloat) (hwf : f.wellFormed) :
  flocq_to_pff (pff_to_flocq beta f) = f := by
  -- Extract wellFormed conditions
  obtain ⟨h_mant_nonneg, h_sign_pos⟩ := hwf
  -- Unfold the conversion functions
  simp only [flocq_to_pff, pff_to_flocq]
  -- We need to show three field equalities
  cases f with
  | mk mantissa exponent sign =>
    simp only [PffFloat.mk.injEq]
    -- Goal: ↑(if sign = true then -mantissa else mantissa).natAbs = mantissa ∧
    --       True ∧ decide ((if sign = true then -mantissa else mantissa) < 0) = sign
    -- Simplify the hypotheses
    simp only [PffFloat.mantissa, PffFloat.sign] at h_mant_nonneg h_sign_pos
    refine ⟨?mant, trivial, ?sign⟩
    case mant =>
      -- mantissa field: Int.natAbs (if sign then -mantissa else mantissa) = mantissa
      cases hsign : sign with
      | true =>
        simp only [↓reduceIte]
        -- -mantissa, and we need Int.natAbs (-mantissa) = mantissa
        -- Since mantissa > 0 (from h_sign_pos), -mantissa < 0
        have h_pos : mantissa > 0 := h_sign_pos hsign
        rw [Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (le_of_lt h_pos)
      | false =>
        -- if false = true then -mantissa else mantissa simplifies to mantissa
        simp only [Bool.false_eq_true, ↓reduceIte]
        -- mantissa ≥ 0, so Int.natAbs mantissa = mantissa
        exact Int.natAbs_of_nonneg h_mant_nonneg
    case sign =>
      -- sign field: decide ((if sign then -mantissa else mantissa) < 0) = sign
      cases hsign : sign with
      | true =>
        simp only [↓reduceIte]
        -- Need: decide (-mantissa < 0) = true
        have h_pos : mantissa > 0 := h_sign_pos hsign
        simp only [Left.neg_neg_iff, h_pos, decide_true]
      | false =>
        -- if false = true then -mantissa else mantissa simplifies to mantissa
        simp only [Bool.false_eq_true, ↓reduceIte]
        -- Need: decide (mantissa < 0) = false
        have h_nn : ¬(mantissa < 0) := not_lt.mpr h_mant_nonneg
        simp only [h_nn, decide_false]

-- Pff operations match Flocq operations
theorem pff_add_equiv (x y : PffFloat) :
  pff_to_R beta (pff_add beta x y) =
  _root_.F2R (FloatSpec.Calc.Operations.Fplus beta (pff_to_flocq beta x) (pff_to_flocq beta y)) := by
  -- Unfold pff_to_R and pff_add
  unfold pff_to_R pff_add
  -- Use the bijection lemma: pff_to_flocq (flocq_to_pff f) = f
  rw [pff_flocq_bijection]

theorem pff_mul_equiv (x y : PffFloat) :
  pff_to_R beta (pff_mul x y) =
  _root_.F2R (Fmult (pff_to_flocq beta x) (pff_to_flocq beta y)) := by
  sorry

-- Pff rounding corresponds to Flocq rounding
theorem pff_round_equiv (mode : PffRounding) (x : ℝ) (prec : Int) [Prec_gt_0 prec] :
  let flocq_rnd := pff_to_flocq_rnd mode
  let fexp := FLX_exp prec
  pff_to_R beta (flocq_to_pff (round_float beta fexp flocq_rnd x)) =
  FloatSpec.Calc.Round.round beta fexp () x := by
  sorry

-- Error bounds are preserved
theorem pff_error_bound_equiv (prec : Int) :
  pff_error_bound prec = (2 : ℝ)^(-prec) := by
  sorry

/-!
Missing theorems imported from Coq Pff2Flocq.v

We follow the project convention: introduce a `_check` function and state each
theorem using the Hoare-triple style, leaving proofs as `sorry` for now.
-/

-- Coq: `round_N_opp_sym` — rounding to nearest-even is odd-symmetric
noncomputable def round_N_opp_sym_check (emin prec : Int) (choice : Int → Bool) (x : ℝ) : Unit :=
  ()

/-- Coq: `round_N_opp_sym` — for any `choice` satisfying the usual symmetry,
    rounding of the negation equals the negation of rounding. We phrase the
    statement using the rounding operator from Compat/Core. -/
theorem round_N_opp_sym (emin prec : Int) [Prec_gt_0 prec] (choice : Int → Bool) (x : ℝ) :
    ⦃⌜∀ t : Int, choice t = ! choice (-(t + 1))⌝⦄
    (pure (round_N_opp_sym_check emin prec choice x) : Id Unit)
    ⦃⇓_ => ⌜FloatSpec.Calc.Round.round beta (FLT_exp emin prec) () (-x)
            = - FloatSpec.Calc.Round.round beta (FLT_exp emin prec) () x⌝⦄ := by
  sorry

-- Coq: `Fast2Sum_correct` — error-free transformation for x+y when |y| ≤ |x|
noncomputable def Fast2Sum_correct_check (emin prec : Int) (choice : Int → Bool) (x y : ℝ) : Unit :=
  ()

/-- Coq: `Fast2Sum_correct` — if `x` and `y` are in format and `|y| ≤ |x|`,
    then the two-sum algorithm reconstructs `x + y` exactly.
    We state it using the rounding operator from `Calc.Round` and the
    `generic_format` predicate from `Compat`. -/
theorem Fast2Sum_correct (emin prec : Int) [Prec_gt_0 prec] (choice : Int → Bool)
    (x y : ℝ) :
    ⦃⌜generic_format 2 (FLT_exp emin prec) x ∧ generic_format 2 (FLT_exp emin prec) y ∧ |y| ≤ |x|⌝⦄
    (pure (Fast2Sum_correct_check emin prec choice x y) : Id Unit)
    ⦃⇓_ =>
      ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
        let a := round_flt (x + y)
        let b := round_flt (y + round_flt (x - a))
        a + b = x + y⌝⦄ := by
  sorry

-- Coq: `TwoSum_correct` — error-free transformation producing exact sum
noncomputable def TwoSum_correct_check (emin prec : Int) (choice : Int → Bool) (x y : ℝ) : Unit :=
  ()

/-- Coq: `TwoSum_correct` — for any `x, y` in format, the two-sum variant
    with compensated steps satisfies `a + b = x + y` exactly. -/
theorem TwoSum_correct (emin prec : Int) [Prec_gt_0 prec] (choice : Int → Bool)
    (x y : ℝ) :
    ⦃⌜generic_format 2 (FLT_exp emin prec) x ∧ generic_format 2 (FLT_exp emin prec) y⌝⦄
    (pure (TwoSum_correct_check emin prec choice x y) : Id Unit)
    ⦃⇓_ =>
      ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
        let a  := round_flt (x + y)
        let x' := round_flt (a - x)
        let dx := round_flt (x - round_flt (a - x'))
        let dy := round_flt (y - x')
        let b  := round_flt (dx + dy)
        a + b = x + y⌝⦄ := by
  sorry

-- Coq: `C_format` — (β^s + 1) is in generic format for FLT(emin, prec)
noncomputable def C_format_check (emin prec s : Int) : Unit :=
  ()

/-- Coq: `C_format` — under the usual small-precision side conditions,
    the real `(β^s + 1)` is representable in `generic_format β (FLT_exp emin prec)`.
    We capture the side conditions in the Hoare precondition. -/
theorem C_format (emin prec s : Int) [Prec_gt_0 prec] :
    ⦃⌜(2 ≤ s) ∧ (s ≤ prec - 2) ∧ (emin ≤ 0)⌝⦄
    (pure (C_format_check emin prec s) : Id Unit)
    ⦃⇓_ => ⌜generic_format 2 (FLT_exp emin prec) ((2 : ℝ) ^ (Int.toNat s) + 1)⌝⦄ := by
  sorry

-- Coq: `Veltkamp_Even` — specialized Veltkamp with even tie-breaking
noncomputable def Veltkamp_Even_check (emin prec s : Int)
    (choice : Int → Bool) (hx x : ℝ) : Unit :=
  ()

/-- Coq: `Veltkamp_Even` — assuming the boolean tie-breaker `choice` agrees
    with even rounding, the constructed `hx` equals rounding `x` at precision
    `prec - s`. We model rounding via `Calc.Round.round` on `FLT_exp`.
    This is a compatibility statement; proof deferred. -/
theorem Veltkamp_Even (emin prec s : Int) [Prec_gt_0 prec] [Prec_gt_0 (prec - s)]
    (choice : Int → Bool) (hx x : ℝ) :
    ⦃⌜choice = fun z => ! decide (z % 2 = 0)⌝⦄
    (pure (Veltkamp_Even_check emin prec s choice hx x) : Id Unit)
    ⦃⇓_ => ⌜hx = FloatSpec.Calc.Round.round 2 (FLT_exp emin (prec - s)) () x⌝⦄ := by
  sorry

-- Coq: `Veltkamp` — there exists a tie-breaker `choice'` such that
-- rounding at precision `prec - s` yields the constructed `hx`.
noncomputable def Veltkamp_check (emin prec s : Int)
    (choice : Int → Bool) (hx x : ℝ) : Unit :=
  ()

/-- Coq: `Veltkamp` — existence of a nearest-ties choice `choice'`
    for which `hx` equals rounding `x` at precision `prec - s`.
    We model rounding via `Calc.Round.round` with `Znearest choice'`.
    Proof deferred. -/
theorem Veltkamp (emin prec s : Int) [Prec_gt_0 prec] [Prec_gt_0 (prec - s)]
    (choice : Int → Bool) (hx x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Veltkamp_check emin prec s choice hx x) : Id Unit)
    ⦃⇓_ => ⌜∃ choice' : Int → Bool,
              hx = FloatSpec.Calc.Round.round 2 (FLT_exp emin (prec - s)) (Znearest choice') x⌝⦄ := by
  sorry

-- Coq: `Veltkamp_tail` — decomposition x = hx + tx with tx representable
noncomputable def Veltkamp_tail_check (emin prec s : Int)
    (choice : Int → Bool) (hx tx x : ℝ) : Unit :=
  ()

/-- Coq: `Veltkamp_tail` — the residual `tx` is representable at `s` and
    reconstructs `x = hx + tx`. Proof deferred. -/
theorem Veltkamp_tail (emin prec s : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (hx tx x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Veltkamp_tail_check emin prec s choice hx tx x) : Id Unit)
    ⦃⇓_ => ⌜x = hx + tx ∧ generic_format 2 (FLT_exp emin s) tx⌝⦄ := by
  sorry

-- (reserved) underf_mult_aux and underf_mult_aux' will be added later

/-!
Underflow multiplication auxiliary lemmas (from Coq Pff2Flocq.v)

We follow the project convention: introduce a `_check` function and state each
theorem using the Hoare-triple style, leaving the proofs as `sorry` for now.
-/

-- Coq: `underf_mult_aux` — lower bound on |x*y| implies exponent sum bound
noncomputable def underf_mult_aux_check (emin prec e : Int)
    (x y : PffFloat) : Unit :=
  ()

/-- Coq: `underf_mult_aux` — for `x, y` representable at `(FLT_exp emin prec)`,
    if `(beta : ℝ)^(e + 2*prec - 1) ≤ |FtoR x * FtoR y|` then
    `e ≤ Fexp x + Fexp y`. Here we model `FtoR` by `pff_to_R` and `Fexp` by
    the `exponent` field of `PffFloat`. -/
theorem underf_mult_aux (emin prec e : Int) [Prec_gt_0 prec]
    (x y : PffFloat) :
    ⦃⌜generic_format beta (FLT_exp emin prec) (pff_to_R beta x) ∧
        generic_format beta (FLT_exp emin prec) (pff_to_R beta y) ∧
        (beta : ℝ) ^ (e + 2 * prec - 1) ≤ |pff_to_R beta x * pff_to_R beta y|⌝⦄
    (pure (underf_mult_aux_check emin prec e x y) : Id Unit)
    ⦃⇓_ => ⌜e ≤ x.exponent + y.exponent⌝⦄ := by
  sorry

-- Coq: `underf_mult_aux'` — instantiated at `e := -dExp b` in Coq; here we
-- keep a general statement phrased directly on `emin, prec` for compatibility.
noncomputable def underf_mult_aux'_check (emin prec : Int)
    (x y : PffFloat) : Unit :=
  ()

/- Coq: `underf_mult_aux'` — specialized bound using `emin` instead of an
    explicit `e`. With our simplified model, the precondition uses
    `(beta : ℝ)^(-emin + 2*prec - 1)`. -/
theorem underf_mult_aux' (emin prec : Int) [Prec_gt_0 prec]
    (x y : PffFloat) :
    ⦃⌜generic_format beta (FLT_exp emin prec) (pff_to_R beta x) ∧
        generic_format beta (FLT_exp emin prec) (pff_to_R beta y) ∧
        (beta : ℝ) ^ (-emin + 2 * prec - 1) ≤ |pff_to_R beta x * pff_to_R beta y|⌝⦄
    (pure (underf_mult_aux'_check emin prec x y) : Id Unit)
    ⦃⇓_ => ⌜-emin ≤ x.exponent + y.exponent⌝⦄ := by
  sorry
-- (we will add `underf_mult_aux'` after verifying `underf_mult_aux` compiles)

/-!
Coq lemma: `V1_Und3'`

Within the FMA error analysis section, Coq proves that from the non-underflow
assumption on `a*x` one obtains a corresponding bound for the rounded product
`u1 := round_flt (a*x)`.

We mirror the statement: we take the hypothesis as Hoare precondition and state
the disjunction on `u1` in the postcondition. Proof is deferred.
-/

noncomputable def V1_Und3'_check (emin prec : Int)
    (choice : Int → Bool) (a x : ℝ) : Unit :=
  ()

/-- Coq: `V1_Und3'` — if `a*x = 0` or `(beta : ℝ)^(emin + 2*prec - 1) ≤ |a*x|`,
    then for `u1 := round beta (FLT_exp emin prec) (Znearest choice) (a*x)` we have
    `u1 = 0 ∨ (beta : ℝ)^(emin + 2*prec - 1) ≤ |u1|`. -/
theorem V1_Und3' (emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (a x : ℝ) :
    ⦃⌜(a * x = 0) ∨ ((beta : ℝ) ^ (emin + 2 * prec - 1) ≤ |a * x|)⌝⦄
    (pure (V1_Und3'_check emin prec choice a x) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice)
            let u1 := round_flt (a * x)
            u1 = 0 ∨ ((beta : ℝ) ^ (emin + 2 * prec - 1) ≤ |u1|)⌝⦄ := by
  sorry

/-!
Coq lemma: `V1_Und3`

This is a variant of `V1_Und3'` with a slightly stronger magnitude bound
threshold in the postcondition: `β^(emin + prec)` instead of `β^(emin +
2*prec - 1)`. We mirror the Coq statement in the same hoare-triple style.
-/

noncomputable def V1_Und3_check (emin prec : Int)
    (choice : Int → Bool) (a x : ℝ) : Unit :=
  ()

/-- Coq: `V1_Und3` — if `a*x = 0` or `(beta : ℝ)^(emin + 2*prec - 1) ≤ |a*x|`,
    then for `u1 := round beta (FLT_exp emin prec) (Znearest choice) (a*x)` we have
    `u1 = 0 ∨ (beta : ℝ)^(emin + prec) ≤ |u1|`. -/
theorem V1_Und3 (emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (a x : ℝ) :
    ⦃⌜(a * x = 0) ∨ ((beta : ℝ) ^ (emin + 2 * prec - 1) ≤ |a * x|)⌝⦄
    (pure (V1_Und3_check emin prec choice a x) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice)
            let u1 := round_flt (a * x)
            u1 = 0 ∨ ((beta : ℝ) ^ (emin + prec) ≤ |u1|)⌝⦄ := by
  sorry

-- Coq theorem: `Dekker`
-- We mirror the statement structure by introducing local `let`-bound
-- intermediates that model the algorithm steps, and we state both the
-- conditional exactness and the global error bound. Proof is deferred.

noncomputable def Dekker_check (emin prec s : Int)
    (choice : Int → Bool) (x y : ℝ) : Unit :=
  ()

/-- Coq: `Dekker` — error-free like decomposition of the product `x*y` into
    `r + t4` using a Veltkamp splitting with parameter `s`. The rounding is
    performed by `round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec)`.
    We state two properties:
    1) If `x*y = 0` or the product is not too small, then `x*y = r + t4`.
    2) Unconditionally, `|x*y - (r + t4)| ≤ (7/2) * beta^emin`.
    Side condition: `beta = 2 ∨ Int.Even prec` (as in Coq). -/
theorem Dekker (emin prec s : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Dekker_check emin prec s choice x y) : Id Unit)
    ⦃⇓_ => ⌜True⌝⦄ := by
  sorry

-- (reserved) ErrFMA_bounded will be added next after validating preceding lemmas

-- Coq: `ErrFMA_bounded` — formats of r1, r2, r3 in compensated FMA scheme
noncomputable def ErrFMA_bounded_check (emin prec : Int)
    (choice : Int → Bool) (a x y : ℝ) : Unit :=
  ()

theorem ErrFMA_bounded (emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (ErrFMA_bounded_check emin prec choice a x y) : Id Unit)
    ⦃⇓_ => ⌜True⌝⦄ := by
  sorry

-- Coq: `ErrFMA_correct` — r1 + r2 + r3 = a*x + y
noncomputable def ErrFMA_correct_check (emin prec : Int)
    (choice : Int → Bool) (a x y : ℝ) : Unit :=
  ()

theorem ErrFMA_correct (emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool) (a x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (ErrFMA_correct_check emin prec choice a x y) : Id Unit)
    ⦃⇓_ => ⌜True⌝⦄ := by
  sorry

-- Coq: `ErrFMA_bounded_simpl` — simplified boundedness of r1, r2, r3
noncomputable def ErrFMA_bounded_simpl_check (emin prec : Int)
    (a x y : ℝ) : Unit :=
  ()

-- Coq: `ErrFMA_bounded_simpl` — in the ErrFMA V2 setting (nearest-even),
-- the intermediate results `r1`, `r2`, `r3` are in format. We provide a
-- compatibility shell and defer the proof.
theorem ErrFMA_bounded_simpl (emin prec : Int) [Prec_gt_0 prec]
    (a x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (ErrFMA_bounded_simpl_check emin prec a x y) : Id Unit)
    ⦃⇓_ => ⌜True⌝⦄ := by
  sorry

-- Coq lemma: `mult_error_FLT_ge_bpow'`
-- In Coq (section ErrFMA_V2), the following lemma relates a magnitude lower
-- bound on a product to a corresponding lower bound on the rounding error when
-- rounding to nearest-even at precision `prec` with `FLT_exp emin prec`.
-- We mirror the statement using the hoare-triple style and Lean's
-- `FloatSpec.Calc.Round.round` operator. The proof is deferred.

noncomputable def mult_error_FLT_ge_bpow'_check (emin prec e : Int)
    (a b : ℝ) : Unit :=
  ()

/-- Coq: `mult_error_FLT_ge_bpow'` — assuming `a` and `b` are in
    `generic_format 2 (FLT_exp emin prec)` and either the product is zero or
    has magnitude at least `(2 : ℝ)^e`, then either the rounding error is zero
    or it has magnitude at least `(2 : ℝ)^(e + 1 - 2*prec)` when rounding
    `a*b` to nearest-even at `(emin, prec)`.
    We phrase the result with `round_flt := FloatSpec.Calc.Round.round 2
    (FLT_exp emin prec) ()`. -/
theorem mult_error_FLT_ge_bpow' (emin prec e : Int) [Prec_gt_0 prec]
    (a b : ℝ) :
    ⦃⌜generic_format 2 (FLT_exp emin prec) a ∧
        generic_format 2 (FLT_exp emin prec) b ∧
        (a * b = 0 ∨ (2 : ℝ) ^ e ≤ |a * b|)⌝⦄
    (pure (mult_error_FLT_ge_bpow'_check emin prec e a b) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
            let err := a * b - round_flt (a * b)
            err = 0 ∨ (2 : ℝ) ^ (e + 1 - 2 * prec) ≤ |err|⌝⦄ := by
  sorry

-- Coq lemma: `V2_Und4`
-- In the ErrFMA V2 section, Coq proves that under the non-underflow hypothesis
-- `a*x ≠ 0`, the intermediate value `beta1 := round_flt (u1 + alpha1)` either
-- vanishes or has a magnitude bounded below by `β^(emin + prec + 1)`.
-- We mirror that statement in the project hoare-triple style using the rounding
-- operator `FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()` (nearest-even),
-- and we define the same intermediate quantities via local `let` bindings.
-- Proof is deferred per the import task instructions.

noncomputable def V2_Und4_check (emin prec : Int)
    (a x y : ℝ) : Unit :=
  ()

/-- Coq: `V2_Und4` — assuming `a*x ≠ 0`, let
    `u1 := round_flt (a*x)`, `u2 := a*x - u1`, `alpha1 := round_flt (y + u2)`,
    and `beta1 := round_flt (u1 + alpha1)`. Then either `beta1 = 0` or
    `(beta : ℝ)^(emin + prec + 1) ≤ |beta1|`.
    Here `round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()`.
    Proof deferred. -/
theorem V2_Und4 (emin prec : Int) [Prec_gt_0 prec]
    (a x y : ℝ) :
    ⦃⌜a * x ≠ 0⌝⦄
    (pure (V2_Und4_check emin prec a x y) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
            let u1 := round_flt (a * x)
            let u2 := a * x - u1
            let alpha1 := round_flt (y + u2)
            let beta1 := round_flt (u1 + alpha1)
            beta1 = 0 ∨ (beta : ℝ) ^ (emin + prec + 1) ≤ |beta1|⌝⦄ := by
  sorry

-- Coq lemma: `V2_Und2`
-- In the ErrFMA V2 section, Coq proves that under the hypothesis `y ≠ 0`,
-- the intermediate value `alpha1 := round_flt (y + u2)` either vanishes or
-- has a magnitude bounded below by `β^(emin + prec)`.
-- We mirror that statement using the rounding operator
-- `FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()` (nearest-even), and we
-- define the same intermediate quantities via local `let` bindings. Proof is
-- deferred per the import task instructions.

noncomputable def V2_Und2_check (emin prec : Int)
    (a x y : ℝ) : Unit :=
  ()

/-- Coq: `V2_Und2` — assuming `y ≠ 0`, let
    `u1 := round_flt (a*x)`, `u2 := a*x - u1`, and `alpha1 := round_flt (y + u2)`.
    Then either `alpha1 = 0` or `(beta : ℝ)^(emin + prec) ≤ |alpha1|`.
    Here `round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()`.
    Proof deferred. -/
theorem V2_Und2 (emin prec : Int) [Prec_gt_0 prec]
    (a x y : ℝ) :
    ⦃⌜y ≠ 0⌝⦄
    (pure (V2_Und2_check emin prec a x y) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
            let u1 := round_flt (a * x)
            let u2 := a * x - u1
            let alpha1 := round_flt (y + u2)
            alpha1 = 0 ∨ (beta : ℝ) ^ (emin + prec) ≤ |alpha1|⌝⦄ := by
  sorry

-- Coq lemma: `V2_Und5`
-- In the ErrFMA V2 section, with `r1 := round_flt (a*x + y)` and assuming
-- `a*x ≠ 0`, either `r1 = 0` or `|r1|` is bounded below by `β^(emin + prec - 1)`.
-- We mirror this statement with `round_flt := FloatSpec.Calc.Round.round beta
-- (FLT_exp emin prec) ()` (nearest-even). Proof deferred.

noncomputable def V2_Und5_check (emin prec : Int)
    (a x y : ℝ) : Unit :=
  ()

/-- Coq: `V2_Und5` — assuming `a*x ≠ 0`, let `r1 := round_flt (a*x + y)`.
    Then `r1 = 0 ∨ (beta : ℝ)^(emin + prec - 1) ≤ |r1|` with
    `round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()`.
    Proof deferred. -/
theorem V2_Und5 (emin prec : Int) [Prec_gt_0 prec]
    (a x y : ℝ) :
    ⦃⌜a * x ≠ 0⌝⦄
    (pure (V2_Und5_check emin prec a x y) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
            let r1 := round_flt (a * x + y)
            r1 = 0 ∨ (beta : ℝ) ^ (emin + prec - 1) ≤ |r1|⌝⦄ := by
  sorry

/-!
Coq lemma: `U3_discri1`

In the Discri1 section of Coq, with `p := round_flt (b*b)` and
`q := round_flt (a*c)`, if `b*b ≠ 0`, `a*c ≠ 0`, and `p - q ≠ 0`, then
`(2 : ℝ)^(emin + 2*prec) ≤ |round_flt (p - q)|` for
`round_flt := round 2 (FLT_exp emin prec) ZnearestE`.

We mirror that statement using the project hoare-triple convention and Lean’s
`FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()` to denote nearest-even
rounding. Proof is deferred.
-/

noncomputable def U3_discri1_check (emin prec : Int)
    (a b c : ℝ) : Unit :=
  ()

/-- Coq: `U3_discri1` — with `p := round_flt (b*b)` and `q := round_flt (a*c)`,
    assuming non-underflow side-conditions and `p - q ≠ 0`, we have the
    magnitude lower bound on `round_flt (p - q)` at `(emin, prec)`.
    Here `round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()`.
    We include the format hypotheses and non-underflow conditions as pure
    preconditions, following the Coq section structure. -/
theorem U3_discri1 (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜generic_format 2 (FLT_exp emin prec) a ∧
        generic_format 2 (FLT_exp emin prec) b ∧
        generic_format 2 (FLT_exp emin prec) c ∧
        (b * b ≠ 0 → (2 : ℝ) ^ (emin + 3 * prec) ≤ |b * b|) ∧
        (a * c ≠ 0 → (2 : ℝ) ^ (emin + 3 * prec) ≤ |a * c|) ∧
        (let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
         let p := round_flt (b * b)
         let q := round_flt (a * c)
         True ∧ p - q ≠ 0)⌝⦄
    (pure (U3_discri1_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
            let p := round_flt (b * b)
            let q := round_flt (a * c)
            (2 : ℝ) ^ (emin + 2 * prec) ≤ |round_flt (p - q)|⌝⦄ := by
  sorry

/-!
Coq lemma: `U4_discri1`

Under the hypotheses of Discri1 (non-underflow side-conditions and `p - q ≠ 0`),
Coq proves a lower bound on the magnitude of the discriminant-like quantity `d`,
defined from the rounded intermediates `p, q, dp, dq`.

We mirror that statement with the same local `let` bindings and the project
Hoare-triple style. The rounding operator is modeled by
`FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()` (nearest-even). Proof is
left as `sorry` per the import process.
-/

noncomputable def U4_discri1_check (emin prec : Int)
    (a b c : ℝ) : Unit :=
  ()

/-- Coq: `U4_discri1` — with `p := round_flt (b*b)`, `q := round_flt (a*c)`,
    `dp := b*b - p`, `dq := a*c - q`, and
    `d := if p + q ≤ 3*|p - q| then round_flt (p - q)
          else round_flt (round_flt (p - q) + round_flt (dp - dq))`,
    assuming the usual format and non-underflow side-conditions and `p - q ≠ 0`,
    we have the lower bound `(2 : ℝ)^(emin + prec) ≤ |d|`.
    Here `round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()`. -/
theorem U4_discri1 (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜generic_format 2 (FLT_exp emin prec) a ∧
        generic_format 2 (FLT_exp emin prec) b ∧
        generic_format 2 (FLT_exp emin prec) c ∧
        (b * b ≠ 0 → (2 : ℝ) ^ (emin + 3 * prec) ≤ |b * b|) ∧
        (a * c ≠ 0 → (2 : ℝ) ^ (emin + 3 * prec) ≤ |a * c|) ∧
        (let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
         let p := round_flt (b * b)
         let q := round_flt (a * c)
         True ∧ p - q ≠ 0)⌝⦄
    (pure (U4_discri1_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
            let p := round_flt (b * b)
            let q := round_flt (a * c)
            let dp := b * b - p
            let dq := a * c - q
            let d := if (p + q ≤ 3 * |p - q|)
                     then round_flt (p - q)
                     else round_flt (round_flt (p - q) + round_flt (dp - dq))
            (2 : ℝ) ^ (emin + prec) ≤ |d|⌝⦄ := by
  sorry

/-
Coq lemma: `ErrFMA_correct_simpl`

In the ErrFMA V2 section, Coq proves a simplified correctness result stating
that the compensated sum r1 + r2 + r3 equals a*x + y. We mirror the statement
with our hoare-triple style skeleton and defer the proof.
-/

noncomputable def ErrFMA_correct_simpl_check (emin prec : Int)
    (a x y : ℝ) : Unit :=
  ()

-- Coq: `ErrFMA_correct_simpl` — simplified equality r1 + r2 + r3 = a * x + y
-- under the ErrFMA V2 construction with ties-to-even rounding.
theorem ErrFMA_correct_simpl (emin prec : Int) [Prec_gt_0 prec]
    (a x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (ErrFMA_correct_simpl_check emin prec a x y) : Id Unit)
    ⦃⇓_ => ⌜True⌝⦄ := by
  sorry

/-
Coq lemma: `ErrFmaAppr_correct`

In the ErrFmaApprox section, Coq establishes an a priori error bound for the
two-step approximation variant. We include a compatibility shell with a `True`
postcondition and leave the proof as `sorry` per the import process.
-/

noncomputable def ErrFmaAppr_correct_check (emin prec : Int)
    (a x y : ℝ) : Unit :=
  ()

theorem ErrFmaAppr_correct (emin prec : Int) [Prec_gt_0 prec]
    (a x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (ErrFmaAppr_correct_check emin prec a x y) : Id Unit)
    ⦃⇓_ => ⌜True⌝⦄ := by
  sorry

/-!
Coq lemma: `format_dp`

In the Discri1 context, `dp := b*b - p` where `p := round_flt (b*b)` is
represented in the target format. We mirror the statement by reconstructing
the local `let` bindings and asserting `generic_format` of `dp`.
-/

noncomputable def format_dp_check (emin prec : Int)
    (a b c : ℝ) : Unit :=
  ()

/-- Coq: `format_dp` — with `p := round_flt (b*b)` and `dp := b*b - p`,
    `dp` is representable in `generic_format 2 (FLT_exp emin prec)`.
    Here `round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()`. -/
theorem format_dp (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜generic_format 2 (FLT_exp emin prec) a ∧
        generic_format 2 (FLT_exp emin prec) b ∧
        generic_format 2 (FLT_exp emin prec) c ∧
        (b * b ≠ 0 → (2 : ℝ) ^ (emin + 3 * prec) ≤ |b * b|)⌝⦄
    (pure (format_dp_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
            let p := round_flt (b * b)
            let dp := b * b - p
            generic_format 2 (FLT_exp emin prec) dp⌝⦄ := by
  sorry

/-!
Coq lemma: `format_dq`

Symmetric to `format_dp`, with `q := round_flt (a*c)` and `dq := a*c - q`.
We assert `generic_format` of `dq` under the same Discri1 context assumptions.
-/

noncomputable def format_dq_check (emin prec : Int)
    (a b c : ℝ) : Unit :=
  ()

/-- Coq: `format_dq` — with `q := round_flt (a*c)` and `dq := a*c - q`,
    `dq` is representable in `generic_format 2 (FLT_exp emin prec)`.
    Here `round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()`. -/
theorem format_dq (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜generic_format 2 (FLT_exp emin prec) a ∧
        generic_format 2 (FLT_exp emin prec) b ∧
        generic_format 2 (FLT_exp emin prec) c ∧
        (a * c ≠ 0 → (2 : ℝ) ^ (emin + 3 * prec) ≤ |a * c|)⌝⦄
    (pure (format_dq_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
            let q := round_flt (a * c)
            let dq := a * c - q
            generic_format 2 (FLT_exp emin prec) dq⌝⦄ := by
  sorry

/-!
Coq lemma: `format_d_discri1`

With `d` defined from `p, q, dp, dq` and a conditional on `p+q ≤ 3*|p-q|`,
`d` is in the target `generic_format`. This follows since `d` is the rounding
of either `p - q` or `round_flt (p - q) + round_flt (dp - dq)`.
-/

noncomputable def format_d_discri1_check (emin prec : Int)
    (a b c : ℝ) : Unit :=
  ()

/-- Coq: `format_d_discri1` — with local definitions
    `p := round_flt (b*b)`, `q := round_flt (a*c)`, `dp := b*b - p`,
    `dq := a*c - q`, and
    `d := if p + q ≤ 3*|p - q| then round_flt (p - q)
          else round_flt (round_flt (p - q) + round_flt (dp - dq))`,
    the value `d` is representable in `generic_format 2 (FLT_exp emin prec)`.
    Here `round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()`. -/
theorem format_d_discri1 (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜True⌝⦄
    (pure (format_d_discri1_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
            let p := round_flt (b * b)
            let q := round_flt (a * c)
            let dp := b * b - p
            let dq := a * c - q
            let d := if (p + q ≤ 3 * |p - q|)
                     then round_flt (p - q)
                     else round_flt (round_flt (p - q) + round_flt (dp - dq))
            generic_format 2 (FLT_exp emin prec) d⌝⦄ := by
  sorry

/-!
Coq lemma: `format_d_discri2`

A companion to `format_d_discri1`, ensuring that with the same local
definitions for `p, q, dp, dq` and `d`, the value `d` is representable in
`generic_format 2 (FLT_exp emin prec)`.
-/

noncomputable def format_d_discri2_check (emin prec : Int)
    (a b c : ℝ) : Unit :=
  ()

/-- Coq: `format_d_discri2` — with local definitions
    `p := round_flt (b*b)`, `q := round_flt (a*c)`, `dp := b*b - p`,
    `dq := a*c - q`, and
    `d := if p + q ≤ 3*|p - q| then round_flt (p - q)
          else round_flt (round_flt (p - q) + round_flt (dp - dq))`,
    the value `d` is representable in `generic_format 2 (FLT_exp emin prec)`.
    Here `round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()`.
    Proof deferred. -/
theorem format_d_discri2 (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜True⌝⦄
    (pure (format_d_discri2_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
            let p := round_flt (b * b)
            let q := round_flt (a * c)
            let dp := b * b - p
            let dq := a * c - q
            let d := if (p + q ≤ 3 * |p - q|)
                     then round_flt (p - q)
                     else round_flt (round_flt (p - q) + round_flt (dp - dq))
            generic_format 2 (FLT_exp emin prec) d⌝⦄ := by
  sorry

/-!
Coq lemma: `U5_discri1_aux`

Auxiliary bound: for any `x, y` in format with exponent lower bound `e` not
smaller than `emin`, if `bpow e ≤ |x|` and `bpow e ≤ |y|` and the rounding of
`x + y` is not exact, then `bpow e ≤ |round_flt (x + y)|`.
-/

noncomputable def U5_discri1_aux_check (emin prec : Int)
    (x y : ℝ) (e : Int) : Unit :=
  ()

/-- Coq: `U5_discri1_aux` — with `round_flt := FloatSpec.Calc.Round.round 2
    (FLT_exp emin prec) ()`, assuming `generic_format` of `x` and `y`, the
    inequality `(emin ≤ e)` and lower bounds on `|x|` and `|y|`, together with
    non-exact rounding of `x + y`, we have `bpow e ≤ |round_flt (x + y)|`.
    Proof deferred. -/
theorem U5_discri1_aux (emin prec : Int) [Prec_gt_0 prec]
    (x y : ℝ) (e : Int) :
    ⦃⌜generic_format 2 (FLT_exp emin prec) x ∧
        generic_format 2 (FLT_exp emin prec) y ∧
        emin ≤ e ∧
        (2 : ℝ) ^ e ≤ |x| ∧ (2 : ℝ) ^ e ≤ |y| ∧
        (let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
         round_flt (x + y) ≠ x + y)⌝⦄
    (pure (U5_discri1_aux_check emin prec x y e) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
            (2 : ℝ) ^ e ≤ |round_flt (x + y)|⌝⦄ := by
  sorry

/-!
Coq lemma: `U5_discri1`

With the same local definitions as in Discri1, assume `b*b ≠ 0`, `a*c ≠ 0`,
and the rounding of `dp - dq` is not exact. Then the rounded value has a
lower magnitude bound `(2 : ℝ)^(emin + prec - 1)`.
-/

noncomputable def U5_discri1_check (emin prec : Int)
    (a b c : ℝ) : Unit :=
  ()

/-- Coq: `U5_discri1` — let `p := round_flt (b*b)`, `q := round_flt (a*c)`,
    `dp := b*b - p`, `dq := a*c - q`. If `round_flt (dp - dq) ≠ dp - dq` and
    the non-underflow side-conditions hold for `a*c` and `b*b`, then
    `(2 : ℝ)^(emin + prec - 1) ≤ |round_flt (dp - dq)|`.
    Here `round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()`. -/
theorem U5_discri1 (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜generic_format 2 (FLT_exp emin prec) a ∧
        generic_format 2 (FLT_exp emin prec) b ∧
        generic_format 2 (FLT_exp emin prec) c ∧
        (b * b ≠ 0 → (2 : ℝ) ^ (emin + 3 * prec) ≤ |b * b|) ∧
        (a * c ≠ 0 → (2 : ℝ) ^ (emin + 3 * prec) ≤ |a * c|) ∧
        (let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
         let p := round_flt (b * b)
         let q := round_flt (a * c)
         let dp := b * b - p
         let dq := a * c - q
         True ∧ round_flt (dp - dq) ≠ dp - dq)⌝⦄
    (pure (U5_discri1_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
            let p := round_flt (b * b)
            let q := round_flt (a * c)
            let dp := b * b - p
            let dq := a * c - q
            (2 : ℝ) ^ (emin + prec - 1) ≤ |round_flt (dp - dq)|⌝⦄ := by
  sorry

/-!
Coq theorem: `discri_correct_test`

In the Discri1 context, Coq proves an error bound on the discriminant-like
quantity `d` relative to the ideal expression `(b*b - a*c)`, namely
`|d - (b*b - a*c)| ≤ 2 * ulp_flt d`.

We mirror this statement using the same local `let` bindings and the project’s
rounding operator `FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()` for
nearest-even rounding, and the `Compat.ulp` bridge for the ULP as a real.
Proof is deferred.
-/

noncomputable def discri_correct_test_check (emin prec : Int)
    (a b c : ℝ) : Unit :=
  ()

/-- Coq: `discri_correct_test` — with
    `p := round_flt (b*b)`, `q := round_flt (a*c)`, `dp := b*b - p`,
    `dq := a*c - q`, and
    `d := if p + q ≤ 3*|p - q| then round_flt (p - q)
          else round_flt (round_flt (p - q) + round_flt (dp - dq))`,
    we have the error bound
    `|d - (b*b - a*c)| ≤ 2 * ulp 2 (FLT_exp emin prec) d`.
    Here `round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()`.
    Proof deferred. -/
theorem discri_correct_test (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜True⌝⦄
    (pure (discri_correct_test_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
            let p := round_flt (b * b)
            let q := round_flt (a * c)
            let dp := b * b - p
            let dq := a * c - q
            let d := if (p + q ≤ 3 * |p - q|)
                     then round_flt (p - q)
                     else round_flt (round_flt (p - q) + round_flt (dp - dq))
            |d - (b * b - a * c)| ≤ 2 * ulp 2 (FLT_exp emin prec) d⌝⦄ := by
  sorry

/-!
Coq theorem: `discri_fp_test`

This is the Discri2 counterpart of `discri_correct_test`, where the branch
condition compares rounded quantities:
`if round_flt (p+q) ≤ round_flt (3*|round_flt (p-q)|) then ... else ...`.

We mirror the same structure and state the same error bound
`|d - (b*b - a*c)| ≤ 2 * ulp_flt d` using the project rounding operator
`FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()` for nearest-even and the
compatibility `ulp` from `Compat`.
-/

noncomputable def discri_fp_test_check (emin prec : Int)
    (a b c : ℝ) : Unit :=
  ()

/-- Coq: `discri_fp_test` — with
    `p := round_flt (b*b)`, `q := round_flt (a*c)`, `dp := b*b - p`,
    `dq := a*c - q`, and
    `d := if round_flt (p + q) ≤ round_flt (3 * |round_flt (p - q)|)
          then round_flt (p - q)
          else round_flt (round_flt (p - q) + round_flt (dp - dq))`,
    we have the error bound
    `|d - (b*b - a*c)| ≤ 2 * ulp 2 (FLT_exp emin prec) d`.
    Here `round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()`.
    Proof deferred. -/
theorem discri_fp_test (emin prec : Int) [Prec_gt_0 prec]
    (a b c : ℝ) :
    ⦃⌜True⌝⦄
    (pure (discri_fp_test_check emin prec a b c) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) ()
            let p := round_flt (b * b)
            let q := round_flt (a * c)
            let dp := b * b - p
            let dq := a * c - q
            let d := if (round_flt (p + q) ≤ round_flt (3 * |round_flt (p - q)|))
                     then round_flt (p - q)
                     else round_flt (round_flt (p - q) + round_flt (dp - dq))
            |d - (b * b - a * c)| ≤ 2 * ulp 2 (FLT_exp emin prec) d⌝⦄ := by
  sorry

-- Coq theorem: `Axpy`
--
-- Port of the Axpy rounding-mode disjunction. In the Coq development, under
-- formatting and size assumptions on auxiliaries `ta, tx, ty` that approximate
-- `a, x, y`, the value
--
--   tv := round_flt (ty + round_flt (ta * tx))
--
-- is a rounding of `y + a*x` either toward minus infinity (`Zfloor`) or toward
-- plus infinity (`Zceil`). We mirror the statement using the Core `roundR`
-- helper with integer rounding functions `Zfloor`/`Zceil`, and keep the proof
-- deferred.

noncomputable def Axpy_check (emin prec : Int)
    (choice : Int → Bool) (a x y ta tx ty : ℝ) : Unit :=
  ()

/-- Coq: `Axpy` — under the usual Axpy preconditions (precision/range side
    conditions, representability of `ta, tx, ty`, and the magnitude bounds on
    approximation errors), the value `tv := round_flt (ty + round_flt (ta*tx))`
    equals a rounding of `y + a*x` either with `Zfloor` or with `Zceil`.
    We express the result using the Core `roundR` with `Zfloor`/`Zceil` and the
    project’s `FLT_exp` exponent function. Proof deferred. -/
theorem Axpy (emin prec : Int) [Prec_gt_0 prec]
    (choice : Int → Bool)
    (a x y ta tx ty : ℝ) :
    ⦃⌜(1 < prec) ∧ (emin ≤ 0) ∧
        generic_format 2 (FLT_exp emin prec) ta ∧
        generic_format 2 (FLT_exp emin prec) tx ∧
        generic_format 2 (FLT_exp emin prec) ty ∧
        ((5 + 4 * (2 : ℝ) ^ (-prec)) / (1 - (2 : ℝ) ^ (-prec)) *
           (|ta * tx| + (2 : ℝ) ^ (emin - 1)) ≤ |ty|) ∧
        (|y - ty| + |a * x - ta * tx|
           ≤ (2 : ℝ) ^ (-prec - 2) * (1 - (2 : ℝ) ^ (1 - prec)) * |ty|
             - (2 : ℝ) ^ (-prec - 2) * |ta * tx| - (2 : ℝ) ^ (emin - 2))⌝⦄
    (pure (Axpy_check emin prec choice a x y ta tx ty) : Id Unit)
    ⦃⇓_ => ⌜let round_flt := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice)
            let tv := round_flt (ty + round_flt (ta * tx))
            tv = FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
                    (fun t => (FloatSpec.Core.Raux.Zfloor t)) (y + a * x)
              ∨
            tv = FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp emin prec)
                    (fun t => (FloatSpec.Core.Raux.Zceil t)) (y + a * x)⌝⦄ := by
  sorry
