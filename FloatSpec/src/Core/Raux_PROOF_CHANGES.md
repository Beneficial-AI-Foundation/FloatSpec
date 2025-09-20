Raux.lean Proof Changes Log

Context: While fixing the first incomplete theorem in `FloatSpec/src/Core/Raux.lean`,
we found a mismatch between the intended Coq semantics and the Lean port regarding
integer powers at negative exponents.

Changed Theorem
- Name: `mag_le_Zpower`
- Location: `FloatSpec/src/Core/Raux.lean`

Original (precondition):
- `⦃⌜1 < beta ∧ |x| < ((beta : ℝ) ^ e)⌝⦄`

Updated (precondition):
- `⦃⌜1 < beta ∧ 0 ≤ e ∧ |x| < ((beta : ℝ) ^ e)⌝⦄`

Rationale
- In Coq Flocq, `IZR (Zpower beta e)` equals `0` when `e < 0`. Hence the hypothesis
  `|x| < IZR (Zpower beta e)` implies `0 ≤ e` automatically (since `|x| ≥ 0`).
- In this Lean port, we model `IZR (Zpower beta e)` via the real integer power
  `((beta : ℝ) ^ e)`, which is always strictly positive, even for negative `e`.
  As a result, the implication `|x| < ((beta : ℝ)^e) → 0 ≤ e` no longer holds by
  default. To faithfully mirror the original Coq statement, we add the explicit
  side condition `0 ≤ e` to the precondition.

Proof Outline
- Case split on `x = 0`:
  - If `x = 0`, then `mag beta x = 0` by definition, and `0 ≤ e` follows from the
    added side condition.
  - If `x ≠ 0`, we reuse the existing lemma `mag_le_bpow`, which requires the
    precondition `1 < beta ∧ x ≠ 0 ∧ |x| < (beta : ℝ)^e` and yields the desired
    conclusion.

This change is minimal, local, and preserves the intended semantics of the Coq lemma
under the Lean modeling of integer powers.

