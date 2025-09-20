Raux: Proof Adjustment Notes

Date: 2025-09-20

Context: While fixing the first incomplete proof in `FloatSpec/src/Core/Raux.lean`,
we found that the original statement of `mag_gt_bpow` was not correct with the
current definition of `mag` (which is `⌈log |x| / log β⌉` for nonzero `x`).

Change made:

- Theorem `mag_gt_bpow` (first incomplete proof in the file)
  - Before: precondition used a non-strict lower bound
    `1 < beta ∧ (beta : ℝ) ^ (e - 1) ≤ |x|` with conclusion `e ≤ mag beta x`.
  - After: precondition is strengthened to a strict lower bound
    `1 < beta ∧ (beta : ℝ) ^ (e - 1) < |x|` with the same conclusion.

Rationale:

- With `mag x := ⌈log |x| / log β⌉`, equality at the lower bound
  `|x| = (β : ℝ)^(e-1)` yields `mag x = e - 1`, so the original
  conclusion `e ≤ mag x` is false in that corner case.
- The strict inequality ensures `(e - 1 : ℝ) < log |x| / log β`, hence
  `e ≤ ⌈log |x| / log β⌉`, making the theorem valid.

Notes:

- The subsequent lemma `mag_ge_bpow` in the file already uses the strict
  lower bound and has the same conclusion; it remains unchanged here.
- All other code and specifications are left untouched.

