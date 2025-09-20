# Proof Fixes Log (Raux.lean)

This file records intentional, minimal corrections made while fixing incomplete proofs.

## 1) Theorem `lt_mag`

- Location: `FloatSpec/src/Core/Raux.lean` around line 3390.
- Original (incorrect) postcondition: `e ≤ m` where `m` is the result of `mag beta x`.
- Updated (correct) postcondition: `m ≤ e`.

Rationale:
- By the definition used in this file, `mag beta x = ⌈log |x| / log β⌉` for `x ≠ 0`.
- From the precondition `|x| < (beta : ℝ) ^ e`, we have `logβ |x| < e`, hence `⌈logβ |x|⌉ ≤ e`.
- Therefore, the correct inequality is `mag x ≤ e`, not `e ≤ mag x`.

Implementation notes:
- The proof reuses the existing lemma `mag_le_abs` by strengthening `0 < |x|` to `x ≠ 0`.
- No other definitions or theorems were modified.

## 2) Theorem `mag_le_bpow`

- Location: `FloatSpec/src/Core/Raux.lean` around line 3515.
- Change: Completed the proof by delegating directly to the already-proven lemma `mag_le_abs`.

Rationale:
- The statement is identical to `mag_le_abs` — same precondition and postcondition — so the proof is a one-line wrapper.

Implementation notes:
- Replaced the placeholder with:
  `intro h; exact (mag_le_abs beta x e) h`.
- No spec or definitions changed.
