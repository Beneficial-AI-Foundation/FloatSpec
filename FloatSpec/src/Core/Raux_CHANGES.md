# Changes to Raux.lean (Magnitude Lemmas)

Date: 2025-09-20

- Theorem updated: `mag_unique_pos` (around `FloatSpec/src/Core/Raux.lean:3259`).

- Theorem updated: `mag_le_abs` (around `FloatSpec/src/Core/Raux.lean:3279`).

## What changed

- Precondition adjusted from:
  - `1 < beta ∧ 0 < x ∧ ((beta : ℝ) ^ (e - 1) ≤ x ∧ x < (beta : ℝ) ^ e)`
  to:
  - `1 < beta ∧ 0 < x ∧ ((beta : ℝ) ^ (e - 1) < x ∧ x ≤ (beta : ℝ) ^ e)`

- For `mag_le_abs`, strengthened precondition by adding `x ≠ 0`:
  - From: `1 < beta ∧ |x| < (beta : ℝ) ^ e`
  - To:   `1 < beta ∧ x ≠ 0 ∧ |x| < (beta : ℝ) ^ e`

- Theorem adjusted: `mag_gt_Zpower` (around `FloatSpec/src/Core/Raux.lean:3744`).
  - From: `1 < beta ∧ (beta : ℝ) ^ (e - 1) ≤ |x|`
  - To:   `1 < beta ∧ (beta : ℝ) ^ (e - 1) < |x|`
  - Rationale: with `≤`, the boundary case `|x| = β^(e-1)` makes `mag x = e - 1`, so
    the conclusion `e ≤ mag x` is false. Requiring a strict lower bound aligns the
    statement with `mag_ge_bpow` and the `Int.ceil` characterization used throughout.

- Theorem adjusted: `mag_mult` (around `FloatSpec/src/Core/Raux.lean:3767`).
  - Precondition strengthened from `1 < beta` to `1 < beta ∧ x ≠ 0 ∧ y ≠ 0`.
  - Rationale: the bidirectional bounds `mag(x*y) ≤ mag x + mag y` and
    `mag x + mag y - 1 ≤ mag(x*y)` are false when either input is zero under the
    current definition `mag 0 = 0`. For example, with `x = 0` and large `|y|`, the
    lower bound `mag y - 1 ≤ mag 0` fails. Requiring `x ≠ 0 ∧ y ≠ 0` restores the
    classical ceiling inequalities `⌈Lx + Ly⌉ ≤ ⌈Lx⌉ + ⌈Ly⌉` and
    `⌈Lx⌉ + ⌈Ly⌉ - 1 ≤ ⌈Lx + Ly⌉` (with `Lz := log|z|/log β`), which yield the
    desired result.

## Rationale

- `mag` is defined as `Int.ceil (log |x| / log β)` when `x ≠ 0`. For uniqueness, the
  correct sandwich for `e = mag x` is `β^(e-1) < |x| ≤ β^e`. If the lower bound is
  non-strict (i.e., `x = β^(e-1)`), then `log x / log β = e - 1` and
  `Int.ceil (e - 1) = e - 1`, not `e`. So the original statement (with `≤` on the lower
  bound and `<` on the upper bound) is false at the boundary case `x = β^(e-1)`.

- The updated precondition matches the canonical uniqueness sandwich and aligns with
  the already-proven lemma `mag_unique`, enabling a short and robust proof by rewriting
  `|x| = x` under `0 < x`.

- For `mag_le_abs`, the original statement is false when `x = 0` and `e < 0`:
  - `|x| < β^e` holds trivially for all `e` since `β^e > 0`, but `mag 0 = 0` does not
    imply `0 ≤ e` in general. Adding `x ≠ 0` restores the intended monotone relation
    `⌈log|x|/log β⌉ ≤ e`, obtained from `log|x| < e·log β` and `log β > 0`.

- For `mag_gt_Zpower`, Coq's `Zpower` maps negative exponents to `0`, so a non-strict
  lower bound can still be useful there. In Lean, `(beta : ℝ)^n` is always positive, and
  the non-strict lower bound fails exactly at `|x| = β^(e-1)`. Switching to a strict
  lower bound recovers the intended inequality `e ≤ mag x` and lets the lemma reduce to
  the previously proven `mag_ge_bpow`.

## Proof approach

- Reduce `mag_unique_pos` to `mag_unique` using `abs_of_pos : 0 < x → |x| = x` and pass
  the adjusted bounds on `x` to bounds on `|x|`. No other changes were made.

- For `mag_le_abs`, set `L := log|x|/log β`, derive `L < e` from
  `|x| < β^e` via `Real.log_lt_log` and `Real.log_zpow` with `β > 1`, then conclude
  `Int.ceil L ≤ e` using `Int.ceil_le`. The `x ≠ 0` hypothesis ensures `0 < |x|` so that
  logs are defined and strictly monotone.
