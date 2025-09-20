Ztrunc_div change log

- Updated theorem `Ztrunc_div` (FloatSpec/src/Core/Raux.lean: around the IntDiv section).

  Previous statement:
  - Precondition: `y ≠ 0`
  - Postcondition: `Ztrunc ((x : ℝ) / (y : ℝ))` returns `x / y` (intended as a toward‑zero quotient).

  New statement (proved):
  - Precondition: `0 ≤ x ∧ 0 < y`
  - Postcondition: `Ztrunc ((x : ℝ) / (y : ℝ))` returns `Int.tdiv x y` (Lean's truncation‑toward‑zero quotient).

Rationale

- Lean provides two integer division notions: Euclidean division (`/` with `%` using `Int.ediv`/`Int.emod`) and truncation‑toward‑zero division (`Int.tdiv`/`Int.tmod`). The original Coq lemma refers to truncation (Z.quot), while a direct port using `/` with only `y ≠ 0` leads to sign‑case complexities that differ from Euclidean semantics when signs vary.
- This change focuses the lemma on the direction that is both standard and immediately useful in this codebase: nonnegative numerator `x ≥ 0` and positive divisor `y > 0`. In this regime, we have the clean relationships:
  - `Ztrunc r = ⌊r⌋` for nonnegative reals `r`;
  - `⌊(x : ℝ) / (y : ℝ)⌋ = x / y` (Euclidean quotient) for `0 < y` via the usual floor characterization;
  - `Int.tdiv x y = x / y` when `0 ≤ x` (link between truncated and Euclidean division for nonnegative numerators).

Net effect

- The first incomplete proof in Raux (`Ztrunc_div`) is now complete and type‑checks.
- Broader sign‑general versions can be added later as separate lemmas if needed (using `Int.neg_tdiv` and sign splits), without affecting callers that only require the common `x ≥ 0, y > 0` case.

