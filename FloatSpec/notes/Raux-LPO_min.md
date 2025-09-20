Summary of changes for FloatSpec/src/Core/Raux.lean

- Added import: `Mathlib.Data.Nat.Find` to access `Nat.find` and supporting lemmas.
- Implemented `noncomputable def LPO_min_choice (P : Nat → Prop)` to return
  - `some (Nat.find h)` when a witness `∃ n, P n` exists (chooses the least witness),
  - `none` otherwise.
  This replaces the previous stub `pure none` which could not satisfy the spec.

- Completed the first incomplete theorem `LPO_min` (around Raux.lean:3048–3066):
  - In the `some` branch, used `Nat.find_spec` for the witness and `Nat.find_min`
    (via the `simp`-rewritten form using `Nat.lt_find_iff`) to obtain minimality.
  - In the `none` branch, discharged the goal using `not_exists.mp`.
  - The proof uses `by classical` to enable classical reasoning; `Nat.find` requires
    `DecidablePred P`, which is provided under classical logic.

- Verified with `lake build`: project builds successfully; remaining `sorry`s in other
  sections/files are untouched per the “fix only the first incomplete theorem” guidance.

