Raux.lean: First incomplete theorem fix

- Location: `FloatSpec/src/Core/Raux.lean:3066–3100` (approx.)
- Change summary:
  - Implemented `LPO_choice` to return `some (Nat.find h)` when `∃ n, P n`, otherwise `none`.
  - Completed the proof of theorem `LPO` by case analysis on existence of a witness and using `Nat.find_spec`.

Rationale

- The previous `LPO_choice` returned `none` unconditionally, which made `LPO` unprovable against its spec.
- The new implementation mirrors `LPO_min_choice`, providing a constructive witness when one exists and aligning with the intended Coq/Flocq lemma.

Notes

- No theorem statements or Hoare-triple specs were changed.
- Build verified with `lake build` after the change.

