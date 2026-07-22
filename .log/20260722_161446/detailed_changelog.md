# Restore Expbe1

Commit: 201fad1cd926050a21212106f67b9e4aacb2fcec

## Summary

- Restored the exact public Flocq Be2NonZero lemma `Expbe1`.
- Proved the symmetric exponent bound through residual ulp bounds, `xLe2y`, a scaled canonical float, and `Fcanonic_Rle_Zle`.
- Updated the authoritative semantic-gap ledger from 17 remaining candidates to 16.

## Verification

- Focused `lake env lean FloatSpec/src/Pff/Pff.lean` passed.
- Full `lake build` passed all 3345 jobs.
- Placeholder and weakening audit reported zero findings.
- Generated status reported zero `sorry`, `axiom`, and `admit` declarations.
- `git diff --check` and the added-hole scan passed.
