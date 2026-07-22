# Restore Expr1

Commit: 01650a0e435507543bd3f071b61185297e136487

## Summary

- Restored the exact public Flocq Be2NonZero lemma `Expr1`.
- Proved the exponent bound through residual ulp bounds, `yLe2x`, a scaled canonical float, and `Fcanonic_Rle_Zle`.
- Updated the authoritative semantic-gap ledger from 18 remaining candidates to 17.

## Verification

- Focused `lake env lean FloatSpec/src/Pff/Pff.lean` passed.
- Full `lake build` passed all 3345 jobs.
- Placeholder and weakening audit reported zero findings.
- Generated status reported zero `sorry`, `axiom`, and `admit` declarations.
- `git diff --check` and the added-hole scan passed.
