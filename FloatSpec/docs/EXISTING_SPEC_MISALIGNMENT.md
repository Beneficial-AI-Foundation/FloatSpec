# Source Alignment Boundaries

This document records intentional compatibility boundaries that must not be
mistaken for Flocq source declarations.

## Boundedness representations

Flocq's `SpecFloat.bounded prec emax m e` combines canonical mantissa evidence
with the upper exponent bound. FloatSpec exposes this source shape as
`specFloat_bounded`.

The older Lean `bounded` predicate additionally models range checks used by
legacy Nat-based carriers. It is a compatibility predicate, not the Coq
notation. Source-facing finite constructors and `canonical_bounded` use
`specFloat_bounded`; Nat callers use the explicitly named
`canonical_bounded_nat` bridge.

## Local `binary_*` helpers

`binary_add`, `binary_mul`, `binary_sub`, `binary_fma`, `binary_div`, and
`binary_sqrt` predate the source-shaped NaN-handler operations. The Flocq
operations are `Bplus`, `Bmult`, `Bminus`, `Bfma`, `Bdiv`, and `Bsqrt`.

`binary_add_correct` and `binary_mul_correct` are exact aliases of the
translated `Bplus_correct` and `Bmult_correct` contracts in
`IEEE754/SourceCorrectnessAliases.lean`. The translated subtraction, fused
multiply-add, division, and square-root contracts are exported directly as
`Bminus_correct`, `Bfma_correct`, `Bdiv_correct`, and `Bsqrt_correct`.

The current `binary_sub_correct`, `binary_fma_correct`, `binary_div_correct`,
and `binary_sqrt_correct` theorems describe the older local compatibility
operations. They are intentionally not aliases of the source-shaped `B*`
theorems: the Coq declarations quantify over source operations and NaN
handlers, while these compatibility results certify different local helpers.

The shared overflow helper is mode-sensitive as in Coq: nearest modes choose
infinity, round-toward-zero chooses the largest finite value, and directed
modes choose according to the sign. This fixes the previously observable RTZ
and directed-rounding mismatch. The four source-shaped contracts additionally
connect that helper to the translated source operations.

## Audit interpretation

Zero placeholder findings means that active Lean syntax contains no recognized
proof hole or trivial semantic replacement. It does not prove cross-language
semantic equivalence. Source alignment remains a declaration-by-declaration
review and judge obligation.
