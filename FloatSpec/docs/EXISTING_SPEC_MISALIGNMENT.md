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

The compatibility names `binary_*_correct` are exact aliases of the translated
`B*_correct` theorem contracts in `IEEE754/SourceCorrectnessAliases.lean`. They
do not claim that the old local helper has the full Flocq behavior.

## Audit interpretation

Zero placeholder findings means that active Lean syntax contains no recognized
proof hole or trivial semantic replacement. It does not prove cross-language
semantic equivalence. Source alignment remains a declaration-by-declaration
review and judge obligation.
