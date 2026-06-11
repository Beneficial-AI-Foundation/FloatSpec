# PrimFloat Proof Notes

`PrimFloat` is modeled as a structure carrying a real value, not as a raw real
alias. The local bridge to binary floats uses `round_to_generic` through
`prim_to_binary`; it is not the old constant-zero bridge.

Consequences for proof repair:

- do not justify primitive-float equivalence theorems by assuming
  `prim_to_binary` maps every input to zero;
- equivalence statements that need a faithful machine-primitive bridge should
  either prove the required rounded-real property directly or remain explicit
  port-gap definitions;
- bridge lemmas that are definitional facts about the current local model may
  be kept as ordinary theorems when they state that exact definitional behavior.

The current product boundary is controlled by `FloatSpecLib`; the broader
translated layers, including IEEE754, are checked by the unified FloatSpec build.
