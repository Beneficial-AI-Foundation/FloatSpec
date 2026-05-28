# Pff and Prop Trust Boundary

Date: 2026-05-27

## Decision

`FloatSpec.src.Pff` and `FloatSpec.src.Prop` are explicit exclusion barrels for
the current milestone. They do not re-export their leaf modules.

The Pff leaves and heavy Prop leaves are classified as scaffold/excluded:

- Pff: legacy compatibility layer and Pff-to-Flocq bridge files.
- Prop: relative-error, arithmetic-error, Sterbenz, round-to-odd, and
  double-rounding files.

## Reason

The audit and Flocq comparison show that upstream Flocq has real definitions and
completed proof chains for these surfaces, while the current Lean leaves contain
translation scaffolding and semantic gaps. Porting them faithfully is large and
outside the current repair pass.

## Import Rule

Trusted aggregate imports must not import `FloatSpec.src.Pff` or
`FloatSpec.src.Prop` expecting Flocq semantics from these layers. Direct leaf
imports are allowed only for audit, future porting, or code that is itself
classified outside the trusted surface.

Before either layer moves into the trusted surface, it needs a statement
preservation check against the upstream Coq files and a proof-trust check with no
semantic stand-ins.
