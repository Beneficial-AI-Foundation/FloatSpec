# FloatSpec Trust Tiers

Date: 2026-05-26

This file defines how the pipeline classifies generated or repaired proof code.
It is a policy document for agent runs and generated status reports, not a claim
that the current repository already satisfies the trusted tier.

## Tier 0: Trusted

A module or theorem can be treated as trusted only when all of these hold:

- It builds under the selected validation command.
- It does not depend on new `sorry`, `axiom`, `admit`, or private bridge facts.
- Its definitions preserve the intended Flocq semantics.
- Its theorem statement preserves upstream hypotheses and conclusion structure, or the adaptation is documented.
- It has no placeholder predicates such as `:= True` or `fun _ _ => True`.
- It has no identity/constant implementation standing in for real arithmetic or rounding.

## Tier 1: Scaffold

Scaffold code preserves useful names, imports, signatures, or partial proof shape,
but is not yet trusted. This tier is acceptable only when the code is clearly
reported as scaffold and does not feed a trusted theorem.

Examples:

- A theorem statement with `sorry` that faithfully mirrors upstream Flocq.
- A dependency placeholder explicitly marked as blocked.
- A module imported only by experimental code.

## Tier 2: Experimental

Experimental code may be useful for exploration but cannot be used as evidence of
proof progress.

Examples:

- Compatibility shims.
- Partially translated IEEE or Pff code.
- Definitions under active semantic repair.

## Tier 3: Excluded

Excluded code is intentionally outside the current milestone.

Current default exclusions:

- `Pff`, unless a later milestone needs legacy compatibility.
- Heavy `Prop` error-analysis and double-rounding layers when the milestone excludes error-bound analysis.
- `PrimFloat`, unless Lean primitive-float semantics are connected to the same model.
- Full IEEE arithmetic/normalization until `BinarySingleNaN` and `Binary` are ported faithfully.
- Higher ULP-nearest theorems when the milestone is limited to directed rounding and basic generic-format properties.

## Required Attempt Artifacts

Every agent proof attempt should produce:

- A build result.
- A local target result.
- A trust-gate result.
- Coq-alignment status.
- A structured `attempt.json` or blocked report.

Build success alone is not enough to move code into Tier 0.
