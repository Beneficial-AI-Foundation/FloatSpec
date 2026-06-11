# IEEE754 Proof Notes

This file records the current status of local IEEE754 proof repairs.

`prim_to_binary` is no longer the historical constant-zero bridge. It maps the
stored primitive real through `round_to_generic` and then into the local binary
representation. Older notes that justified proofs by saying every primitive
value maps to positive zero are obsolete and must not be used as audit evidence.

The current policy is:

- executable IEEE helpers may remain as local models when their Flocq payload is
  not fully ported;
- theorem-shaped correctness claims must not be proved by reflexive or
  vacuous behavior;
- missing Flocq payloads should be represented as explicit port-gap
  definitions, not as Hoare triples with trivial postconditions.

The authoritative checks are the Lean files themselves plus `lake build
FloatSpecAudit`.
