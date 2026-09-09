# FloatSpec Translation and Review Pipeline

FloatSpec is a semantic port of Flocq, not a tactic-by-tactic transcription.
Every translated declaration must preserve the source contract before proof
repair begins.

## Trusted inputs

- Coq source: `Deps/flocq/src` (or the pinned source checkout used by the task)
- Lean target: `FloatSpec/src`
- Toolchain and dependencies: `lean-toolchain`, `lakefile.lean`, `lake-manifest.json`

Record the exact Coq revision in every translation or judge report.  Local
absolute paths, agent transcripts, full diffs, and compiler logs belong in run
artifacts, not in the library tree.

## Per-declaration workflow

1. Extract the Coq declaration, parameters, implicit section variables,
   theorem statement, and direct dependencies.
2. Write a short source-semantics note.  Identify representation changes such
   as Coq `positive` versus Lean `Nat`, Boolean predicates versus propositions,
   rounding-mode encodings, and proof-carrying constructors.
3. Search Mathlib, CSLib, and existing FloatSpec declarations before adding a
   new abstraction.
4. Freeze the Lean statement before attempting its proof.  A changed
   precondition, dropped output clause, `Unit`, `True`, constant implementation,
   or conclusion repeated as a hypothesis requires explicit reviewer approval.
5. Reconstruct the proof using the Coq proof structure and Lean dependencies.
6. Compile the affected module and its source-contract regression tests.
7. Run the trust gates and record the source-to-target mapping for the judge.

Never replace an unresolved proposition with a same-name `Unit` definition.
Never add `sorry`, `admit`, an axiom, or a weakened theorem to make a run green.
If a faithful proof is blocked, keep the declaration out of trusted exports and
record the missing lemma in the external run report.

## Source-facing and compatibility APIs

Source-facing declarations retain the Flocq contract and use source-shaped
types where feasible.  Compatibility helpers must be named and documented as
such.  For example, the range-only Lean predicate `bounded` is distinct from
Flocq's `SpecFloat.bounded`; source theorems use `specFloat_bounded`.

When an old local theorem name has no Coq counterpart, either remove it or make
it an exact alias of the corresponding source theorem.  Do not certify a local
helper under a misleading source-correctness name.

## Required local gates

```bash
lake build
lake build FloatSpecTests
lake build floatspec
lake build FloatSpec.Test
scripts/audit_placeholders.sh --json FloatSpec
scripts/status_report.sh --write
git diff --check
```

The placeholder audit must report zero active `sorry`, `admit`, axioms, and
semantic-placeholder patterns.  The generated status files must be committed
and reproducible from a clean checkout.

## Alignment judge

Run the repository judge only after compilation and trust gates pass.  Each
matched item receives the source declaration, target declaration, dependency
context, and both repository roots.  An `aligned` verdict requires executable
or proof-checked evidence on both sides; a `not_aligned` verdict requires a
verified counterexample.  Unverifiable cross-language input/output identity is
reported as uncertainty rather than converted into a negative verdict.

Judge outputs, harnesses, model transcripts, and counterexamples are pipeline
artifacts.  Only concise, manually audited conclusions belong under
`FloatSpec/docs`.

## Reviewable change structure

Integration work is split by dependency layer:

1. toolchain and trust infrastructure;
2. Core representations and generic rounding;
3. Calc operations;
4. Prop rounding/error theorems;
5. IEEE754 representations and operations;
6. Pff compatibility;
7. source-contract tests;
8. documentation and CI.

Generated `.log`, `.change_log`, `.subagent_log`, and local cache files are
ignored and must not be force-added to commits.
