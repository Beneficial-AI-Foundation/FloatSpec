# FloatSpec Pipeline Improvements from Verina++

Date: 2026-05-25

Scope: suggestions for the FloatSpec proof-generation and proof-repair pipeline, borrowing lessons from the surrounding Verina/Verina++ evaluation reports and plans. This document focuses on process. It does not cover VCFloat-style `ErrorBound` implementation.

## Summary

The current FloatSpec pipeline already has useful instructions: pick one theorem, inspect the local spec and source, avoid `axiom`/`admit`/trivial placeholders, build after each change, and log the attempt. However, the repo state shows that text-level guidance is not enough. The pipeline needs machine-checkable gates that detect semantic weakening, placeholder proofs, and inconsistent shared definitions.

Verina++ experience suggests the key upgrade: treat proof repair as an evaluated workflow with structured artifacts, not as a series of ad hoc agent edits.

## Lessons to Borrow

### 1. Add structured validation results per attempt

Source anchors:

- FloatSpec already says "compile after each step" in [scripts/subagent_prompt.md](/mnt2/users/kaile/hantao/verina/FloatSpec/scripts/subagent_prompt.md:20).
- Verina pipeline schemas use explicit validation statuses and report artifacts in `repo-level-vcg-pipeline-pr/docs/pipeline-schema.md`.

Recommendation:

For every proof attempt, emit an `attempt.json` record:

```json
{
  "target": "FloatSpec/src/Core/Ulp.lean:2526",
  "reason": "sorry",
  "result": "blocked",
  "build": "pass|fail|not_run",
  "no_new_sorry": true,
  "no_axiom_or_admit": true,
  "no_placeholder_semantics": false,
  "coq_alignment": "checked|not_checked|not_applicable",
  "statement_changed": false,
  "blocker": "needs DN/UP spacing lemma",
  "changed_files": []
}
```

This makes progress auditable and prevents "agent round" commits from being the only state trail.

### 2. Separate build success from placeholder status

Source anchors:

- Verina reports show many failures are build failures, unfilled slots, or joint-check failures rather than subtle local proof mistakes in [eval_case_study_20260506.md](/mnt2/users/kaile/hantao/verina/eval_case_study_20260506.md:34).
- Verina also observed cases where individual specs pass but the joint check fails in [eval_case_study_20260506.md](/mnt2/users/kaile/hantao/verina/eval_case_study_20260506.md:177).

Recommendation:

Add three independent gates:

- `build_gate`: `lake build` or targeted `lake env lean`.
- `local_target_gate`: target theorem has no `sorry` and no unresolved goals.
- `placeholder_status`: report placeholder definitions, weakened theorem statements, conclusion-as-hypothesis, and trivial typeclass witnesses.

A patch should not be marked complete unless all three pass, or the report explicitly says which gate failed.

### 3. Add anti-cheat checks for semantic placeholders

Source anchors:

- Current FloatSpec prompt bans `axiom`, `admit`, `pure true`, and trivial `decide True` forms in [scripts/subagent_prompt.md](/mnt2/users/kaile/hantao/verina/FloatSpec/scripts/subagent_prompt.md:32).
- Verina++ anti-cheat work identified hollow typeclass instances such as `LT Float := fun _ _ => True` in `repo-level-vcg-pipeline-pr/plan/20260504-203000-eval-anticheat.md`.

Recommendation:

Extend the forbidden-pattern scanner beyond literal `sorry`/`axiom`:

- Typeclasses with only `True` fields.
- Predicates defined as `True`.
- Operations returning a fixed argument or constant value while comments say "placeholder".
- Check functions changed to constants to satisfy placeholder conversions.
- Theorems whose precondition includes their postcondition.
- High-priority or shadowing instances.
- Any public theorem proving `True`, unless the Coq source theorem is genuinely trivial.

This should run over diffs and over the current repo to classify existing debt.

### 4. Introduce a nontriviality classifier

Source anchors:

- Verina's nontriviality analysis distinguishes trivial proof bodies from real reasoning in [nontrivial_spec_success_20260506.md](/mnt2/users/kaile/hantao/verina/nontrivial_spec_success_20260506.md:11).

Recommendation:

Classify completed FloatSpec proofs as:

- `definitional`: `intro`, `simp`, `rfl`, direct unfold.
- `routine`: local algebra, `rw`, `ring`, simple cases.
- `structural`: induction, strong recursion, case splits over format/rounding, helper lemma factoring.
- `semantic`: proves or uses a core Flocq property such as spacing, DN/UP maximality, ULP stability, monotonicity.

This helps avoid mistaking a high count of direct-computation proofs for progress on the hard foundation.

### 5. Add joint consistency checks for shared definitions

Source anchors:

- Verina codeproof mode has an extra joint consistency burden; all individual specs can pass while the joint result fails in [eval_case_study_20260506.md](/mnt2/users/kaile/hantao/verina/eval_case_study_20260506.md:177).

Recommendation:

For FloatSpec, "joint consistency" means:

- A local theorem proof did not weaken a shared definition.
- A theorem statement still matches the intended Coq theorem or an explicitly documented Lean adaptation.
- No upstream helper was made trivial to unblock a downstream proof.
- Existing nearby theorems still mean the same thing after edits.

Implement this as a statement-diff and definition-diff gate:

- If a `def`, `class`, or theorem statement changes, require a `COQ_ALIGNMENT.md` note or an explicit audit entry.
- Forbid changing a theorem statement in the same patch that claims to prove it, unless the target is "repair incorrect statement" and the report says so.

### 6. Replace free-form status markdown with generated status

Source anchors:

- Verina reports aggregate failure classes and status counts in [eval_case_study_20260506.md](/mnt2/users/kaile/hantao/verina/eval_case_study_20260506.md:40) and [sweep_results_snapshot.md](/mnt2/users/kaile/hantao/verina/sweep_results_snapshot.md:9).

Recommendation:

Generate a `status.json` and `status.md` for FloatSpec:

```json
{
  "lean_files": 61,
  "sorry_count": 388,
  "axiom_count": 1,
  "placeholder_semantics_count": 0,
  "spec_weakened_count": 0,
  "by_module": {
    "Core": {"sorry": 38, "placeholder": 0},
    "Prop": {"sorry": 239, "placeholder": 0},
    "Pff": {"sorry": 108, "placeholder": 0}
  }
}
```

The placeholder/spec-weakened counts should come from a curated classifier, not just `rg`.

### 8. Make "blocked" a valid successful outcome

Source anchors:

- Verina evaluation distinguishes build failure, unfilled slots, joint failure, and other failure classes rather than flattening all failures in [eval_case_study_20260506.md](/mnt2/users/kaile/hantao/verina/eval_case_study_20260506.md:40).

Recommendation:

When a theorem depends on an unported foundational lemma, the agent should produce a blocker report rather than inventing a local placeholder.

Blocked report template:

```markdown
Target: `FloatSpec/src/Core/Ulp.lean:2526`
Needed theorem: ULP stability of nearest-rounding result
Why current proof cannot close: DN/UP spacing and midpoint bucket lemmas are absent
Do not solve by: private axiom, adding conclusion as hypothesis, weakening rounding mode
Next prerequisite target: `consecutive_scaled_mantissas_ax`
```

This makes dependency ordering explicit and prevents low-quality "green" proofs.

## Proposed Pipeline Stages

1. **Inventory**
   - Count `sorry`, `axiom`, placeholders, statement changes, and imports.
   - Classify modules by placeholder and proof status.

2. **Target Selection**
   - Pick one theorem or one semantic placeholder.
   - Require a dependency check before editing.

3. **Source Alignment**
   - Link the Coq theorem or explain why no direct Coq counterpart applies.
   - Record required hypotheses, especially `1 < beta`, monotonic exponent, and valid rounding assumptions.

4. **Patch**
   - Allow helper lemmas.
   - Forbid semantics-weakening changes.
   - Avoid broad statement rewrites.

5. **Validation**
   - Run build.
   - Run forbidden-pattern scanner.
   - Run statement-diff checker.
   - Run dependency and placeholder-status checkers.

6. **Report**
   - Emit `attempt.json`.
   - Update generated status.
   - If blocked, emit prerequisite target instead of a fake proof.

## Immediate Tooling To Build

- `scripts/audit_placeholders.sh`
  - Search for `:= True`, `fun _ _ => True`, "placeholder", "always returns", "mode is ignored", and conclusion-as-hypothesis patterns.

- `scripts/status_report.sh`
  - Emit counts by module family.

- `scripts/audit_placeholders.sh`
  - Fail on new `sorry`, `axiom`, `admit`, public `def ... := True`, identity stubs, or theorem statement changes without an allowlist.

- `scripts/classify_attempt.py`
  - Convert build logs, diff scans, and target metadata into `attempt.json`.

- unified build/status documentation
  - Maintain the current placeholder/status classification.

## Practical Policy Changes

- Do not call a theorem "done" if it depends on a private `sorry` bridge introduced for that theorem.
- Do not repair an unprovable theorem by adding the postcondition to the precondition.
- Do not prove IEEE or Pff correctness against identity/constant placeholder operations unless the theorem name clearly says it is placeholder-only.
- Treat mode-erased rounding as a repository-wide blocker for nearest/directed/IEEE mode results.
- Prefer honest `sorry` plus blocker report over a compiling theorem with weakened semantics.

## Expected Outcome

With these changes, FloatSpec can still use agents aggressively, but the output becomes auditable. The pipeline will distinguish:

- Real proof progress.
- Useful scaffold preservation.
- Known blockers.
- Placeholder-only compatibility.
- Unsound or misleading proof repairs.

That distinction is the main lesson from Verina++: successful verification work needs strict evaluation artifacts, not just successful compilation.
