#!/usr/bin/env bash
set -euo pipefail

# Use GNU timeout if available; on macOS prefer gtimeout (coreutils)
TIMEOUT_BIN="${TIMEOUT_BIN:-timeout}"
command -v "$TIMEOUT_BIN" >/dev/null 2>&1 || TIMEOUT_BIN="gtimeout"
if ! command -v "$TIMEOUT_BIN" >/dev/null 2>&1; then
  echo "warning: timeout/gtimeout not found; running without a time limit" >&2
  TIMEOUT_BIN=""
fi

# Files to process and per-file run time (in hours)
file_list=(
#   Float_prop.lean
#   Raux.lean
  # FIX.lean
  # FLT.lean
  # FLX.lean
  # FTZ.lean
  # Round_NE.lean
  Ulp.lean
  # Round_pred.lean
)
hours=(
#   2
#   2
  # 4
  # 3
  # 3
  # 2
  # 2
  # 3
  6
)

# Sanity check: arrays must match
if [[ ${#file_list[@]} -ne ${#hours[@]} ]]; then
  echo "error: file_list and hours length mismatch" >&2
  exit 1
fi

# Iterate over indices of file_list
for i in "${!file_list[@]}"; do
  f="${file_list[$i]}"
  t="${hours[$i]}"

  # Build the multi-line prompt literally, no expansions.
  # NOTE: The line with EOF must be at column 1 with no trailing spaces/tabs.
  # The '|| true' prevents 'set -e' from exiting because read -d '' returns 1 at EOF.
  IFS= read -r -d '' msg <<'EOF' || true
Here’s a tighter, more deterministic version you can drop in as a system/task prompt.

# Always Works™ Prompt

## Task

Fix proofs / theorems in `FloatSpec/src/Core/__PLACEHOLDER__`.

## Goal

Repair **exactly one** item: the **first** theorem in the target file that lacks a full proof (due to `sorry`, errors, or unsolved goals). Priority: errors > sorry. Deliver a clean `lake build` with **no new breakages** introduced.

---

## Selection Rule (deterministic)

0. Find the latest log in `.change_log/` (by timestamp). Read the log and indentify if there are unfinished target left behind. If this target belongs to the current file or the dependencies of the current file (i.e. without fixing this error, current file can never be built), continue to work on it. If not, proceed to step 1.
1. Run `lake build` and capture logs.
2. Search for all `error` inside the log file. If the build reports any **error** inside the target file, choose the error with the **smallest line number**; the associated theorem is your target. If the build is blocked by errors in other files, fix those first (they may be dependencies).
3. Otherwise, search the file for the first `sorry` (by line number).

   * If that `sorry` is **inside a `def`/function body**, locate the original Coq source in `/home/hantao/code/flocq/src/Core`, port the definition to Lean 4, and then prove the corresponding theorems. Do not use `pure true` or any placeholder in the definition.
4. If there is **no** error and **no** `sorry` in the file, go through the file to examine non-`sorry` placeholder in the definition of functions or specs, including `pure (decide True)`, `pure (decide ((0 : ℝ) ≤ 0))`, and its variants which could be easily deducted to a `True`. If you find any of these placeholders, locate the original Coq source in `/home/hantao/code/flocq/src/Core`, port the definition to Lean 4 to replace original placeholder, and then prove the corresponding theorems.
5. If none of the previous case are detected, write a short report explaining what you checked and **stop**.

> “First” always means **smallest line number** in the target file.

---

## Prerequisites (read first)

* `FloatSpec/PIPELINE.md` (overall pipeline)
* `./CLAUDE.md` (proof-writing conventions and `mvcgen` info)

---

## Process (ONE-BY-ONE, compile after each step)

1. **Identify target** using the Selection Rule and record the exact line number and reason (error/sorry/unsolved goals).
2. **Understand spec & code**

   * Verify the definition body (if relevant) matches intent and source (Coq).
   * Review the local spec/Hoare triples and nearby lemmas.
3. **Plan**: decide whether to prove directly or factor helper lemmas (preferred for long proofs).
4. **Draft Implement**

   * Add minimal helper lemmas (use `private` or local `namespace`).
   * Follow house style; use `Zaux.lean`’s `Zfast_div_eucl_spec` and in-file patterns as templates.
   * Do not attempt to skip or bypass the proof: `axiom`, `admit`, `pure true`, or any non-`sorry` placeholder (including `pure (decide True)`, `pure (decide ((0 : ℝ) ≤ 0))`, and all variants which could be easily deducted to a `True`) are strictly forbidden.
5. **Check Implement**: review your changes to ensure no forbidden placeholders were introduced. To be specific:
    * Search the diff for `axiom`, `admit`, `pure true`, `pure (decide True)`, `pure (decide ((0 : ℝ) ≤ 0))`, and all variants which could be easily deducted to a `True`.
    * If you find any of these placeholders, revert all the related changes and work from beginning.
    * If the search did not find any of these placeholders, apply the patch and proceed to the next step.
6. **Compile**: `lake build` immediately after the change.

   * Fix all reported errors before making more changes.
7. **Polish**: refactor only if it **reduces** proof fragility and aligns with the Coq source.
8. **Log**: update the change log (see “Change Log & Reporting”).

> Never batch multiple risky edits. Build early, build often.

---

## Allowed vs. Prohibited Changes

**Allowed (with restraint)**

* Be persistent: The calling process is single-rounded, so try your best to close the target, or at least leave behind useful, compiling helper lemmas (or comments) that reduce the remaining gap.
* Introduce small, well-named helper lemmas.
* Reorder theorems **only** to resolve clear dependency cycles—and log it.
* Minimal spec tweaks **only if** the Coq original demands it (see below).

**Prohibited**

* The dependency cycle is strictly forbidden in lean4. So do not attempt to include any import that causes a dependency cycle. If you need a definition from another file, check if the import will cause a dependency cycle; if so, do not reorder and check the Coq original source and use the proof Strategy from there.
* Deleting any existing theorems/functions.
* Using `axiom`, `admit`, `pure true`, or any non-`sorry` placeholder, including `pure (decide True)`, `pure (decide ((0 : ℝ) ≤ 0))`, and all variants which could be easily deducted to a `True`. If you see such placeholders, replace them with `sorry` instead.
* Expanding scope beyond the **single selected** target.
* Broad spec rewrites or syntax changes to Hoare triples (unless strictly required by the Coq source and documented).

---

## If the Theorem/Spec Seems Wrong

1. Compare with the original Coq statement/proof in `/home/hantao/code/flocq/src/Core`.
2. If a mismatch **blocks** the Lean proof:

   * Update the Lean statement **minimally** to match the Coq intent.
   * Port the relevant argument/structure from Coq.
   * **Record every change** in the change log with justification and Coq references.

---

## Proof Strategy Guidelines

* Prefer decomposition: prove small lemmas, then assemble.
* Use existing proven lemmas from imports and `mathlib4` where available; if uncertain, search first, otherwise implement locally.
* Keep terms and rewriting explicit; avoid fragile tactic scripts.
* Preserve existing notation and Hoare triple syntax whenever possible.
* Trying is encouraged: if a tactic or approach seems promising, implement and test it instead of over-planning.
* Some theorems lack a pre-condition `1 < beta`—if needed, add it (Coq reference required).

---

## Compilation & Completion Criteria

* After **every** change: run `lake build` (capture logs).
* **Definition of Complete** for this task:

  * The selected target theorem is fully proven (no `sorry`, no `axiom` or other placeholders, no unsolved goals).
  * The repository compiles cleanly (errors = 0).
  * No unrelated theorems were altered, deleted, or broken.
* Warnings may remain; do **not** chase them unless they block the proof.

---

## Change Log & Reporting (mandatory)

Append an entry to a markdown file (e.g., `.change_log/$timestamp.md`) with:

```
## File: FloatSpec/src/Core/__PLACEHOLDER__
- Target: <theorem/def name> at line <n>
- Reason picked: <error|sorry|unsolved goals>
- Approach: <direct proof | helper lemmas (list) | ported from Coq (list)>
- Changes:
  - [ ] Definition modified? (yes/no). If yes, minimal diff + reason.
  - [ ] Spec modified? (yes/no). If yes, minimal diff + Coq reference path.
  - [ ] Reordering done? (yes/no). If yes, explain dependency.
- Coq reference(s): /home/hantao/code/flocq/src/Core/<file>.v : <lines/lemma names>
- Build: <command used> | <log file path>
- Notes: pitfalls, invariants, future useful lemmas (if any)
```

If the file had no target (no errors, no `sorry`), write a brief “No-action report”.

---

## Practical Tips

* Save build output to a log and search it instead of scrolling:

  * Example: `lake build 2>&1 | tee .log/$(date +%Y%m%d_%H%M%S)_build.log`
* When adding lemmas, colocate near the target or in a `private` section to avoid polluting the API.
* If a `def` is `sorry` and the function is hard to realize: inline the needed facts into the theorem (as in the Coq proof), **clear** the `def`’s `sorry` via a correct implementation or restructure to avoid relying on a bogus placeholder—then prove the theorem.
* Look for definition in the imports and opens before actually implementing it. If the definition is already in the imports or opens, just use it directly and aviod duplicate definition.
* Change order within file is permitted only to resolve dependency cycles. If you do reorder, document it. If the dependency you need is in another file, check if the import will cause a dependency cycle; if so, do not reorder and check the coq original source and use the proof Strategy from there.

---

## Recap Checklist (ALL must be checked and achieved before you stop)

* [ ] Applied Selection Rule; recorded line+reason.
* [ ] Read PIPELINE/CLAUDE docs.
* [ ] Implemented proof (or minimal Coq-aligned spec tweak).
* [ ] No `axiom`/`admit`/`pure true`; no new `sorry`. Check by searching the diff to make sure you did not introduce any of these. If you did introduce any of these, revert all the related changes and work from beginning.
* [ ] `lake build` succeeds without error.
* [ ] Change log entry added with Coq references.

**Be persistent.** If you can’t close the main target within this session, leave behind **useful, compiling helper lemmas** that clearly reduce the remaining gap—and document them in the change log.

EOF

  # Replace the placeholder with the actual file name
  msg=${msg//__PLACEHOLDER__/$f}

  # Build the CLI command as an array to preserve spaces/newlines
  # NOTE: Keep your original flags; remove the stray 'high' token if not supported.
  cmd=(codex exec "$msg" --dangerously-bypass-approvals-and-sandbox)

  end=$(( $(date +%s) + t*60*60 ))
  while [[ $(date +%s) -lt $end ]]; do
    if [[ -n "$TIMEOUT_BIN" ]]; then
      "$TIMEOUT_BIN" 7200 "${cmd[@]}" || true
    else
      "${cmd[@]}" || true
    fi
  done
done