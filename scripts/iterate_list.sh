#!/usr/bin/env bash
set -euo pipefail
export ANTHROPIC_LOG=debug

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
  # Ulp.lean
  # Round_pred.lean
  # Generic_fmt.lean
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
  12
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
# Always Works™ Prompt

## Task

Fix proofs / theorems in `FloatSpec/src/Core/__PLACEHOLDER__`.

## Goal

Repair **exactly one** theorem: the **first** theorem mentioned in /data/hantao/FloatSpec/FloatSpec/src/Core/Status.md that could be handled right now and lacks a full proof (due to `sorry`, errors, or unsolved goals). Deliver a clean `lake build` with **no new breakages** introduced and no `sorry`, errors, and unsolved goals in the target theorem.

---

## Selection Rule (deterministic, do it step-by-step)

0. You should stick to this rule tightly, and do not consider other factors in the selection process. On any step, if you find a valid target, stop, do not look into later steps or think too much; go straight to the proving process and spend your thoughts there.
1. Run `lake build` and capture logs.
2. Compare the logs and the corresponding code files with the record in /data/hantao/FloatSpec/FloatSpec/src/Core/Status.md. Check if they are currently aligned with the update rules. If there are misalignments, update the status file to reflect the current state.
3. Read the updated /data/hantao/FloatSpec/FloatSpec/src/Core/Status.md carefully and select the **first** theorem that is marked as `in progress` (just search for `- Status: in progress` and grab the first match). This should be an exact match, and DO NOT pick the one with `could not be finished now` at this stage. If you find corresponding theorem in the status file, go to prove it.
4. When the previous steps cannot find any valid target, read the updated /data/hantao/FloatSpec/FloatSpec/src/Core/Status.md carefully and select the **first** theorem that is marked as `unfinished` (just search for `- Status: unfinished` and grab the first match). If you find corresponding theorem in the status file, go to prove it.
5. When the previous steps cannot find any valid target, pick the **first** theorem that is not marked as `finished` and is either in `could not be finished now` or other state. Work hard and attempt to prove it.
6. If none of the previous case are detected, write a short report explaining what you checked and **stop**.

> “First” always means **smallest line number** in the target file.

---

## Prerequisites (read first)

* `FloatSpec/PIPELINE.md` (overall pipeline)
* `./CLAUDE.md` (proof-writing conventions and `mvcgen` info)

---

## Process (ONE-BY-ONE, compile after each step)

1. **Identify target** using the Selection Rule and record the exact line number and reason (error/sorry/unsolved goals).
2. **Understand spec & code**

  * Read the 'Reason' in this theorem’s Status.md entry.
   * Read the Coq original in `/home/hantao/code/flocq/src/Core` (if available).
  * Verify the definition body (if relevant) matches intent and source (Coq).
  * Review the local spec/Hoare triples and nearby lemmas.
3. **Plan**: decide whether to prove directly or factor helper lemmas (preferred for long proofs).
4. **Draft Implement**

   * Add minimal helper lemmas (use `private` or local `namespace`).
   * Follow house style; use `Zaux.lean`’s `Zfast_div_eucl_spec` and in-file patterns as templates.
   * Do not attempt to skip or bypass the proof: `axiom`, `admit`, `pure true`, or any placeholder (including `sorry`, `pure (decide True)`, `pure (decide ((0 : ℝ) ≤ 0))`, and all variants which could be easily deducted to a `True`) are strictly forbidden.
5. **Compile**: `lake build` immediately after the change.

   * Fix all reported errors before making more changes.
6. **Check Implement**: review your changes to ensure no forbidden placeholders were introduced. To be specific:
    * Search the diff for `axiom`, `admit`, `pure true`, `pure (decide True)`, `pure (decide ((0 : ℝ) ≤ 0))`, and all variants which could be easily deducted to a `True`.
    * If you find any of these placeholders, revert all the related changes and work from beginning.
    * If the search did not find any of these placeholders, apply the patch and proceed to the next step.
    * Search the diff for `sorry`. If you find any sorry, continue to work on it until there is no sorry left in the diff.
    * If you did not find any sorry in the diff, proceed to the next step.
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
* Start a complex fix of a certain proof, despite the risk of failure, if you have a clear plan and the Coq source as a guide.
* Move the target theorem to a different location in the file (e.g., closer to related lemmas or later than some required lemmas) if it helps your workflow.

**Prohibited**

* Remove theorems or functions. DO NOT DIRECTLY REMOVE ANYTHING!!!! In order to move a theorem, you should first copy the theorem to the new location, then delete the old one for the sake of replication. Besides the sake of replication, nothing should be directly removed. You should never directly delete or remove a theorem or function with the excuse of moving it.
* The dependency cycle is strictly forbidden in lean4. So do not attempt to include any import that causes a dependency cycle. If you need a definition from another file, check if the import will cause a dependency cycle; if so, do not reorder and check the Coq original source and use the proof Strategy from there.
* Deleting any existing theorems/functions.
* Using `axiom`, `admit`, `pure true`, or any non-`sorry` placeholder, including `pure (decide True)`, `pure (decide ((0 : ℝ) ≤ 0))`, and all variants which could be easily deducted to a `True`. If you see such placeholders, replace them with `sorry` instead.
* Expanding scope beyond the **single selected** target.
* Broad spec rewrites or syntax changes to Hoare triples (unless strictly required by the Coq source and documented).
* Use `complex proof` as an excuse for doing no action. Instead, you should do whatever you are able to - moving theorems to avoid dependency issues, create local lemmas which does not exist previously (and you need them to prove the target theorem), etc. The goal is to reduce the gap as much as possible.
* It is strictly forbidden to revert any previous changes through git commands. YOU SHOULD NEVER, EVER REVERT ANY PREVIOUS CHANGES THROUGH GIT COMMANDS. If you find any previous changes are problematic, you should fix them through new patches instead of reverting them. Reverting with git often revert other unexpected (and beneficial) changes, which could cause more problems.

---

## If the Theorem/Spec Seems Wrong

1. Compare with the original Coq statement/proof in `/home/hantao/code/flocq/src/Core`.
2. If a mismatch **blocks** the Lean proof:

   * Update the Lean statement **minimally** to match the Coq intent.
   * Port the relevant argument/structure from Coq.
   * **Record every change** in the change log with justification and Coq references.

---

## Proof Strategy Guidelines

* Do not overthink! If you think some tactic or approach seems promising, implement and test it instead of over-planning. But do obey the rules in the prompt.
* Some theorems lack a pre-condition `1 < beta`—if needed, add it (Coq reference required). But you have to press all related errors to make compile pass safely.
* Prefer no decomposition and moving operations: Try your best to prove the theorem directly through trial and error. Only if you are completely stuck, factor out small helper lemmas. Aviod replacing a single sorry with multiple sorries that you are UNCERTAIN about the correctness.
* Use existing proven lemmas from imports, existing files and `mathlib4` where available; if uncertain, search first, otherwise implement locally.
* Keep terms and rewriting explicit; avoid fragile tactic scripts.
* Preserve existing notation and Hoare triple syntax whenever possible.
* Trying is encouraged: if a tactic or approach seems promising, implement and test it instead of over-planning.
* You are allowed to move theorems: When you observe that the target theorem depends on some lemmas that are defined later in the file, you can move the target theorem to a different location in the file (e.g., closer to related lemmas or later than some required lemmas) if it helps your workflow. If you do reorder, YOU MUST MAKE SURE THAT THE DEPENDENCY IS error-safe after your move (or else you could make other moves first to ensure that), then document it. If the dependency you need is in another file, check if the import will cause a dependency cycle; if so, do not reorder and check the coq original source and use the proof Strategy from there.

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

Update the change status file `/data/hantao/FloatSpec/FloatSpec/src/Core/Status.md`:
Compile again. Double check the log and the proof body itself:
If the full proof is completed (which means no sorry in its proof and the helper lemmas you added), change the 'Status' to `finished` for the target theorem. You should be extremely cautious to ensure that the proof is indeed complete before changing the status to `finished`. (which means at least double-check).
If you could not finish the full proof, but you made some progress, update the 'Status' to `in progress` or `could not be finished now` (choose one that best describes the current state) for the target theorem. If you did not make any progress on the target theorem, do not change its status.
Specifically, if your attempts on the target theorem is more than 3, you should change the 'Status' to `could not be finished now` for the target theorem. 

Update the 'Reason' to reflect the current state (e.g., `Made an task list, among them A, B, C is finished, and next we should focus on D, E, F`, `in progress: lemma X added`, `fixed error: ...`, `could not be finished now: ...`). If the 'Status' is changed to `finished`, the 'Reason' must explain how the proof was completed, referencing Coq source lines where relevant. 

Update the 'Attempt' to log the number of attempts you made on this theorem. If this is your first attempt, set it to 1. If you have made previous attempts, increment the count by 1.

Update the theorems: If you add any new helper lemmas, add them to the Status.md file with correct line numbers, 'Status', ''Reason', and 'Attempt' fields. If you move the target theorem to a different location in the file, update its line number accordingly.

---

## Practical Tips

* Be determined and persistent: Do not overthink or overplan on selection or proof strategy. If you think some tactic or approach seems promising, implement and test it instead of over-planning. But do obey the rules in the prompt.
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
  # cmd=(claude -p "$msg" --dangerously-skip-permissions)

  end=$(( $(date +%s) + t*60*60 ))
  while [[ $(date +%s) -lt $end ]]; do
    # if [[ -n "$TIMEOUT_BIN" ]]; then
    #   "$TIMEOUT_BIN" 10800 "${cmd[@]}" || true
    # else
    #   "${cmd[@]}" || true
    # fi
    "${cmd[@]}" || true
    git add .
    timestamp=$(date +%Y%m%d_%H%M%S)
    git commit -m "Update $f at $timestamp after an agent round" || true
  done
done