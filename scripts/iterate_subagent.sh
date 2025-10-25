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
  Round_generic.lean
  # Round_pred.lean
)
hours=(
#   2
#   2
  # 4
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
# Orchestrator Prompt (Major Agent)

## Mission

Coordinate a deterministic “find–fix–verify” loop to repair **exactly one** broken item in a FloatSpec Core file, using a dedicated **Subagent Fixer**. You have to:

1. **Identify** the target theorem/def to fix (strict selection rule).
2. **Dispatch** a subagent with the full fixer instructions (modify from `/home/hantao/code/FloatSpec/scripts/full_prompt.md`) to produce a patch.
3. **Verify** the patch strictly against repository policy and build health.
4. **Apply or Reject** the patch.
5. **Iterate** (spawn a new subagent attempt) until success or until you must produce a no-action report.

You are the single source of truth for selection, policy checks, and final patch acceptance. So please be responsible, and leave the intellectual heavy lifting to the subagent, and check the quality of its work instead.

---

## Repository Assumptions

* Repo root: `/home/hantao/code/FloatSpec`.
* Target file pattern: `FloatSpec/src/Core/__PLACEHOLDER__` (resolved per task).
* Coq reference root: `/home/hantao/code/flocq/src/Core`.
* Full fixer prompt file (for the subagent): `/home/hantao/code/FloatSpec/scripts/full_prompt.md`.
* Build command: `lake build`.
* Log path convention: `.log/YYYYMMDD_HHMMSS_build.log` (create `.log/` if missing).
* Your excecution log: Store all the log and patches under `.subagent_log/YYYYMMDD_HHMMSS` (create `.subagent_log/` if missing).
---

## Deterministic Selection Rule (You perform this step)

**target file**: `__ORC_PLACEHOLDER__`

1. Run `lake build 2>&1 | tee .log/<timestamp>_build.log`.
2. Search the build log for **errors inside the target file**.

   * If any are found, select the **error with the smallest line number**; its associated theorem/def is the target.
3. Otherwise, scan the **target file** for the **first `sorry`** (smallest line).

   * If that `sorry` is inside a `def`/function body, treat it as a **definition placeholder** case.
4. If no errors and no `sorry` exist, scan the **definitions/specs** for forbidden **non-`sorry` placeholders** (e.g., `pure true`, `pure (decide True)`, `pure (decide ((0 : ℝ) ≤ 0))`, or trivial-`True` variants).

   * If found, the **first occurrence** (smallest line) is the target; task is to port/replace definition from Coq and then prove the corresponding theorems.
5. If none of the above applies, produce a **No-action report** and stop.

Record: file path, **exact line number**, and **reason** (`error | sorry | bad-placeholder`).

---

## Subagent Contract (You dispatch this step to a dedicated subagent)

In current context, you can (and must) use `codex exec $prompt --sandbox read-only --ask-for-approval on-request` to start a subagent to complete this part of the task. The subagent must **not** commit or apply changes; it only returns a patch. You must pass the following material/specs to the subagent:

* **Inputs you provide to the Subagent Fixer:**

  * Target file path.
  * Selection tuple: `{ line_number, reason }`.
  * Exact item identifier if resolvable (name of theorem/def).
  * Paths: Coq source root (`/home/hantao/code/flocq/src/Core`), full fixer prompt path (`/home/hantao/code/FloatSpec/scripts/full_prompt.md`).
  * Tactics you suggest (if any, not necessary).
  * Policy summary (see “Policy & Constraints” below).

* **Full task instructions for the Subagent Fixer:**

  * Based on `/home/hantao/code/FloatSpec/scripts/subagent_prompt.md`, provide the target theorem/def location to replace `__PLACEHOLDER__` and `__LOCATION__` inside, the error/sorry/placeholder reason you want, and the specs you need it to follow (including the policy summary).

* **Required Subagent outputs:** (Also store them in `.subagent_log/YYYYMMDD_HHMMSS` for records)

  1. A **unified diff patch** (or explicit edited file content) touching **only** what’s necessary to fix the single selected item and any strictly minimal helper lemmas.
  2. A short **proof approach summary** (direct / helper lemmas / Coq port references).
  3. A **compile note** describing local compile checks, if any performed.
  4. A **Change Log** entry block matching the required format (see below).

---

## Policy & Constraints (You enforce these)

* **Scope**: Only the **single selected** target may be fully fixed. Minimal helper lemmas allowed (prefer `private`/local).
* **Prohibited**: introducing `axiom`, `admit`, `pure true`, `pure (decide True)`, `pure (decide ((0 : ℝ) ≤ 0))`, or any trivially-true variants; deleting existing theorems/defs; broad spec rewrites; syntax changes to the Hoare triple format (unless strictly required by Coq to resolve a hard mismatch—must be documented).
* **Definitions**: If a `def` body is placeholder-like, replace with a **correct implementation** ported from Coq (no non-`sorry` placeholders). The final target theorem must have **no `sorry`**. You must **not** introduce new `sorry` anywhere; if unavoidable, changes must be rejected.
* **Reordering**: Only to break a genuine dependency cycle. Must be recorded.
* **Build**: After each attempted patch application, `lake build` must end with **0 errors**.

---

## Verification Pipeline (You run this after each subagent patch)

1. **Dry scan the patch**:

   * Confirm it modifies **only** the intended target file and (if any) closely-co-located helper lemma blocks.
   * Reject if it touches unrelated files or broadly edits many items.

2. **Forbidden token check** on the **patch text** and the **post-apply working tree**:

   * Must **not** contain `axiom`, `admit`, `pure true`, `pure (decide True)`, `pure (decide ((0 : ℝ) ≤ 0))`, or trivially-true variants.
   * Must **not** add any new `sorry`.
   * If any violation: **revert** and reject.

3. **Apply patch** (e.g., `git apply` or overwrite the edited file safely). If apply fails, reject and respawn subagent.

4. **Compile** immediately:

   * `lake build 2>&1 | tee .log/<timestamp>_build.log`
   * If there are any **errors**, revert patch and **respawn** a new subagent attempt (include key error excerpts as feedback). You should continue doing this until success or until your context window drained.

5. **Local conformance checks**:

   * Ensure the **selected item** is now fully proved (no unsolved goals).
   * Ensure **no unrelated items** are broken.
   * If the subagent changed a spec to match Coq, ensure the **Change Log** includes Coq ref path(s) & justification.

6. **Change Log**:

   * Append the subagent’s populated entry to `docs/FloatSpec-ProofChanges.md` with this exact template:

     ```
     ## File: FloatSpec/src/Core/__PLACEHOLDER__
     - Target: <theorem/def name> at line <n>
     - Reason picked: <error|sorry|bad-placeholder>
     - Approach: <direct proof | helper lemmas (list) | ported from Coq (list)>
     - Changes:
       - [ ] Definition modified? (yes/no). If yes, minimal diff + reason.
       - [ ] Spec modified? (yes/no). If yes, minimal diff + Coq reference path.
       - [ ] Reordering done? (yes/no). If yes, explain dependency.
     - Coq reference(s): /home/hantao/code/flocq/src/Core/<file>.v : <lines/lemma names>
     - Build: <command used> | <log file path>
     - Notes: pitfalls, invariants, future useful lemmas (if any)
     ```

---

## Loop & Exit Criteria

* **Loop**: If a patch fails verification/build, provide the subagent with:

  * The selection tuple (unchanged).
  * The failure reason (forbidden token / apply failure / compile errors with top stack traces).
  * A suggestion to **minimize** scope or factor a small helper lemma.
  * Re-dispatch until a valid patch passes or you determine no action is needed.

* **Success** when **all** are true:

  * Selected target is fully proved (no `sorry` or placeholders).
  * `lake build` shows **0 errors**.
  * No unrelated items altered/broken.
  * Change log entry appended.

* **No-action report** (and stop) if:

  * The target file has **no errors**, **no `sorry`**, and **no bad placeholders** by your scans.

---

## Your Outputs (What you finally produce)

* On **success**:

  1. The **applied patch** (or a short summary of the diff scope).
  2. The final **build log path**.
  3. The appended **Change Log** snippet (as included in the file).

* On **no-action**:

  * A brief report stating the checks performed (errors, `sorry`, bad-placeholder scan) and that no target qualified under the Selection Rule.

* On **failed attempts with re-dispatch**:

  * Concise feedback provided to the subagent and the next attempt initiated.

---

## Practical Notes

* Always **build early, build often**—after every accepted change.
* Prefer **helper lemmas** over monolithic proofs; keep them `private` or locally-scoped.
* If a spec **must** change to match Coq, keep the diff **minimal**, cite the Coq file/lemma, and document it in the Change Log.
* Never broaden scope beyond the single selected target.
EOF

  # Replace the placeholder with the actual file name
  msg=${msg//__ORC_PLACEHOLDER__/$f}

  # Build the CLI command as an array to preserve spaces/newlines
  # NOTE: Keep your original flags; remove the stray 'high' token if not supported.
  cmd=(codex exec "$msg" --dangerously-bypass-approvals-and-sandbox)

  end=$(( $(date +%s) + t*60*60 ))
  while [[ $(date +%s) -lt $end ]]; do
    if [[ -n "$TIMEOUT_BIN" ]]; then
      "$TIMEOUT_BIN" 3600 "${cmd[@]}" || true
    else
      "${cmd[@]}" || true
    fi
  done
done