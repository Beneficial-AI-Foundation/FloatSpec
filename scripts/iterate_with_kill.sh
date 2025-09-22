#!/usr/bin/env bash
set -euo pipefail

# ========== Config ==========
# Hourly kill interval; override with env if desired (seconds)
KILL_INTERVAL="${KILL_INTERVAL:-3600}"
# Grace period (seconds) between SIGTERM and SIGKILL
KILL_GRACE="${KILL_GRACE:-10}"

# ========== timeout utility detection ==========
# Use GNU timeout if available; on macOS prefer gtimeout (coreutils)
TIMEOUT_BIN="${TIMEOUT_BIN:-timeout}"
command -v "$TIMEOUT_BIN" >/dev/null 2>&1 || TIMEOUT_BIN="gtimeout"
if ! command -v "$TIMEOUT_BIN" >/dev/null 2>&1; then
  echo "warning: timeout/gtimeout not found; running without a time limit" >&2
  TIMEOUT_BIN=""
fi

# ========== Helper: timestamped log ==========
ts() { date +"[%Y-%m-%d %H:%M:%S]"; }

# ========== Background killer ==========
start_killer() {
  local self_pid="$1"
  local killer_pid="$$" # this function runs in subshell; after backgrounding, $$ is killer's pid

  # Prefer pkill/pgrep if present; fallback to ps+awk
  have_pgrep=0
  command -v pgrep >/dev/null 2>&1 && have_pgrep=1

  list_pids() {
    # args: pattern
    local pat="$1"
    if [[ $have_pgrep -eq 1 ]]; then
      # -f: match against full command line
      # Filter out self and killer
      pgrep -f -- "$pat" 2>/dev/null | awk -v spid="$self_pid" -v kpid="$killer_pid" '($0!=spid)&&($0!=kpid)'
    else
      # portable fallback
      # shellcheck disable=SC2009
      ps -ax -o pid= -o command= | awk -v pat="$pat" -v spid="$self_pid" -v kpid="$killer_pid" '
        index($0, pat) {
          pid=$1
          if (pid != spid && pid != kpid) print pid
        }'
    fi
  }

  kill_pattern() {
    # args: pattern
    local pat="$1"
    # First try a gentle TERM
    mapfile -t pids < <(list_pids "$pat" | sort -u || true)
    if ((${#pids[@]})); then
      echo "$(ts) Sending SIGTERM to ${#pids[@]} processes matching: $pat -> ${pids[*]}" >&2
      kill -TERM "${pids[@]}" 2>/dev/null || true
      sleep "$KILL_GRACE"
      # Re-check remaining
      mapfile -t remain < <(printf '%s\n' "${pids[@]}" | xargs -r ps -o pid= -p | awk '{print $1}' || true)
      if ((${#remain[@]})); then
        echo "$(ts) Escalating SIGKILL to ${#remain[@]} processes matching: $pat -> ${remain[*]}" >&2
        kill -KILL "${remain[@]}" 2>/dev/null || true
      fi
    else
      echo "$(ts) No processes found matching: $pat" >&2
    fi
  }

  echo "$(ts) Killer started (pid=$killer_pid). Interval=${KILL_INTERVAL}s, grace=${KILL_GRACE}s." >&2
  while :; do
    sleep "$KILL_INTERVAL" || true
    echo "$(ts) Hourly cleanup triggered." >&2
    # Kill processes whose command line contains 'codex' or 'lean'
    kill_pattern "codex"
    kill_pattern " lean "     # pad with spaces to avoid over-matching short substrings
    kill_pattern "/lean"      # common binary path pattern
    kill_pattern " lake build"  # catch lean builds
  done
}

# Launch killer in background (independent of main loop) and clean it up on exit
SELF_PID="$$"
start_killer "$SELF_PID" &
KILLER_BG_PID=$!
disown "$KILLER_BG_PID" 2>/dev/null || true
trap 'kill -TERM "$KILLER_BG_PID" 2>/dev/null || true' EXIT INT TERM

# ========== Build the multi-line prompt literally, no expansions ==========
# NOTE: The line with EOF must be at column 1 with no trailing spaces/tabs.
# The '|| true' prevents 'set -e' from exiting because read -d '' returns 1 at EOF.
IFS= read -r -d '' msg <<'EOF' || true
Please ensure your implementation Always Works™ for:

## Task: Fix Proofs in FloatSpec/src/Core/Float_prop.lean

## Scope

theorems: Fix the first (only the very first, work really hard on it and don't care about others) theorem without a full proof \(sorry and/or error and/or unsolved goals, whatever make the proof incomplete\) in the function. First locate the line number and the error type you need to fix using lake build (preferred) or MCP tool (the very first incomplete proof within the target file), then think in detail about the mistake, and work really hard to solve it. You can use exisiting lemma to assist your proof or create new private lemma to assist your proof. If you think the original theorem is inadequate, you might revise it, but in a very cautious way and record every those changes in a markdown file. 

### Prerequisites

1. **Read documentation first:**
    - FloatSpec/PIPELINE.md - understand the overall pipeline
    - ./CLAUDE.md - focus on proof writing instructions and mvcgen info

### Core Requirements

### Proof Writing Process

1. **Follow the Zfast_div_eucl_spec example** in Zaux.lean and other proofs in current file as your template
2. **ONE-BY-ONE approach is mandatory:**
    - Write ONE proof
    - Check immediately with `lake build`(preferred) or `mcp` 
    - Fix any errors before proceeding to next proof
    - Never batch multiple proofs without checking

### Before Writing Each Proof

1. **Verify function implementation** - ensure the function body is correct
2. **Check existing specs** - understand what needs to be proven
3. **Preserve syntax** - do NOT change hoare triple syntax unless absolutely necessary
    - Think multiple times before modifying specs or code body
    - If changes are needed, decompose complex specs rather than rewriting

### Compilation Verification

- **After EVERY proof:** Run `mcp` or `lake build xxx`(preferred)
- **Definition of complete:** NO `sorry` statements AND clean compilation
- **Never mark as complete if:**
    - Any `sorry` remains
    - Compilation returns errors

### Proof Strategy

1. **Handle all `sorry` statements and errors** in:
    - Function definitions
    - Specifications
    - Proofs
2. **When facing difficulties:**
    - Search for proof tactics using MCP tools
    - Trying to decompose the original theorem into lemmas and deal with them one by one.
    - If no tactics work, consider:
        - Reformatting the spec
        - Decomposing complex specs into simpler lemmas \(follow patterns in the file\)
    - Reference original proof comments for guidance
3. **Order of implementation:**
    - Choose your own order
    - Can switch mid-task if needed
    - Focus on completeness over speed

### Important Notes

- Use MCP tool instead of bash command to get diagnostic messages!
- Some functions ARE difficult to prove - persistence is expected
    - If you are meeting difficulties at least come up with some useful lemma that could compile and is helpful to future proofs before ending your session. Remember that!
- Skip already-proven theorems!! There might be warnings be just leave them there!
- You can use exisiting (and proved) theorem to assist your proving. If a theorem is necessary but not proved, you can turn to work on that first. The useful theorems might not be in the same file, but in the import list
- When you are trying to use a certain lemma, check through mcp tools (or https://github.com/leanprover-community/mathlib4) to make sure the lemma exists. Else, write your own implementation of the lemma.
- You are not allowed to delete ANY theorems or functions in the file. You can only modify them in a very cautious way, and if you think some theorem itself is not correct, find its corresponding theorem in coq at /home/hantao/code/flocq/src/Core/Float_prop.v and use that definition instead. Do not change the theorem without any reference!
- If you observe that the whole file is completed, which means that no sorry or error could be spotted in the file, find the process containing `iterate_codex.sh` and terminate it.

### Success Criteria

✅ All `sorry` statements eliminated
✅ Clean compilation for entire file
✅ Each proof verified individually before moving on
EOF

# ========== Build the CLI command as an array to preserve spaces/newlines ==========
cmd=(codex --model gpt-5 high exec "$msg" --dangerously-bypass-approvals-and-sandbox)

# ========== Main execution loop (5 hours) ==========
end=$(( $(date +%s) + 5*60*60 ))

echo "$(ts) Starting execution loop. End at $(date -d "@$end" +"%Y-%m-%d %H:%M:%S" 2>/dev/null || date -r "$end" +"%Y-%m-%d %H:%M:%S")"
while [ "$(date +%s)" -lt "$end" ]; do
  if [[ -n "$TIMEOUT_BIN" ]]; then
    # Add a per-iteration timeout as a guard (optional); adjust as needed
    "$TIMEOUT_BIN" 30m "${cmd[@]}" || true
  else
    "${cmd[@]}" || true
  fi
done
echo "$(ts) Execution loop finished."