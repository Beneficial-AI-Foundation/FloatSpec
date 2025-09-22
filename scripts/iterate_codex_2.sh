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
  Generic_fmt.lean
)
hours=(
#   2
#   2
  4
  4
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
Please ensure your implementation Always Works™ for:

## Task: Fix Proofs in FloatSpec/src/Core/__PLACEHOLDER__

## Scope

theorems: Fix the first (only the very first, work really hard on it and don't care about others) theorem without a full proof \(sorry and/or error and/or unsolved goals, whatever make the proof incomplete\) in the function. First locate the line number and the error type you need to fix using lake build (the very first incomplete proof within the target file). If there is error, locate the error with the smallest line number and deal with that theorem; if there is not error, search for the very first sorry and deal with that theorem; if the sorry appears inside a function, go search for it's original definition in /home/hantao/code/flocq/src/Core, transform it into lean4, and fix the corresponding theorems and proof accordingly; if no sorry or error appear in this file, just report this process and end. Then think in detail about the mistake, and work really hard to solve it. You can use exisiting lemma to assist your proof or create new private lemma to assist your proof. If you think the original theorem is inadequate, you might revise it, but in a very cautious way and record every those changes in a markdown file. 

### Prerequisites

1. **Read documentation first:**
    - FloatSpec/PIPELINE.md - understand the overall pipeline
    - ./CLAUDE.md - focus on proof writing instructions and mvcgen info

### Core Requirements

### Proof Writing Process

1. **Follow the Zfast_div_eucl_spec example** in Zaux.lean and other proofs in current file as your template
2. **ONE-BY-ONE approach is mandatory:**
    - Write ONE proof
    - Check immediately with `lake build`
    - Fix any errors before proceeding to next proof
    - Never batch multiple proofs without checking

### Before Writing Each Proof

1. **Verify function implementation** - ensure the function body is correct
2. **Check existing specs** - understand what needs to be proven
3. **Preserve syntax** - do NOT change hoare triple syntax unless absolutely necessary
    - Think multiple times before modifying specs or code body
    - If changes are needed, decompose complex specs rather than rewriting

### Compilation Verification

- **After EVERY proof:** Run `lake build xxx`
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
    - Search for proof tactics
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

- Some functions ARE difficult to prove - persistence is expected
    - If you are meeting difficulties at least come up with some useful lemma that could compile and is helpful to future proofs before ending your session. Remember that!
- Skip already-proven theorems!! There might be warnings be just leave them there!
- You can use exisiting (and proved) theorem to assist your proving. If a theorem is necessary but not proved, you can turn to work on that first. The useful theorems might not be in the same file, but in the import list
- When you are trying to use a certain lemma, check through https://github.com/leanprover-community/mathlib4 to make sure the lemma exists. Else, write your own implementation of the lemma.
- You are not allowed to delete ANY theorems or functions in the file. You can only modify them in a very cautious way!
- The output of `lake build` could be long (but it's normal to be several minutes so don't be too hard on it): You could save the build output to a log file and search for error within it, which is better than going through the long log by yourself.

### Success Criteria

✅ All `sorry` statements eliminated
✅ Clean compilation for entire file
✅ Each proof verified individually before moving on
EOF

  # Replace the placeholder with the actual file name
  msg=${msg//__PLACEHOLDER__/$f}

  # Build the CLI command as an array to preserve spaces/newlines
  # NOTE: Keep your original flags; remove the stray 'high' token if not supported.
  cmd=(codex --model gpt-5 exec "$msg" --dangerously-bypass-approvals-and-sandbox)

  end=$(( $(date +%s) + t*60*60 ))
  while [[ $(date +%s) -lt $end ]]; do
    if [[ -n "$TIMEOUT_BIN" ]]; then
      "$TIMEOUT_BIN" 3600 "${cmd[@]}" || true
    else
      "${cmd[@]}" || true
    fi
  done
done