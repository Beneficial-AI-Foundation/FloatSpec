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
  # Round_generic.lean
  # Ulp.lean
  
  # Div.lean
  # Plus.lean
  # Round.lean
  # Sqrt.lean
  # Operations.lean
  # Bracket.lean
  # Binary.lean
  # Bits.lean
  BinarySingleNaN.lean
  PrimFloat.lean
)
hours=(
#   2
#   2
  # 4
  # 2
  # 2
  # 2
  # 6
  # 6
  6
  6
  # 4
  
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

## Task: Fix Proofs in FloatSpec/src/IEEE754/__PLACEHOLDER__

## Scope

theorems: Fix the first (only the very first, work really hard on it and don't care about others) theorem without a full proof \(sorry and/or error and/or unsolved goals, whatever make the proof incomplete\) in the function. First locate the line number and the error type you need to fix using lake build (the very first incomplete proof within the target file). If there is error inside FloatSpec/src/IEEE754/__PLACEHOLDER__, locate the error with the smallest line number and deal with that theorem; if there is not error (or error is in files that is other than FloatSpec/src/IEEE754/__PLACEHOLDER__ and is not a dependency of FloatSpec/src/IEEE754/__PLACEHOLDER__, e.g., Prop, Pff, IEEE754, ...), search for the very first sorry and deal with that theorem; if the sorry appears inside a function, go search for it's original definition in /home/hantao/code/flocq/src/IEEE754, transform it into lean4, and fix the corresponding theorems and proof accordingly; if no sorry or error appear in this file, just report this process and end. Then think in detail about the mistake, and work really hard to solve it. You can use exisiting lemma to assist your proof or create new private lemma to assist your proof. If you think the original theorem is inadequate, you might revise it, but in a very cautious way and record every those changes in a markdown file. 

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

### Logging

- **Save all build outputs:** Always redirect `lake build` output to log files in `__LOG_DIR__` directory
- **Log file naming:** Use descriptive names like `__LOG_DIR__/build_<timestamp>.log` or `__LOG_DIR__/error_<timestamp>.log`
- **Error analysis:** When encountering errors, save the full build output to `__LOG_DIR__` and analyze the log file to locate specific line numbers and error types

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
    - If you are meeting difficulties at least come up with some useful lemma that c33ould compile and is helpful to future proofs before ending your session. Remember that!
    - Do not give up easily! Do not replace existing theorems or functions with `sorry`, `pure true`, or `admit` for the simplicity of compilation! If the theorem is indeed hard, you should check the original theorem and proof in the corresponding file at /home/hantao/code/flocq/src/IEEE754, and try to understand the original proof and transform it into lean4. You should only change the existing pre- and post-condition or functions when it is different with the original one and this diff hinders the proof process, and you should record every those changes in a markdown file.
    - Do not be frustrate! Do not delete the proof that is already completed and passed compilation!
- Skip already-proven theorems!! There might be warnings be just leave them there!
- You can use exisiting (and proved) theorem to assist your proving. If a theorem is necessary but not proved, you can turn to work on that first. The useful theorems might not be in the same file, but in the import list
- When you are trying to use a certain lemma, check through https://github.com/leanprover-community/mathlib4 to make sure the lemma exists. Else, write your own implementation of the lemma.
- You are not allowed to delete ANY theorems or functions in the file. You can only modify them in a very cautious way!
- The output of `lake build` could be long (but it's normal to be several minutes so don't be too hard on it): You should save the build output to a log file in `__LOG_DIR__` and search for error within it, which is better than going through the long log by yourself.
- If some theorems relies on other theorems that is not imported yet (possibly in the later part of this file), you should move that theorem to the later part of this file and prove the other theorems first. You should only change the order of the theorems in a very cautious way, and if you think some theorem itself is not correct, find its corresponding theorem in coq at /home/hantao/code/flocq/src/IEEE754 and use that definition instead. Do not change the theorem without any reference!
- Again, do not replace existing theorems or functions with `sorry`, `pure true`, or `admit` for the simplicity of compilation!  If the theorem is indeed hard, you should check the original theorem and proof in the corresponding file at /home/hantao/code/flocq/src/IEEE754, and try to understand the original proof and transform it into lean4. AGAIN, NO `pure true` SHOULD BE USED TO ESCAPE THE PROOF OR TO SERVE AS A PLACEHOLDER! IF YOU WANT TO USE A PLACEHOLDER, USE `sorry` INSTEAD!
- Some theorems are in the format of a def and a theorem pair. If the def is given by sorry, you should first implement the def according to the original definition in /home/hantao/code/flocq/src/IEEE754, and then prove the corresponding theorem. If the sorry in def is hard to implement as a function, you should directly contain all the content (you can derive that from /home/hantao/code/flocq/src/IEEE754 by search the theorem there) in the theorems, clean the def, and prove the theorem.
- Again, NO PURE TRUE!!!!!

### Success Criteria

✅ All `sorry` statements eliminated
✅ Clean compilation for entire file
✅ Each proof verified individually before moving on
EOF

  # Export environment variable for sandbox mode
  export IS_SANDBOX=1

  # Create .log directory if it doesn't exist
  mkdir -p .log

  end=$(( $(date +%s) + t*60*60 ))
  while [[ $(date +%s) -lt $end ]]; do
    timestamp=$(date +%Y%m%d_%H%M%S)
    log_dir=".log"
    
    # Replace placeholders with actual values
    current_msg="${msg//__PLACEHOLDER__/$f}"
    current_msg="${current_msg//__LOG_DIR__/$log_dir}"
    
    # Update command with the message containing replaced placeholders
    cmd=(claude -p "$current_msg" --dangerously-skip-permissions)
    
    if [[ -n "$TIMEOUT_BIN" ]]; then
      "$TIMEOUT_BIN" 7200 "${cmd[@]}" 2>&1 || true
    else
      "${cmd[@]}" 2>&1 || true
    fi
    git add .
    git commit -m "Update $f at $timestamp after an agent round" || true
  done
done