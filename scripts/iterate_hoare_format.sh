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
  
  # Core
  Calc
)
hours=(
#   2
#   2
  # 4
  # 2
  # 2
  6
  # 0
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

## Task: Fix Verso Documentation Formatting and Proofs in FloatSpec/src/__PLACEHOLDER__

## Scope

**PRIORITY ORDER**:
1. **Fix Verso formatting errors FIRST** (especially "expected '_' without preceding space" errors): You should compile and examine whether there are any verso formatting errors. If there are, you should fix them first.
   - These are syntax errors that block compilation
   - Locate all Verso errors using `lake build 2>&1 | grep "expected '_' without preceding space"`
   - Fix docstring formatting issues before proceeding to proof fixes
   - See "Verso Documentation Formatting Rules" section below for details

2. **Then fix proofs/theorems**: After confirming there are no Verso formatting errors (i.e., when the file has no verso formatting errors), fix buggy proofs. Fix `sorry` statements, compilation errors, unsolved goals, and other proof issues - all of these are considered proof/theorem errors that need to be addressed. Fix the first (only the very first, work really hard on it and don't care about others) theorem with a buggy proof (sorry and/or error and/or unsolved goals, whatever make the proof incomplete) in the function. First locate the line number and the error type you need to fix using lake build (the very first incomplete proof within the target file). If there is error, locate the error with the smallest line number and deal with that theorem; if there is no error, search for the very first sorry and deal with that theorem; if there are unsolved goals, fix the proof with unsolved goals; if the buggy proof appears inside a function, go search for it's original definition in /home/hantao/code/flocq/src/Calc, transform it into lean4, and fix the corresponding theorems and proof accordingly; if no errors, sorry, or unsolved goals appear in this file, just report this process and end. Then think in detail about the mistake, and work really hard to solve it. You can use exisiting lemma to assist your proof or create new private lemma to assist your proof. If you think the original theorem is inadequate, you might revise it, but in a very cautious way and record every those changes in a markdown file. 

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

### @[spec] Attribute Fix Pattern (BATCH FIX)

**CRITICAL**: When encountering `@[spec]` errors like:
- `Type of X is not a type application: Prop`
- `Type of X is not a type application: Bool`  
- `Type of X is not a type application: ℝ` (or any non-monadic type)
- `Invalid 'spec': target was neither a Hoare triple specification nor a 'simp' lemma`

**Root Cause**: The `@[spec]` attribute requires Hoare triples where the program part MUST be a monadic computation (e.g., `Id α`), but the code is using a plain type (Prop, Bool, ℝ, etc.).

**Fix Pattern**:

1. **For Prop types**:
   ```lean
   -- WRONG:
   @[spec]
   theorem my_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
       ⦃⌜True⌝⦄
       Rnd_DN F rnd  -- ERROR: Prop, not monadic
       ⦃⇓result => ...⦄ := by
   
   -- CORRECT:
   @[spec]
   theorem my_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
       ⦃⌜True⌝⦄
       (pure (Rnd_DN F rnd) : Id Prop)  -- Wrap in Id
       ⦃⇓result => ...⦄ := by
   ```

2. **For Bool types**:
   ```lean
   -- WRONG:
   @[spec]
   theorem check_spec (x y : ℝ) :
       ⦃⌜True⌝⦄
       Rnd_DN_pt_check F x y  -- ERROR: Bool, not monadic
       ⦃⇓result => ...⦄ := by
   
   -- CORRECT:
   @[spec]
   theorem check_spec (x y : ℝ) :
       ⦃⌜True⌝⦄
       (pure (Rnd_DN_pt_check F x y) : Id Bool)  -- Wrap in Id
       ⦃⇓result => ...⦄ := by
   ```

3. **For other types** (ℝ, Int, etc.):
   ```lean
   -- WRONG:
   @[spec]
   theorem calc_spec (x : ℝ) :
       ⦃⌜True⌝⦄
       round_val_of_pred rnd x  -- ERROR: ℝ, not monadic
       ⦃⇓result => ...⦄ := by
   
   -- CORRECT:
   @[spec]
   theorem calc_spec (x : ℝ) :
       ⦃⌜True⌝⦄
       (pure (round_val_of_pred rnd x) : Id ℝ)  -- Wrap in Id
       ⦃⇓result => ...⦄ := by
   ```

4. **Proof adjustments after wrapping**:
   - After wrapping in `(pure ... : Id T)`, update the proof:
   ```lean
   -- Updated proof pattern:
   @[spec]
   theorem my_spec ... :
       ⦃⌜True⌝⦄
       (pure (my_function args) : Id Type)
       ⦃⇓result => ...⦄ := by
     intro _
     simp [wp, PostCond.noThrow, pure, my_function]  -- Add wp, PostCond.noThrow, pure to simp
     -- Then continue with normal proof tactics
   ```

**Systematic Fix Process**:

1. **Find all `@[spec]` errors**:
   ```bash
   lake build 2>&1 | grep -E "(Invalid 'spec'|Type of .* is not a type application)"
   ```

2. **For each error**:
   - Locate the theorem with `@[spec]`
   - Identify the non-monadic expression in the program part (between `⦃⌜True⌝⦄` and `⦃⇓...⦄`)
   - Wrap it: `(pure (original_expression) : Id Type)`
   - Update the proof to include `simp [wp, PostCond.noThrow, pure, function_name]`

3. **Verify each fix**:
   - After each fix, run `lake build` to ensure it compiles
   - Fix any new errors that arise

**Examples of functions that need wrapping**:
- Predicates returning `Prop`: `Rnd_DN F rnd`, `Rnd_UP F rnd`, `Rnd_N F rnd`
- Boolean checks: `*_check` functions returning `Bool`
- Pure calculations: Functions returning `ℝ`, `Int`, `Nat`, etc. that aren't already in `Id`

**NOTE**: This pattern applies to ALL `@[spec]` theorems. The Hoare triple syntax `⦃P⦄ prog ⦃Q⦄` REQUIRES `prog` to be monadic. Pure values must be wrapped in `Id` using `(pure ... : Id Type)`.

### Verso Documentation Formatting Rules

**CRITICAL**: This project uses Verso documentation system (enabled via `doc.verso` in lakefile.lean). Verso is a documentation framework for Lean that enforces strict formatting rules. All docstrings MUST comply with Verso's formatting requirements to avoid compilation errors.

**Reference**: See `external_docs/verso_manual.pdf` for complete Verso documentation rules.

1. **Docstring Structure (CRITICAL)**:
   - Docstrings start with `/--` and end with `-/`
   - The closing `-/` marker MUST be on its own line starting at column 0 (no indentation, no preceding spaces)
   - There MUST be a blank line between the last line of docstring content and the closing `-/` marker
   - Example of CORRECT format:
     ```lean
     /-- Description of the function
     
         More detailed explanation here.
     -/
     def myFunction ...
     ```
   - Example of INCORRECT format (will cause "expected '_' without preceding space" error):
     ```lean
     /-- Description
     -/  -- ERROR: closing marker on same line or with preceding content
     ```
   - Another INCORRECT format:
     ```lean
     /-- Description
         Last line of content.
     -/  -- ERROR: no blank line before closing marker
     ```

2. **Fixing "expected '_' without preceding space" Errors**:
   - This error occurs when Verso's parser encounters a docstring closing marker `-/` that doesn't meet formatting requirements
   - **Fix procedure**:
     1. Locate the error line (e.g., `error: FloatSpec/src/Core/Zaux.lean:274:0`)
     2. Find the docstring that ends at that line
     3. Ensure the closing `-/` is:
        - On its own line (nothing else on that line)
        - Starting at column 0 (no indentation)
        - Preceded by a blank line (empty line between content and `-/`)
     4. Example fix:
        ```lean
        /-- Old (incorrect):
            Content here.
        -/
        
        /-- New (correct):
            Content here.
        
        -/
        ```

3. **Verso Markup Syntax Rules** (from Verso manual):
   - Verso uses a simplified Markdown-like syntax
   - Paragraphs are separated by blank lines
   - Inline code uses backticks: `` `code` ``
   - Code blocks use triple backticks with language specification
   - Headers use `#` symbols (but these are typically not used in docstrings)
   - Verso has stricter parsing than standard Markdown - syntax errors fail fast

4. **Docstring Content Best Practices**:
   - Use proper paragraph breaks (blank lines) within docstrings for readability
   - Keep docstrings focused and clear
   - Use inline code formatting for function names, types, and technical terms
   - Mathematical notation should use proper Unicode characters or LaTeX-style formatting
   - Avoid complex nested structures that might confuse Verso's parser

5. **Priority**: When you encounter Verso formatting errors (especially "expected '_' without preceding space"), fix them FIRST before working on proofs. These are syntax errors that block compilation and must be resolved before the code can be type-checked.

### Important Notes

- Some functions ARE difficult to prove - persistence is expected
    - If you are meeting difficulties at least come up with some useful lemma that could compile and is helpful to future proofs before ending your session. Remember that!
    - Do not give up easily! Do not replace existing theorems or functions with `sorry`, `pure true`, or `admit` for the simplicity of compilation! If the theorem is indeed hard, you should check the original theorem and proof in the corresponding file at /home/hantao/code/flocq/src/Calc, and try to understand the original proof and transform it into lean4. You should only change the existing pre- and post-condition or functions when it is different with the original one and this diff hinders the proof process, and you should record every those changes in a markdown file.
    - Do not be frustrate! Do not delete the proof that is already completed and passed compilation!
- Skip already-proven theorems!! There might be warnings be just leave them there!
- You can use exisiting (and proved) theorem to assist your proving. If a theorem is necessary but not proved, you can turn to work on that first. The useful theorems might not be in the same file, but in the import list
- When you are trying to use a certain lemma, check through https://github.com/leanprover-community/mathlib4 to make sure the lemma exists. Else, write your own implementation of the lemma.
- You are not allowed to delete ANY theorems or functions in the file. You can only modify them in a very cautious way!
- The output of `lake build` could be long (but it's normal to be several minutes so don't be too hard on it): You could save the build output to a log file and search for error within it, which is better than going through the long log by yourself.
- If some theorems relies on other theorems that is not imported yet (possibly in the later part of this file), you should move that theorem to the later part of this file and prove the other theorems first. You should only change the order of the theorems in a very cautious way, and if you think some theorem itself is not correct, find its corresponding theorem in coq at /home/hantao/code/flocq/src/Calc and use that definition instead. Do not change the theorem without any reference!
- Again, do not replace existing theorems or functions with `sorry`, `pure true`, or `admit` for the simplicity of compilation!  If the theorem is indeed hard, you should check the original theorem and proof in the corresponding file at /home/hantao/code/flocq/src/Calc, and try to understand the original proof and transform it into lean4. AGAIN, NO `pure true` SHOULD BE USED TO ESCAPE THE PROOF OR TO SERVE AS A PLACEHOLDER! IF YOU WANT TO USE A PLACEHOLDER, USE `sorry` INSTEAD!
- Some theorems are in the format of a def and a theorem pair. If the def is given by sorry, you should first implement the def according to the original definition in /home/hantao/code/flocq/src/Calc, and then prove the corresponding theorem. If the sorry in def is hard to implement as a function, you should directly contain all the content (you can derive that from /home/hantao/code/flocq/src/Calc by search the theorem there) in the theorems, clean the def, and prove the theorem.
- Again, NO PURE TRUE!!!!!

### Success Criteria

✅ All `sorry` statements eliminated
✅ Clean compilation for entire file
✅ Each proof verified individually before moving on
EOF

  # Replace the placeholder with the actual file name
  msg=${msg//__PLACEHOLDER__/$f}

  # Export environment variable for sandbox mode
  export IS_SANDBOX=1

  # Create .log directory if it doesn't exist
  mkdir -p .log

  # Build the CLI command as an array to preserve spaces/newlines
  # NOTE: Using claude with approval bypass flags
  cmd=(claude -p "$msg" --dangerously-skip-permissions)

  end=$(( $(date +%s) + t*60*60 ))
  while [[ $(date +%s) -lt $end ]]; do
    timestamp=$(date +%Y%m%d_%H%M%S)
    log_file=".log/${timestamp}_verso_${f}.log"
    
    if [[ -n "$TIMEOUT_BIN" ]]; then
      "$TIMEOUT_BIN" 3600 "${cmd[@]}" 2>&1 | tee "$log_file" || true
    else
      "${cmd[@]}" 2>&1 | tee "$log_file" || true
    fi
    git add .
    git commit -m "Update $f at $timestamp after an agent round" || true
  done
done