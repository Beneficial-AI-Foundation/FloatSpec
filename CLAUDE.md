# FloatSpec Project Overview

You are a functional programmer working in Lean 4.

**Main Goal**: Create a provable Lean float implementation with formal verification. Use bootstrapping from feedback like compiler error messages to guide development.

## IMPORTANT: "Keep Going" Context

If you're told to "keep going" without context, you're likely working on:
1. **Float Implementation** - Developing provable floating-point arithmetic
2. **Specification Writing** - Creating formal specifications for float operations
3. **Test Writing** - Add more property-based tests using Plausible

## General Programming Philosophy

Programming is about onomastics (naming), composition (functoriality), and caching. Think conformally at every scale and across scales.

Build a pit of success: internal systems that grow as a whole outwards, never allowing the fallible external world to leak in except at boundaries. Meet the external world at well-defined interfaces.

When solving problems, write tooling/linters/auto-fixers to widen the pit of success. Use rigid compiler error messages and linter warnings to guide future users (**including** AI) toward correct solutions.

Favor statically typed functional programming but use mutability where it makes sense or is easier to port.

## Project Structure

- `FloatSpec.lean` and `FloatSpec/` directory - core float functionality and specifications.
- `lakefile.lean` - Lean 4 project configuration.

## Development Commands

**`just` is our main program runner.** It provides a unified interface for all common development tasks. Run `just` without arguments to see all available commands.

Key commands:
- `just build` - Build Lean project
- `just test` - Run the Python test suite  
- `just bootstrap` - Bootstrap developer environment (Rust, Elan, UV)

You can also run underlying tools directly:
- `lake build` - Build Lean project (use frequently for constant feedback)
- `uv run -m pytest` - Run Python tests directly

## Commit Logging Process

After making a commit, create a log entry:

1. Create timestamped directory: `.log/YYYYMMDD_HHMMSS/`
2. Store commit information:
   - `change_stats.txt` - Basic change statistics (see `.log/20250808_102956/change_stats.txt` for an example)
   - `change_stats.txt` - Basic commit metadata (hash, author, date, subject)
   - `full_diff.txt` - Full diff of changes (see `.log/20250808_102956/full_diff.txt` for an example)
   - `detailed_changelog.md` - Detailed summary of changes and their impact (see `.log/20250808_102956/detailed_changelog.md` for an example)

This provides a searchable history of all significant changes to the codebase.

### Recent Commits

- **2025-08-08 10:29:56** - Replace Float with Real (ℝ) throughout codebase
  - Major architectural fix replacing Lean's Float with mathematical reals
  - 54 files changed across entire codebase
  - See `.log/20250808_102956/` for details

Use `uvx lean-lsp-mcp` to get feedback on your code (primary workflow). Prefer these tools for fast, local diagnostics after every change; use `lake build` for broader checks or when you need a full project build.

Usage:

- `lean_diagnostic_messages`: Get all diagnostic messages for a Lean file. This includes infos, warnings and errors.

```text
Example output
l20c42-l20c46, severity: 1
simp made no progress

l21c11-l21c45, severity: 1
function expected at h_empty term has type T ∩ compl T = ∅
```

- `lean_goal`: Get the proof goal at a specific location (line or line & column) in a Lean file.

Example output (line):

```text
Before:
S : Type u_1
inst✝¹ : Fintype S
inst✝ : Nonempty S
P : Finset (Set S)
hPP : ∀ T ∈ P, ∀ U ∈ P, T ∩ U ≠ ∅
hPS : ¬∃ T ∉ P, ∀ U ∈ P, T ∩ U ≠ ∅
compl : Set S → Set S := fun T ↦ univ \ T
hcompl : ∀ T ∈ P, compl T ∉ P
all_subsets : Finset (Set S) := Finset.univ
h_comp_in_P : ∀ T ∉ P, compl T ∈ P
h_partition : ∀ (T : Set S), T ∈ P ∨ compl T ∈ P
⊢ P.card = 2 ^ (Fintype.card S - 1)
After:
no goals
```

- `lean_term_goal`: Get the term goal at a specific position (line & column) in a Lean file.

- `lean_hover_info`: Retrieve hover information (documentation) for symbols, terms, and expressions in a Lean file (at a specific line & column).

Example output (hover info on a `sorry`):

```text
The `sorry` tactic is a temporary placeholder for an incomplete tactic proof,
closing the main goal using `exact sorry`.

This is intended for stubbing-out incomplete parts of a proof while still having a syntactically correct proof skeleton.
Lean will give a warning whenever a proof uses sorry, so you aren't likely to miss it,
but you can double check if a theorem depends on sorry by looking for sorryAx in the output
of the #print axioms my_thm command, the axiom used by the implementation of sorry.
```

- `lean_declaration_file`: Get the file contents where a symbol or term is declared. Use this to find the definition of a symbol.

- `lean_completions`: Code auto-completion: Find available identifiers or import suggestions at a specific position (line & column) in a Lean file. Use this to fill in program fragments.

- `lean_multi_attempt`:  Attempt multiple lean code snippets on a line and return goal state and diagnostics for each snippet. This tool is useful to screen different attempts before using the most promising one.

```text
Example output (attempting `rw [Nat.pow_sub (Fintype.card_pos_of_nonempty S)]` and `by_contra h_neq`)
rw [Nat.pow_sub (Fintype.card_pos_of_nonempty S)]:
S : Type u_1
inst✝¹ : Fintype S
inst✝ : Nonempty S
P : Finset (Set S)
hPP : ∀ T ∈ P, ∀ U ∈ P, T ∩ U ≠ ∅
hPS : ¬∃ T ∉ P, ∀ U ∈ P, T ∩ U ≠ ∅
⊢ P.card = 2 ^ (Fintype.card S - 1)

l14c7-l14c51, severity: 1
unknown constant 'Nat.pow_sub'

by_contra h_neq:
S : Type u_1
inst✝¹ : Fintype S
inst✝ : Nonempty S
P : Finset (Set S)
hPP : ∀ T ∈ P, ∀ U ∈ P, T ∩ U ≠ ∅
hPS : ¬∃ T ∉ P, ∀ U ∈ P, T ∩ U ≠ ∅
h_neq : ¬P.card = 2 ^ (Fintype.card S - 1)
⊢ False
```

### Building and Testing

```bash
# Build using just (recommended)
just build        # Build Lean project
just test         # Run Python tests

# Or use direct commands:
lake build        # Full Lean build (slower; use as a cross-check)
uv run -m pytest -q  # Run tests directly

# Check Lean syntax and types
lake build --verbose
```

## Proof Writing Playbook

- One-by-one: Write exactly one proof, run LSP diagnostics immediately (via `lean_lsp_mcp`), fix issues, then move on. Do not batch multiple new proofs without checking.
- Follow examples: Mirror patterns from existing proofs, especially `Zfast_div_eucl_spec` in `FloatSpec/src/Core/Zaux.lean` and nearby lemmas in the same file you are editing.
- Before each proof:
  - Verify the function body is correct and stable.
  - Check existing specs to understand precisely what needs to be proven.
  - Preserve specification/Hoare triple syntax; avoid changing it unless absolutely necessary. If change is unavoidable, decompose the spec into simpler lemmas rather than rewriting wholesale.
- Compilation verification:
  - After every proof, run `lean_lsp_mcp.lean_diagnostic_messages` for the edited file.
  - Use `lake build` as a fallback or for a project-wide typecheck.
  - “Complete” means: no `sorry` in the edited proof and the file typechecks.
- When stuck:
  - Search for relevant lemmas with MCP hover/decl tools or Mathlib; if a lemma doesn’t exist, write a small private helper lemma close to the proof.
  - Decompose complex statements into smaller, local lemmas.
  - Reference nearby proofs for patterns and naming.

## Practical Lean Tips (FloatSpec)

- Magnitude and logs:
  - `mag` is defined with `Int.ceil (log (|x|)/log β)`. To get `|x| ≤ β^e`, sandwich `L := log|x|/logβ` and use `Real.log_le_iff_le_exp` plus `Real.log_zpow`.
  - Keep a clean chain: derive `log |x| ≤ log (β^e)`, then exponentiate; avoid brittle simp rewrites between `exp (e*log β)` and `β^e`—prove equality explicitly using `Real.exp_log` and `Real.log_zpow`.
- Powers and positivity:
  - Use `zpow_pos : 0 < a → 0 < a^n` and `abs_of_nonneg` for `a^n` when the base is positive.
  - Collapse products with `FloatSpec.Core.Generic_fmt.zpow_mul_sub` and reconstruct with `zpow_add₀` or `zpow_sub_add` (requires nonzero base).
  - For nonnegative exponent `k ≥ 0`, switch to Nat powers via `zpow_nonneg_toNat`.
- Absolute values with scaling factors:
  - Prefer `abs (x * y) = |x| * |y|` and ensure `y ≥ 0` so `|y| = y`.
  - When the scale is `β^(-c)`, consider rewriting as `((β^c)⁻¹)` and use `inv_nonneg.mpr (le_of_lt (zpow_pos …))` to keep monotonicity simple.
- Integer truncation:
  - Use `Ztrunc_intCast` and `Ztrunc_zero` to compute truncations on integer-valued expressions.
- Calc blocks over heavy simp:
  - Prefer explicit `calc`/`have` chains with named lemmas instead of relying on `simp` to bridge nondefinitional equalities (especially around `log/exp`, `zpow`, and `abs`).

## Plan + Preambles (for AI agents)

- Maintain a short, evolving plan (use the `update_plan` tool) with exactly one `in_progress` step.
- Before grouped tool calls, write a concise 1–2 sentence preamble explaining what you are about to do.
- Share progress updates after nontrivial steps, and re-align the plan if scope changes.

## Quality Bar

- 30-second reality check: After each change, be able to answer “yes” to all:
  - Did I run/build the code (via MCP or `lake build`)?
  - Did I trigger the exact feature I changed?
  - Did I see expected results, and check for errors?
  - Would I bet $100 it works?
- Phrases to avoid: “should work”, “fixed the issue” (without verification), “try it now” (without running it yourself).

## FloatSpec Roadmap

### 1. Float Representation and Core Operations

- **IEEE 754 compliant types**: Implement single and double precision floating-point numbers
- **Bit-level representation**: Use `BitVec` for accurate bit-level manipulation
- **Core arithmetic**: Addition, subtraction, multiplication, division with proper rounding

### 2. Formal Specifications

- **IEEE 754 semantics**: Formalize the IEEE 754 standard in Lean
- **Error bounds**: Specify and prove error bounds for operations
- **Special values**: Handle infinities, NaN, and subnormal numbers correctly

### 3. Next Steps

1. **Core types**: Implement IEEE 754 float types with bit-accurate representation
2. **Property test probe**: Use <https://github.com/leanprover-community/plausible> to test properties of the spec in a cheap way, a sort of Pareto frontier point in between unit tests and formal proofs. Write code with an eye towards generalizing to future use.
   - [ ] make `lean_lib` in `lakefile.lean` for property tests
3. **Benchmark & test**: small-scale benchmarks (`#eval`, `timeIt`) for performance validation.

- [ ] investigate `lake bench`

4. **Docs & examples**: <https://github.com/leanprover/verso> is the (meta)-doc tool. It is very extensible.
   - [ ] add any accumulated verso extensions to `VersoExt`
     - [ ] update `lakefile.lean` to include `VersoExt`

## Lean 4 Development Guidelines

- Use named holes (`?foo`) for incremental development
- Wrap reserved names in «guillemets» when needed
- Implement "notation typeclasses" like `GetElem`, `Add`, etc where appropriate.
- Practice "sorry-friendly programming": Instead of a comment you put down a spec, but it is only "proved" with `sorry`. This is strictly better than a comment, because the typechecker will use it for program generation.
- Decompose proofs until tools like `canonical`, `grind`, and `simp` dissolve the pieces. Use them to do the "how", the AI should do the "what".
- Don't use `i` and `j` as variable names when you could use `r`(ow) and `c`(olumn) instead. Ditto for `m` and `n` as matrix dimensions. Use `R` and `C`.

## Verifying Imperative Programs using mvcgen

The `mvcgen` tactic implements a monadic verification condition generator that breaks down goals involving imperative programs written using Lean's `do` notation into pure verification conditions.

### Key Features:
- **Monadic verification**: Handles programs with local mutability, for loops, and early returns
- **Hoare triple support**: Specifications use the notation `⦃P⦄ prog ⦃Q⦄` for pre/postconditions
- **Loop invariants**: Supports specifying invariants for loops using zipper data structures
- **Compositional reasoning**: Allows building specifications for individual monadic functions
- **Monad transformer stacks**: Works with StateT, ReaderT, ExceptT and custom monad combinations

### Basic Usage Pattern:
```lean
theorem program_correct : program_spec := by
  generalize h : (program args) = result
  apply MonadType.of_wp_run_eq h  -- Focus on monadic part
  mvcgen [unfold_hints]           -- Generate verification conditions
  case inv1 => exact invariant_spec  -- Specify loop invariants
  all_goals mleave; grind         -- Discharge pure goals
```

### Pure Functions with Id Monad Pattern

**IMPORTANT**: For pure functions, keep return types pure and use `Id` wrapper ONLY in specs:

```lean
-- CORRECT: Pure function returning plain type
def myCheck (x : Int) : Bool := x > 0

-- CORRECT: Spec wraps with (pure ... : Id T)
@[spec]
theorem myCheck_spec (x : Int) :
    ⦃⌜True⌝⦄
    (pure (myCheck x) : Id Bool)
    ⦃⇓r => ⌜r = true ↔ x > 0⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, myCheck]

-- WRONG: Don't make the function return Id
def badCheck (x : Int) : Id Bool := pure (x > 0)  -- DON'T DO THIS
```

**Why?** `mvcgen` requires SOME monad, even for pure functions. `Id` is the trivial monad, and wrapping only in specs keeps the function definitions clean.

### The @[spec] Attribute

Mark specification theorems with `@[spec]` to enable automatic lookup during verification:

```lean
@[spec]
theorem operation_spec : ⦃P⦄ operation ⦃Q⦄ := ...
```

### Loop Invariants:
- Use zipper data structures (`xs.pref` for processed elements, `xs.suff` for remaining)
- Early returns supported with `Invariant.withEarlyReturn`
- State-dependent invariants can reference monadic state through function arguments

### Skill Documentation

See `.claude/docs/lean4/mvcgen-tactic.md` and `.claude/docs/lean4/grind-tactic.md` for comprehensive documentation on these tactics.

This approach scales to complex imperative programs while maintaining compositional reasoning and avoiding the need to replicate control flow in proofs.
### Import and Module Structure

- Imports MUST come before any syntax elements, including module and doc comments
  - [ ] set extensible error messages to suggest a fix for AI. Then remove this admonishment.
- Set `linter.missingDocs = true` and `relaxedAutoImplicit = false` in `lakefile.lean`.

### Common Errors and Solutions

- **"unexpected token 'namespace'"**: Module/doc comment placed incorrectly (should be after imports)
- **"unexpected token"**: Often caused by misplaced docstrings - use multiline comments instead
  - [ ] use extensible error messages to suggest a fix for AI. Then remove this admonishment.
- [ ] make a pre-push hook that runs lake build


## Python Development Guidelines

- Always use `uv` for Python package management (not pip). Use `uv add` over `uv pip install`, `uv sync`, and `uv run` over `python`. If a tool requires further build integration, use hatch to do it in the `pyproject.toml`.

## Additional Guidelines

- Use `rg` and `fd` instead of grep/find
- Make atomic commits and use branches liberally


## Development Strategies

### Lean 4 Development Approach

- Read the reference manual assiduously. Ultrathink.
- Figure out the parser by interactively building up toy components.
- [ ] install https://github.com/GasStationManager/LeanTool as mcp tool
- Spam `lake build` to verify the pieces work and build up FUNCTORIALLY.
- **IMPORTANT**: Check compilation with `lake build` every time before marking anything as complete
- **IMPORTANT**: In Lean 4, `Int.emod` always returns a positive value (Euclidean modulo)
- Use compiler tooling like extensible error messages, `simproc` (pattern guided reductions), and metaprogramming for pit of success
- If you solve a hard problem, write a tactic or simproc to pave the way
- Try harder to index without `!` or `?` - name `match`/`if` branches for better inference
- Raw string syntax: `r#".."#`, multiline strings use `\` continuation
- Use `lakefile.lean` over `lakefile.toml` for better AI introspection and metaprogramming
- Incorporate positive surprises into memories - stay curious!

### Debugging and Development Process

- Use named holes like `?holeName` for well-typed fragment programs
- Make mermaid diagrams with labeled edges describing data flow
- Category theory wiring diagram style for complex systems
- Apply the scientific method for debugging

## FloatSpec Implementation Progress

### Current Status

- ✓ **Project Setup**: Basic Lean 4 project structure with lakefile.lean
- ✓ **Build System**: Lake configuration for Lean 4 development
- ✓ **Zaux.lean**: Complete formalization of auxiliary integer functions (80 functions from Coq)

### Flocq to Lean 4 Transformation Order

Based on the dependency analysis in `Deps/flocq_dependency_graph.dot`, the proper transformation order is:

#### **Phase 1: Core Foundation (Ready Now)**
1. ✓ **Zaux.lean** - Integer auxiliary functions (completed)
2. **Raux.lean** - Real auxiliary functions (169 defs) - **NEXT PRIORITY**
   - Depends on: Zaux
   - Required by: Most other Core files
3. **Defs.lean** - Basic definitions (12 defs)
   - Depends on: Zaux, Raux
   - Required by: Almost all other files

#### **Phase 2: Core Data Structures (After Phase 1)**
4. **Digits.lean** - Digit manipulation (62 defs)
   - Depends on: Zaux
   - Required by: Float_prop, Generic_fmt, and higher-level operations
5. **Float_prop.lean** - Basic float properties (36 defs)  
   - Depends on: Defs, Digits, Raux, Zaux
   - Required by: Most formatting and rounding operations

#### **Phase 3: Generic Formatting (After Phase 2)**
6. **Round_pred.lean** - Rounding predicates (78 defs)
   - Depends on: Defs, Raux
   - Required by: Generic_fmt, Ulp, Round_NE, FIX, FLX, FLT, FTZ
7. **Generic_fmt.lean** - Generic formatting (124 defs) - **MAJOR COMPONENT**
   - Depends on: Defs, Float_prop, Raux, Round_pred, Zaux
   - Required by: Ulp, Round_NE, FIX, FLX, FLT, FTZ and all higher-level operations

#### **Phase 4: Precision Systems (After Phase 3)**
8. **Ulp.lean** - Unit in the last place (116 defs)
9. **Round_NE.lean** - Nearest-even rounding (99 defs) 
10. **FIX.lean** - Fixed-point format (7 defs)
11. **FLX.lean** - Fixed-precision format (23 defs)
12. **FLT.lean** - Floating-point format (25 defs)
13. **FTZ.lean** - Flush-to-zero format (11 defs)

#### **Phase 5: IEEE 754 Implementation (After Phase 4)**
14. **Core.lean** - Top-level Core module (0 defs, imports all Core files)

#### **Phase 6: Calculations (After Core)**
15. **Calc/Bracket.lean** - Bracketing operations (37 defs)
16. **Calc/Operations.lean** - Basic operations (16 defs)
17. **Calc/Div.lean**, **Calc/Sqrt.lean**, **Calc/Round.lean**, **Calc/Plus.lean**

#### **Phase 7: Properties and IEEE754 (Final)**
18. **Prop/** modules - Error analysis and properties
19. **IEEE754/** modules - Full IEEE 754 implementation
20. **Pff/** modules - Legacy compatibility

### Current Next Steps

**Immediate Priority: Raux.lean**
- 169 definitions covering real number auxiliary functions
- Critical dependency for almost all other Core files
- Should be started immediately after Zaux completion

**Key Dependencies Insight:**
- Zaux → Raux → Defs forms the foundational triangle
- Generic_fmt is the central heavyweight component (124 defs)
- Most IEEE754 functionality requires the complete Core foundation
- Zaux has the widest fan-out (used by 12/13 Core modules)
- The dependency graph shows clear layering: Core → Calc → Prop → IEEE754
- Phase approach minimizes rework and enables parallel development within phases

### Design Principles

- **Correctness First**: Every operation should have formal verification
- **IEEE 754 Compliance**: Strict adherence to the IEEE 754 standard
- **Bit-level Accuracy**: Use precise bit-level representations
- **Type Safety**: Use Lean's type system to prevent numerical errors

## Important Lean Documentation Resources

When working with Lean 4, consult these authoritative sources:

- **Lean 4 Official Documentation**: <https://lean-lang.org/lean4/doc> - The formal Lean documentation covering language features, tactics, and standard library
- **Mathlib Manual**: <https://leanprover-community.github.io/mathlib-manual/html-multi/Guides/> - Comprehensive guide to mathlib conventions, tactics, and best practices
- **Lean Language Reference**: <https://lean-lang.org/doc/reference/latest/> - The definitive Lean language reference for syntax and semantics

## ✅ COMPLETED: Replace Float with Real (ℝ)

**Issue**: The implementation was using Lean's built-in `Float` type throughout the formalization, which created a circular definition - we were using floating-point numbers to define floating-point numbers!

**Solution Implemented**: Replaced all occurrences of `Float` with `ℝ` (Real) from Mathlib. This matches the original Coq Flocq library which uses `R` (Coq's real number type).

**Files updated**:
- ✅ All files in `FloatSpec/src/Core/` (Defs.lean, Raux.lean, Float_prop.lean, Round_pred.lean, Generic_fmt.lean, Ulp.lean, Round_NE.lean, FIX.lean, FLX.lean, FLT.lean, FTZ.lean)
- ✅ All files in `FloatSpec/src/Calc/` (Bracket.lean, Operations.lean, Div.lean, Sqrt.lean, Round.lean, Plus.lean)
- ✅ All files in `FloatSpec/src/Prop/` (All 7 property files)
- ✅ All files in `FloatSpec/src/IEEE754/` (Binary.lean, BinarySingleNaN.lean, Bits.lean, PrimFloat.lean)
- ✅ All files in `FloatSpec/src/Pff/` (Pff.lean, Pff2Flocq.lean, Pff2FlocqAux.lean)

**Changes completed**:
1. ✅ Added Mathlib dependency to lakefile.lean
2. ✅ Imported Mathlib's real number support (`import Mathlib.Data.Real.Basic` and `open Real`) in all files
3. ✅ Replaced `Float` with `ℝ` throughout all type annotations
4. ✅ Updated absolute value operations from `Float.abs` to `|·|` notation
5. ✅ Added `noncomputable` to functions involving real number operations

This fundamental architectural fix has been completed, ensuring the formalization correctly uses mathematical real numbers instead of computational floats.



## Development Tools and Workflow

### Version Control

**Jujutsu (jj) Setup for GitHub-friendly Development:**

- Use `jj git init --colocate` for existing git repos (recommended for this project)
- Colocated repos automatically sync jj and git on every command
- Enables mixing `jj` and `git` commands seamlessly
- Tools expecting `.git` directory continue to work

**Essential jj configuration:**

```bash
jj config edit --user
```

Add these settings:

```toml
[git]
auto-local-bookmark = true  # Import all remote bookmarks automatically

[snapshot]  
auto-update-stale = true    # Auto-update stale working copies when switching contexts
```

**Key workflow improvements over git:**

- Anonymous branches - no need to name every small change
- Better conflict resolution and interactive rebase
- `jj absorb` automatically squashes changes into relevant ancestor commits
- `jj undo` and `jj op restore` for powerful history manipulation
- Empty commit on top by default (enables easier experimentation)

**GitHub integration commands:**

- `jj git fetch` + `jj rebase -d main` (replaces `git pull`)
- `jj bookmark create <name>` for named branches
- SSH keys recommended for GitHub (as of Oct 2023)
- Support for both "add commits" and "rewrite commits" review workflows

## Common Lean Pitfalls

- [Automatic implicit parameters](https://github.com/nielsvoss/lean-pitfalls#automatic-implicit-parameters)
- [Forgetting the Mathlib cache](https://github.com/nielsvoss/lean-pitfalls#forgetting-the-mathlib-cache)
- [Using `have` for data](https://github.com/nielsvoss/lean-pitfalls#using-have-for-data)
- [Rewriting under binders](https://github.com/nielsvoss/lean-pitfalls#rewriting-under-binders)
- [Trusting tactics to unfold definitions](https://github.com/nielsvoss/lean-pitfalls#trusting-tactics-to-unfold-definitions)
- [Using `b > a` instead of `a < b`](https://github.com/nielsvoss/lean-pitfalls#using-b--a-instead-of-a--b)
- [Confusing `Prop` and `Bool`](https://github.com/nielsvoss/lean-pitfalls#confusing-prop-and-bool)
- [Not checking for distinctness](https://github.com/nielsvoss/lean-pitfalls#not-checking-for-distinctness)
- [Not accounting for 0](https://github.com/nielsvoss/lean-pitfalls#not-accounting-for-0)
- [Division by 0](https://github.com/nielsvoss/lean-pitfalls#division-by-0)
- [Integer division](https://github.com/nielsvoss/lean-pitfalls#integer-division)
- [Natural number subtraction](https://github.com/nielsvoss/lean-pitfalls#natural-number-subtraction)
- [Other partial functions](https://github.com/nielsvoss/lean-pitfalls#other-partial-functions)
- [Wrapping arithmetic in `Fin`](https://github.com/nielsvoss/lean-pitfalls#wrapping-arithmetic-in-fin)
- [Real power](https://github.com/nielsvoss/lean-pitfalls#real-power)
- [Distance in `Fin n → ℝ`](https://github.com/nielsvoss/lean-pitfalls#distance-in-fin-n-%E2%86%92-%E2%84%9D)
- [Accidental double `iInf` or `iSup`](https://github.com/nielsvoss/lean-pitfalls#accidental-double-iinf-or-isup)
- [Trying to extract data from proofs of propositions](https://github.com/nielsvoss/lean-pitfalls#trying-to-extract-data-from-proofs-of-propositions)
- [Working with equality of types](https://github.com/nielsvoss/lean-pitfalls#working-with-equality-of-types)
- [Parameters for instances that already exist](https://github.com/nielsvoss/lean-pitfalls#parameters-for-instances-that-already-exist)
- [Using `Set`s as types](https://github.com/nielsvoss/lean-pitfalls#using-sets-as-types)
- [Sort _](https://github.com/nielsvoss/lean-pitfalls#sort-_)
- [Trying to prove properties about Float](https://github.com/nielsvoss/lean-pitfalls#trying-to-prove-properties-about-float)
- [`native_decide`](https://github.com/nielsvoss/lean-pitfalls#native_decide)
- [Panic does not abort](https://github.com/nielsvoss/lean-pitfalls#panic-does-not-abort)
- [Lean 3 code](https://github.com/nielsvoss/lean-pitfalls#lean-3-code)
- [Non-terminal simp](https://github.com/nielsvoss/lean-pitfalls#non-terminal-simp)
- [Ignoring warnings](https://github.com/nielsvoss/lean-pitfalls#ignoring-warnings)
- [Ambiguous unicode characters](https://github.com/nielsvoss/lean-pitfalls#ambiguous-unicode-characters)

## Docs

Do NOT use the `{lit}` verso role if an identifier is missing. Use `{given
-show}`foo` and {givenInstance} roles.

## Verso Docstring Roles

- `{lean}` validates identifiers against global scope - metavariables like `n` will error
- `{given +show}`n : Nat`` introduces metavariables for display and subsequent `{lean}` roles
- `{given -show}` for internal (non-displayed) variable introduction
- Pattern: `{given +show}`n : Nat`` then `{lean}`some n`` works
- `{coq}` role (from VersoCoq) links to Flocq documentation
- `{lit}` for literal math notation without validation, but don't overuse for patterns with metavariables
- `@[doc_role]` must define at root namespace for role name to match (e.g., `coq` not `VersoCoq.Roles.coq`)
