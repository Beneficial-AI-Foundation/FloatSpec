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

Use `uvx lean-lsp-mcp` to get feedback on your code. Usage:

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
lake build        # Local Lean build (primary workflow)
uv run -m pytest -q  # Run tests directly

# Check Lean syntax and types
lake build --verbose
```

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

### Next Priorities for FloatSpec

1. **IEEE 754 Types**: Define bit-accurate floating-point representations
2. **Basic Operations**: Implement addition, subtraction, multiplication, division
3. **Rounding Modes**: Support for different IEEE 754 rounding modes
4. **Special Values**: Proper handling of infinity, NaN, and zero
5. **Error Analysis**: Formal bounds on numerical errors

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