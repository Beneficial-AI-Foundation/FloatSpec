# mvcgen Tactic - Monadic Verification Condition Generator

## Overview

The `mvcgen` tactic implements a monadic verification condition generator that breaks down goals involving imperative programs written using Lean's `do` notation into pure verification conditions.

Reference: https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/Tutorial___-Verifying-Imperative-Programs-Using--mvcgen/

## Key Features

- **Monadic verification**: Handles programs with local mutability, for loops, and early returns
- **Hoare triple support**: Specifications use the notation `⦃P⦄ prog ⦃Q⦄` for pre/postconditions
- **Loop invariants**: Supports specifying invariants for loops using zipper data structures
- **Compositional reasoning**: Allows building specifications for individual monadic functions
- **Monad transformer stacks**: Works with StateT, ReaderT, ExceptT and custom monad combinations

## Imports Required

```lean
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do
```

## Hoare Triple Notation

```lean
⦃⌜P⌝⦄ prog ⦃⇓result => ⌜Q⌝⦄
```

- `⌜P⌝` - Precondition (pure proposition lifted into SPred)
- `prog` - Monadic program
- `⇓result` - Binds the result value
- `⌜Q⌝` - Postcondition (can reference result)

## The @[spec] Attribute

Mark specification lemmas with `@[spec]` to make them available for automatic lookup:

```lean
@[spec]
theorem myFunc_spec (x : Nat) :
    ⦃⌜x > 0⌝⦄
    myFunc x
    ⦃⇓r => ⌜r > x⌝⦄ := by
  ...
```

## Pure Functions with Id Monad

**Key Pattern**: For pure functions, use `Id` monad wrapper ONLY in specs:

```lean
-- Pure function returning a plain type
def myPureFunc (n : Nat) : Nat := n + 1

-- Spec wraps with (pure ... : Id T) for mvcgen compatibility
@[spec]
theorem myPureFunc_spec (n : Nat) :
    ⦃⌜True⌝⦄
    (pure (myPureFunc n) : Id Nat)
    ⦃⇓r => ⌜r = n + 1⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, myPureFunc]
```

**Why Id?** `mvcgen` requires SOME monad, even for pure functions. `Id` is the trivial monad.

**Pattern Summary**:
- Functions: Return pure types (Bool, Prop, etc.)
- Specs: Wrap with `(pure ... : Id T)`
- DON'T: Make functions return `Id T` directly (ugly)

## Basic Usage Pattern

```lean
theorem program_correct : program_spec := by
  generalize h : (program args) = result
  apply MonadType.of_wp_run_eq h  -- Focus on monadic part
  mvcgen [unfold_hints]           -- Generate verification conditions
  case inv1 => exact invariant_spec  -- Specify loop invariants
  all_goals mleave; grind         -- Discharge pure goals
```

## Example: Simple Specification

```lean
def increment (x : Nat) : Nat := x + 1

@[spec]
theorem increment_spec (x : Nat) :
    ⦃⌜True⌝⦄
    (pure (increment x) : Id Nat)
    ⦃⇓r => ⌜r = x + 1⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, increment]
```

## Example: Boolean Check

```lean
def isPositive (n : Int) : Bool := n > 0

@[spec]
theorem isPositive_spec (n : Int) :
    ⦃⌜True⌝⦄
    (pure (isPositive n) : Id Bool)
    ⦃⇓r => ⌜r = true ↔ n > 0⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, isPositive]
  decide
```

## Loop Invariants

Use zipper data structures for loop invariants:
- `xs.pref` - Processed elements
- `xs.suff` - Remaining elements
- Early returns supported with `Invariant.withEarlyReturn`

## Common Tactics After mvcgen

```lean
mvcgen [unfolds...]
all_goals mleave    -- Leave unresolved goals for manual proof
all_goals grind     -- Use grind to discharge pure goals
```

## Useful Simp Lemmas

```lean
simp [wp, PostCond.noThrow, Id.run, pure, bind]
```

## Compositional Specifications

Build up specifications for complex programs by specifying individual functions:

```lean
@[spec] theorem f_spec : ... := ...
@[spec] theorem g_spec : ... := ...

-- mvcgen automatically uses f_spec and g_spec when verifying:
theorem composed_spec :
    ⦃P⦄ do let x ← f; g x ⦃Q⦄ := by
  mvcgen
```

## State-Dependent Invariants

For stateful programs, invariants can reference monadic state through function arguments.
