# grind Tactic - Automated Proof Search

## Overview

The `grind` tactic is a powerful automated proof tactic in Lean 4 that uses SMT-inspired techniques to discharge goals. It's particularly effective for goals involving:
- Propositional logic
- Congruence closure
- Linear arithmetic
- Case splitting

Reference: https://lean-lang.org/doc/reference/latest/The--grind--tactic/

## Basic Usage

```lean
example (p q : Prop) (h1 : p → q) (h2 : p) : q := by
  grind
```

## Key Features

### 1. Propositional Reasoning

`grind` handles propositional logic automatically:

```lean
example (p q r : Prop) (h1 : p ∨ q) (h2 : p → r) (h3 : q → r) : r := by
  grind
```

### 2. Equality Reasoning (Congruence Closure)

Automatically reasons about equalities:

```lean
example (f : Nat → Nat) (a b : Nat) (h1 : a = b) : f a = f b := by
  grind
```

### 3. Linear Arithmetic

Handles linear arithmetic over naturals and integers:

```lean
example (x y : Nat) (h : x + 1 = y) : y > x := by
  grind
```

### 4. Case Splitting

Automatically performs case splits when needed:

```lean
example (n : Nat) : n = 0 ∨ n > 0 := by
  grind
```

## Configuration

`grind` accepts configuration options:

```lean
-- With specific simp lemmas
grind [lemma1, lemma2]

-- With unfolding hints
grind [↓definition_to_unfold]
```

## When to Use grind

**Good for:**
- Pure verification conditions after mvcgen
- Simple arithmetic and logical goals
- Equality-based reasoning
- Goals with bounded case analysis

**Less effective for:**
- Complex inductions
- Goals requiring domain-specific lemmas
- Non-linear arithmetic
- Goals needing specific rewrite strategies

## Combining with Other Tactics

### With mvcgen

```lean
theorem foo_spec : ... := by
  mvcgen [unfolds...]
  all_goals grind
```

### With mleave

```lean
theorem bar_spec : ... := by
  mvcgen
  all_goals mleave; grind  -- Leave hard goals, grind the rest
```

### As a Finisher

```lean
theorem baz_spec : ... := by
  intro h
  simp [definitions...]
  grind
```

## grind vs Other Tactics

| Tactic | Best For |
|--------|----------|
| `grind` | Propositional + arithmetic + equality |
| `simp` | Term rewriting |
| `omega` | Linear arithmetic only |
| `decide` | Decidable propositions |
| `aesop` | General proof search |

## Examples

### Simple Propositional

```lean
example (p q : Prop) : p ∧ q → q ∧ p := by grind
```

### Arithmetic

```lean
example (a b c : Nat) : a + b + c = c + b + a := by grind
```

### Mixed Reasoning

```lean
example (f : Nat → Nat) (x y : Nat)
    (h1 : x = y) (h2 : f x > 0) : f y > 0 := by grind
```

### With Custom Lemmas

```lean
@[grind] theorem my_lemma : ... := ...

example : ... := by grind  -- Uses my_lemma automatically
```

## Troubleshooting

If `grind` doesn't work:

1. **Add simp lemmas**: `grind [lemma1, lemma2]`
2. **Unfold definitions**: `grind [↓myDef]`
3. **Split manually first**: `cases h <;> grind`
4. **Use `grind?`** to see what lemmas might help
5. **Fall back to manual proof** for complex cases

## Integration with Verification

In verification workflows (e.g., with mvcgen), `grind` is typically used to discharge pure goals:

```lean
theorem program_correct : ... := by
  mvcgen [program_unfolds...]
  case goal1 => grind
  case goal2 => grind [specific_lemma]
  case hard_goal => -- manual proof
```
