# FloatSpec Proof Writing Pipeline

## Key Insights from BooleanComparisons Proof Writing Experience

### 1. The `decide` Pattern for Bool/Prop Compatibility
**Critical Discovery**: When writing Hoare triple specifications that return `Bool`, the postcondition must use `decide` to convert from `Prop` to `Bool`.

```lean
-- WRONG: Type mismatch between Bool and Prop
theorem Zeq_bool_spec (x y : Int) :
    ⦃⌜True⌝⦄
    Zeq_bool x y
    ⦃⇓result => ⌜result = (x = y)⌝⦄  -- Error: (x = y) is Prop, not Bool

-- CORRECT: Using decide for proper type conversion
theorem Zeq_bool_spec (x y : Int) :
    ⦃⌜True⌝⦄
    Zeq_bool x y
    ⦃⇓result => ⌜result = decide (x = y)⌝⦄  -- decide converts Prop to Bool
```

### 2. Standard Proof Pattern for Simple Specifications

For functions that directly compute their specified result, use this pattern:

```lean
theorem function_spec (params) :
    ⦃⌜precondition⌝⦄
    function_call
    ⦃⇓result => ⌜postcondition⌝⦄ := by
  intro _              -- Introduce precondition (use _ if not needed)
  unfold function_name -- Unfold the function definition
  rfl                  -- Reflexivity completes the proof
```

### 3. Incremental Verification Strategy

**ALWAYS** check compilation after EACH proof, not after completing a batch:
1. Write ONE proof
2. Check compilation with `mcp__lean-lsp-mcp__lean_diagnostic_messages`
3. Fix any errors immediately
4. Only then proceed to the next proof

This prevents cascading errors and makes debugging much easier.

### 4. Common Patterns in Boolean Comparison Proofs

#### Pattern A: Direct Boolean Computation
Functions that return `decide (condition)` can be proved with just `unfold` and `rfl`:
```lean
def Zeq_bool (x y : Int) : Id Bool := decide (x = y)
-- Proof: intro _, unfold Zeq_bool, rfl
```

#### Pattern B: Constant Return Functions
Functions that always return a constant need only `unfold` and `rfl`:
```lean
def Zeq_bool_true (_ _ : Int) : Id Bool := true
-- Proof: intro _, unfold Zeq_bool_true, rfl
```

#### Pattern C: Boolean Property Verification
Functions that verify properties (returning `decide (property)`) follow the same pattern:
```lean
def Zle_bool_opp (x y : Int) : Id Bool := decide ((- x ≤ - y) = (y ≤ x))
-- Proof: intro _, unfold Zle_bool_opp, rfl
```

### 5. Type-Checking Hints

When Lean reports type mismatches involving `Bool` and `Prop`:
- If comparing booleans with propositions, use `decide` 
- If the function returns `Bool` but you're asserting a `Prop`, wrap with `decide`
- Remember: `decide : Prop → Bool` for decidable propositions

### 6. Hoare Triple Syntax Reminder

The Hoare triple syntax in this project:
```lean
⦃⌜precondition⌝⦄    -- Precondition (Prop)
computation          -- The computation being specified
⦃⇓result => ⌜postcondition using result⌝⦄  -- Postcondition
```

The `⇓result =>` binds the computation's result for use in the postcondition.

### 7. Proof Development Workflow

1. **Read the function implementation** - Understand what it actually does
2. **Check the specification** - Ensure it matches the implementation
3. **Identify the proof pattern** - Most simple functions use the standard pattern
4. **Write the proof** - Start with the standard pattern
5. **Compile immediately** - Don't accumulate unverified proofs
6. **Fix type issues** - Usually involves adding `decide` for Bool/Prop conversions

### 8. When Proofs Get Complex

For more complex proofs (like `Zfast_div_eucl_spec`), additional tactics may be needed:
- `split` for case analysis on if-then-else
- `have` for intermediate results  
- `calc` for calculation chains
- `simp` for simplification
- Named hypothesis introduction with `intro h` instead of `intro _`

But start simple - many proofs just need `intro _, unfold, rfl`.