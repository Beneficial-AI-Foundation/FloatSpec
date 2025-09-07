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

## Digits Proofs Playbook (Core Lessons + Steps)

This section distills what worked when proving theorems in `FloatSpec/src/Core/Digits.lean` (e.g., `digits2_Pnat_correct`) and similar arithmetic specs.

### A. Strategy Patterns That Worked Well

- Pure-helper equality: Prove that the monadic program equals a pure function, then reduce the Hoare triple to a pure proposition.
  - Example: define a total helper `bits : Nat → Nat` mirroring the recursion and prove `digits2_Pnat n = pure (bits n)` via `Nat.strongRecOn`.
- Strong induction with divide-by-2: Use `Nat.strongRecOn` + split by `n = 2*(n/2) + n%2`.
  - Lemma to reuse: `split2 (n) : n = 2 * (n / 2) + n % 2 ∧ n % 2 < 2` (wraps `Nat.div_add_mod`).
  - Strict decrease: `((k+1)/2) < (k+1)` via `Nat.div_lt_self`.
- Calc over simp for tricky rewrites: Prefer explicit `calc` chains to avoid `simp` recursion blowups.
  - Rewrite helpers that avoid loops:
    - `2^(k+1) = 2 * 2^k` (`Nat.pow_succ`).
    - If `k > 0`, then `2^k = 2 * 2^(k-1)` (index manipulation via `Nat.sub_add_cancel`).
    - `2*m + 2 = 2*(m+1)` via a short `calc` using `Nat.mul_add` rather than `simp`.
- Index translation for recursive definitions: When you have `bits (n) = 1 + bits (n/2)`, translate bounds using an explicit index identity like `(1 + x) - 1 = x`.

### B. Minimal Lemmas To Scaffold Arithmetic Proofs

- `bits_succ`: `bits (k + 1) = 1 + bits ((k + 1) / 2)` (by `simp` on the definition).
- `digits2_eq_bits`: `digits2_Pnat n = pure (bits n)` (by `Nat.strongRecOn`, apply recursion on `(n+1)/2`).
- `split2`: `n = 2*(n/2) + n%2 ∧ n%2 < 2` (wrap `Nat.div_add_mod`).
- `div2_lt_self_succ`: `((k+1)/2) < (k+1)` (via `Nat.div_lt_self`).
- Power rewrites: `2^(k+1) = 2 * 2^k`, and for `k>0`, `2^k = 2 * 2^(k-1)`.

### C. Hoare Triples: Reducing to Pure Facts

For `⦃P⦄ prog ⦃⇓d => Q d⦄`, if you can show `prog = pure f`, rewrite the triple to prove `Q (f)` under `P`. This keeps executable specs clean and proofs robust.

### D. Common Pitfalls + Fixes

- `simp` recursion depth reached: Replace with explicit `calc` and small helper equalities; avoid heavy `simpa` chains over composite equalities.
- Nat index off-by-one: Use explicit equalities like `((k-1)+1 = k)` to move between `2^k` and `2^(k-1)` safely.
- When rewriting `n` via `n = 2*m + r`, make all later rewrites refer back to this named equality to avoid goal drift.

### E. Restart Checklist (Context-Free Boot Sequence)

Use this when picking up proofs without prior context:

1) Read: `PIPELINE.md` (this file) and `CLAUDE.md` (mvcgen + proof notes).
2) Build once: `lake build` to surface current error locations.
3) Pick one target theorem only; do not batch.
4) Verify the function body and spec match (do not change triple syntax unless necessary).
5) If the proof is complex, sketch helper lemmas first (see B), prove them, build.
6) Reduce monadic specs to pure goals via a helper equality if applicable.
7) Prefer `calc` + small rewrites over aggressive `simp/simpa` on composite goals.
8) After every small step: build. Fix issues immediately.
9) If stuck on an algebraic step: add a tiny lemma with a direct proof rather than fighting `simp`.
10) Keep the “one-proof-at-a-time” rhythm until the file compiles cleanly.

### F. Commands / Quick Actions

- Build project: `lake build`
- Locate diagnostics (LSP): use your editor’s Lean diagnostics pane; keep the loop fast.
- Search for prior lemmas in the file to avoid duplicate work.

Following this playbook consistently kept proofs small, maintainable, and debuggable.
