# Pipeline for Generating Lean 4 Specifications from Flocq Documentation

## Overview

This document provides a systematic process for generating Vector-based Lean 4 specifications with Hoare triple syntax from Flocq function documentation and source code. The pipeline produces formal specifications that capture the mathematical properties of Flocq operations.

## Essential Concepts

### 1. Hoare Triple Syntax in Lean 4

The new syntax uses special brackets for pre/post conditions:
```lean
⦃⌜precondition⌝⦄ function ⦃⇓result => postcondition⦄
```

- `⦃⌜...⌝⦄` - Precondition wrapped in special brackets
- `⦃⇓result => ...⦄` - Postcondition with bound result variable
- Always end theorems with `:= by sorry` during specification phase

### 2. Array to Vector Transformation Rules

| Array Pattern | Vector Pattern |
|--------------|----------------|
| `Array T` | `Vector T n` |
| `a : Array Int` | `{n : Nat} (a : Vector Int n)` |
| `(h : a.size = b.size)` | Remove (enforced by type) |
| `a.size > 0` | Use `Vector T (n + 1)` |
| `∀ i (hi : i < a.size)` | `∀ i : Fin n` |
| `a[i]'hi` | `a.get i` |
| `∃ hr : res.size = a.size` | Remove (types match) |

## Complete Examples

### Example 1: Binary Operation (Addition)

**Array Version:**
```lean
def add (a b : Array Int): Id (Array Int) :=
  sorry

theorem add_spec (a b : Array Int) (h : a.size = b.size) :
    ⦃⌜a.size = b.size⌝⦄
    add a b
    ⦃⇓r => ∃ hr : r.size = a.size, ∀ i (hi : i < r.size), r[i] = a[i] + b[i]⦄ := by
  sorry
```

**Vector Version:**
```lean
/-- Element-wise addition of two vectors

    Computes the sum of two vectors by adding corresponding elements:
    result[i] = a[i] + b[i] for all valid indices i

    This operation is:
    - Commutative: add(a, b) = add(b, a)
    - Associative: add(add(a, b), c) = add(a, add(b, c))
    - Has identity element: add(a, zeros) = a
-/
def add {n : Nat} (a b : Vector Int n) : Id (Vector Int n) :=
  sorry

/-- Specification: Element-wise addition produces correct sums

    The addition operation satisfies:
    1. Each element of the result is the sum of corresponding input elements
    2. The operation preserves vector length (enforced by type system)
    3. No overflow checking is performed (uses mathematical integers)
-/
theorem add_spec {n : Nat} (a b : Vector Int n) :
    ⦃⌜True⌝⦄
    add a b
    ⦃⇓r => ∀ i : Fin n, r.get i = a.get i + b.get i⦄ := by
  sorry
```

### Example 2: Unary Operation Requiring Non-empty (Maximum)

**Array Version:**
```lean
def max (a : Array Int) : Id Int :=
  sorry

theorem max_spec (a : Array Int) (h : a.size > 0) :
    ⦃⌜a.size > 0⌝⦄
    max a
    ⦃⇓res => ∃ i : Nat, ∃ hi : i < a.size, res = a[i]'hi ∧
             ∀ j : Nat, ∀ hj : j < a.size, a[j]'hj ≤ res⦄ := by
  sorry
```

**Vector Version:**
```lean
/-- Find the maximum element in a non-empty vector

    Returns the largest element in the vector. For vectors containing
    multiple occurrences of the maximum value, any of them may be returned.
    
    The type Vector Int (n + 1) ensures the vector is non-empty at compile time,
    eliminating the need for runtime checks.
-/
def max {n : Nat} (a : Vector Int (n + 1)) : Id Int :=
  sorry

/-- Specification: Maximum element satisfies ordering constraints

    The maximum operation ensures:
    1. The returned value exists in the vector (witness: index i)
    2. No element in the vector is larger than the returned value
    3. The operation is well-defined for non-empty vectors (enforced by type)
    
    Note: When multiple elements equal the maximum, any valid index may be chosen.
-/
theorem max_spec {n : Nat} (a : Vector Int (n + 1)) :
    ⦃⌜True⌝⦄
    max a
    ⦃⇓res => ∃ i : Fin (n + 1), res = a.get i ∧
             ∀ j : Fin (n + 1), a.get j ≤ res⦄ := by
  sorry
```

## Step-by-Step Workflow

### 1. Initial Setup
```bash
mkdir -p DafnySpecs/dfy_syntax_from_doc
```

### 2. File-by-File Conversion Process

For each file:

1. **Read the original Array version**
   ```lean
   -- Identify: function signature, preconditions, postconditions
   ```

2. **Create the Vector version header**
   ```lean
   import Std.Do.Triple
   import Std.Tactic.Do
   
   open Std.Do
   ```

3. **Transform the function signature**
   - Add `{n : Nat}` parameter for vector size
   - Replace `Array T` with `Vector T n`
   - For non-empty requirements, use `Vector T (n + 1)`
   - Remove size equality parameters

4. **Transform the specification**
   - Simplify preconditions (usually to `⌜True⌝`)
   - Remove existential size proofs
   - Replace index types with `Fin n`
   - Use `.get` for element access

5. **Compile and verify**
   ```bash
   lake build  # Check for compilation errors
   ```

### 3. Common Patterns

#### Binary Operations (Equal Size)
```lean
/-- Generic pattern for element-wise binary operations

    Applies a binary function f : T → T → R element-wise to two vectors
    of the same length. Common examples include:
    - Addition: f(x, y) = x + y
    - Multiplication: f(x, y) = x * y
    - Maximum: f(x, y) = max(x, y)
    
    The type system ensures both input vectors have identical length.
-/
def op {n : Nat} (a b : Vector T n) : Id (Vector R n) :=
  sorry

/-- Specification: Element-wise operations preserve structure

    The binary operation satisfies:
    1. Each output element is computed by applying f to corresponding inputs
    2. Output vector has the same length as inputs (type-enforced)
    3. The operation is deterministic and pure
    
    This pattern captures most Coq binary function behavior.
-/
theorem op_spec {n : Nat} (a b : Vector T n) :
    ⦃⌜True⌝⦄
    op a b
    ⦃⇓r => ∀ i : Fin n, r.get i = f (a.get i) (b.get i)⦄ := by
  sorry
```

#### Operations with Non-zero Preconditions
```lean
/-- Element-wise integer division of two vectors

    Performs integer division a[i] / b[i] for each element.
    Requires all divisors to be non-zero to avoid undefined behavior.
    
    In Lean, integer division rounds towards negative infinity (floor division),
    matching Python's // operator rather than C's truncation behavior.
-/
def divide {n : Nat} (a b : Vector Int n) : Id (Vector Int n) :=
  sorry

/-- Specification: Division requires non-zero divisors

    The division operation ensures:
    1. Each result element is the integer quotient of corresponding inputs
    2. Precondition enforces all divisors are non-zero
    3. Division semantics follow Lean's floor division rules
    
    For example: (-7) / 3 = -3 (not -2 as in truncating division)
-/
theorem divide_spec {n : Nat} (a b : Vector Int n) 
    (h_nonzero : ∀ i : Fin n, b.get i ≠ 0) :
    ⦃⌜∀ i : Fin n, b.get i ≠ 0⌝⦄
    divide a b
    ⦃⇓r => ∀ i : Fin n, r.get i = a.get i / b.get i⦄ := by
  sorry
```

#### Index-returning Operations
```lean
/-- Find the index of the maximum element (first occurrence)

    Returns the index of the first element that equals the maximum value.
    For vectors with multiple maxima, returns the smallest valid index.
    
    This matches Coq's behavior of returning the first occurrence
    when scanning from index 0.
-/
def argmax {n : Nat} (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  sorry

/-- Specification: argmax returns the first index of the maximum

    The argmax operation ensures:
    1. The element at the returned index equals the maximum value
    2. All elements before the returned index are strictly smaller
    3. This guarantees we return the first occurrence of the maximum
    
    This specification captures Coq's left-to-right scanning behavior.
-/
theorem argmax_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    argmax a
    ⦃⇓idx => a.get idx = max a ∧ 
            ∀ j : Fin (n + 1), j < idx → a.get j < a.get idx⦄ := by
  sorry
```

## Critical Success Factors

### 1. Type-Level Size Management
- Use implicit `{n : Nat}` parameters
- Let Lean infer sizes when possible
- Use `(n + 1)` pattern for non-empty constraints

### 2. Proof Simplification
- Vector types eliminate size equality proofs
- `Fin n` eliminates bounds checking proofs
- Focus specifications on actual behavior, not size management

### 3. Compilation Verification
- **Always** check compilation after each file
- Fix errors immediately before proceeding
- Common fixes:
  - Missing parentheses around array accesses
  - Incorrect proof term transformations
  - Type mismatches in index operations

### 4. Special Cases

#### 2D Arrays
```lean
/-- Flatten a 2D matrix into a 1D vector (row-major order)

    Converts a matrix of shape (rows × cols) into a vector of length rows*cols.
    Elements are arranged in row-major order (C-style), meaning we traverse
    all columns of row 0, then all columns of row 1, etc.
    
    For a 2×3 matrix [[a,b,c], [d,e,f]], the result is [a,b,c,d,e,f].
-/
def flatten {rows cols : Nat} 
    (mat : Vector (Vector Int cols) rows) : 
    Id (Vector Int (rows * cols)) :=
  sorry

/-- Specification: Flatten preserves elements in row-major order

    The flattening operation ensures:
    1. Element at position (i,j) in the matrix appears at position i*cols + j
    2. All elements are preserved without duplication or loss
    3. The output length equals rows × cols
    
    This matches Coq's default 'C' order flattening behavior.
-/
theorem flatten_spec {rows cols : Nat}
    (mat : Vector (Vector Int cols) rows) :
    ⦃⌜True⌝⦄
    flatten mat
    ⦃⇓v => ∀ (i : Fin rows) (j : Fin cols),
        v.get ⟨i.val * cols + j.val, sorry⟩ = (mat.get i).get j⦄ := by
  sorry
```

#### Dynamic Size Computation
```lean
/-- Generate evenly spaced values within a given interval

    Creates a vector of n values starting at 'start', incrementing by 'step',
    where n is determined by the formula: floor((stop - start) / step).
    
    Similar to Coq's arange but with size specified at type level.
    The last value is start + (n-1)*step, which is less than stop.
-/
def arange {n : Nat} (start stop step : Float) : Id (Vector Float n) :=
  sorry

/-- Specification: arange generates arithmetic progression

    The arange operation ensures:
    1. First element equals start
    2. Each subsequent element increases by step
    3. All generated values are less than stop
    4. The number of elements matches the computed size
    
    For example: arange(0, 5, 1.5) produces [0, 1.5, 3, 4.5]
-/
theorem arange_spec {n : Nat} (start stop step : Float) 
    (h_size : n = ((stop - start)/step).floor.toUInt64.toNat)
    (h_step_pos : step > 0) :
    ⦃⌜n = ((stop - start)/step).floor.toUInt64.toNat ∧ step > 0⌝⦄
    arange start stop step
    ⦃⇓v => (n > 0 → v.get ⟨0, sorry⟩ = start) ∧
           (∀ i : Fin n, v.get i = start + i.val.toFloat * step) ∧
           (∀ i : Fin n, v.get i < stop)⦄ := by
  sorry
```

## Common Pitfalls and Solutions

1. **Forgetting to wrap array accesses in parentheses**
   - Wrong: `a[i]'proof + b[i]'proof`
   - Right: `(a[i]'proof) + (b[i]'proof)`

2. **Using wrong index types**
   - Wrong: `∀ i : Nat, i < n → ...`
   - Right: `∀ i : Fin n, ...`

3. **Keeping unnecessary size proofs**
   - Wrong: `∃ hr : r.size = a.size, ...`
   - Right: Just use the postcondition directly

4. **Complex index proof terms**
   - Wrong: `a[i]'(hr ▸ h ▸ hi)`
   - Right: `a.get i` (with Vectors)

## Automation Strategy

When converting many files:

1. Start with 2-3 manual conversions to establish patterns
2. Create sub-agents for batches of similar files
3. Group files by operation type:
   - Binary operations (add, multiply, compare)
   - Unary operations (abs, sign, square)
   - Reductions (sum, max, argmax)
   - Special operations (reshape, flatten)

## Final Checklist

- [ ] All imports are correct
- [ ] Return type uses `Id` monad
- [ ] Specification uses ⦃⌜...⌝⦄ syntax
- [ ] Postcondition binds result with ⇓
- [ ] All array accesses use `.get`
- [ ] Indices use `Fin n` type
- [ ] File compiles with only `sorry` warnings
- [ ] No unnecessary size equality proofs
- [ ] The file could pass the lean4 compiler, you can use mcp tool to check the file.

## Input Format

The input will be a JSON object containing:
```json
{
  "name": "coq.function_name",
  "description": "Brief description",
  "url": "https://coq.inria.fr/doc/...",
  "doc": "Full documentation string with parameters and returns",
  "code": "Python implementation"
}
```

## Output Format

Generate a Lean 4 specification file with:
1. Required imports
2. Function definition with `sorry` implementation
3. Specification theorem using Hoare triple syntax
4. Save to: `DafnySpecs/dfy_syntax_from_doc/Coq_FunctionName.lean`

## Generation Process

### Step 1: Parse the Documentation

From the `doc` field, extract:
- **Parameters**: Types and constraints
- **Returns**: Type and properties
- **Behavior**: What the function computes

### Step 2: Determine Lean Types

| Coq Type | Lean Type | Notes |
|------------|-----------|-------|
| `array_like` | `Vector T n` | Use implicit `{n : Nat}` |
| `ndarray of ints` | `Vector Int n` | |
| `ndarray of floats` | `Vector Float n` | |
| `int` (index) | `Fin n` | Type-safe index |
| `axis` parameter | Omit for now | Focus on 1D |

### Step 3: Identify Preconditions

Common preconditions to check for:
- Non-empty array: Use `(h : n > 0)` parameter or `Vector T (n + 1)`
- Value constraints: e.g., `∀ i : Fin n, v.get i ≠ 0`
- Size relationships: Handled by type system with Vectors

### Step 4: Generate the Specification

Template:
```lean
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- [Description from doc] -/
def functionName {n : Nat} (params...) : Id ReturnType :=
  sorry

/-- Specification: [describe what function does] -/
theorem functionName_spec {n : Nat} (params...) (preconditions...) :
    ⦃⌜precondition_formula⌝⦄
    functionName params
    ⦃⇓result => postcondition_formula⦄ := by
  sorry
```

### Step 5: Supply Natural Language Explanations

After generating the spec, add comprehensive documentation comments that explain:
- The mathematical formula being implemented
- What each parameter represents
- The properties the specification captures
- Any helper functions used

Example:
```lean
/-- Compute the one-dimensional discrete Fourier Transform

    The FFT computes the DFT defined as:
    X[k] = Σ(n=0 to N-1) x[n] * exp(-2πi*k*n/N)

    where:
    - x is the input vector
    - X is the output vector
    - N is the length of the vector
    - i is the imaginary unit
-/
def fft {n : Nat} (a : Vector Complex n) : Id (Vector Complex n) :=
  sorry

/-- Specification: FFT computes the discrete Fourier transform

    The FFT satisfies the DFT equation and has the following properties:
    1. Each output element is the sum of input elements weighted by complex exponentials
    2. The transform is linear
    3. Parseval's theorem: energy is preserved (with proper normalization)
    4. FFT(FFT^(-1)(x)) = x (inverse property when combined with IFFT)

    The specification captures the fundamental DFT formula where each output
    element k is computed as the sum over all input elements j, multiplied
    by the complex exponential exp(-2πi*k*j/n).
-/
theorem fft_spec {n : Nat} (a : Vector Complex n) (h : n > 0) :
    ⦃⌜n > 0⌝⦄
    fft a
    ⦃⇓result => ⌜∀ k : Fin n,
        result.get k = complexSum (fun j =>
            a.get j * cexp (-2 * (3.14159265358979323846 : Float) * (k.val.toFloat * j.val.toFloat) / n.toFloat)) ∧
        -- Sanity check: output vector has same length as input
        result.size = n ∧
        -- FFT preserves the DC component (k=0) correctly
        (n > 0 → result.get ⟨0, h⟩ = complexSum (fun j => a.get j)) ∧
        -- FFT satisfies the fundamental DFT property for each frequency component
        (∀ k : Fin n, ∃ (sum : Complex), 
            sum = complexSum (fun j => a.get j * cexp (-2 * (3.14159265358979323846 : Float) * (k.val.toFloat * j.val.toFloat) / n.toFloat)) ∧
            result.get k = sum)⌝⦄ := by
  sorry
```

This documentation should:
- Explain the mathematical background
- Clarify any complex formulas
- Make the spec accessible to readers unfamiliar with the specific algorithm
- Include any assumptions or simplifications made

## Complete Example: coq.argmax

**Input:**
```json
{
  "name": "coq.argmax",
  "description": "Returns the indices of the maximum values along an axis.",
  "doc": "coq.argmax(a, axis=None, out=None, *, keepdims=<no value>)\n\nReturns the indices of the maximum values along an axis.\n\nParameters:\n- a : array_like\n  Input array.\n- axis : int, optional\n  By default, the index is into the flattened array.\n\nReturns:\n- index_array : ndarray of ints\n  Array of indices into the array.",
  "code": "..."
}
```

**Output:**
```lean
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Returns the index of the maximum value in a vector (first occurrence)

    Scans the vector from left to right and returns the index of the first
    element that equals the maximum value. This matches Coq's behavior
    where ties are broken by returning the smallest index.
    
    The parameter h : n > 0 ensures the vector is non-empty, making the
    operation well-defined. The return type Fin n guarantees the index
    is valid for the given vector.
-/
def argmax {n : Nat} (arr : Vector Float n) (h : n > 0) : Id (Fin n) :=
  sorry

/-- Specification: argmax returns the index of the first maximum element

    The argmax operation satisfies the following properties:
    1. Maximality: No element in the vector is larger than arr[argmax(arr)]
    2. First occurrence: All elements before the returned index are strictly
       less than the maximum (ensuring we return the first occurrence)
    3. Existence: The returned index is valid (guaranteed by type Fin n)
    
    This specification precisely captures Coq's argmax behavior for 1D arrays,
    including the tie-breaking rule that favors smaller indices.
-/
theorem argmax_spec {n : Nat} (arr : Vector Float n) (h : n > 0) :
    ⦃⌜n > 0⌝⦄
    argmax arr h
    ⦃⇓ret => (∀ i : Fin n, i < ret → arr.get ret > arr.get i) ∧
             (∀ i : Fin n, ret < i → arr.get ret ≥ arr.get i)⦄ := by
  sorry
```

Save as: `DafnySpecs/dfy_syntax_from_doc/Coq_Argmax.lean`

## Specification Patterns by Function Type

### 1. Element-wise Operations (add, multiply, abs)
```lean
/-- Generic element-wise operation pattern

    Applies a function f element-wise to input vectors. This pattern
    covers binary operations (add, multiply) and unary operations (abs, sign).
    The function f determines the specific operation performed.
-/
def op {n : Nat} (a b : Vector T n) : Id (Vector T n) :=
  sorry

/-- Specification: Element-wise operations apply f to each position

    This pattern ensures that each element of the result is computed
    by applying function f to the corresponding input elements.
    Common instances include arithmetic operations and comparisons.
-/
theorem op_spec {n : Nat} (a b : Vector T n) :
    ⦃⌜True⌝⦄
    op a b
    ⦃⇓r => ∀ i : Fin n, r.get i = f (a.get i) (b.get i)⦄ := by
  sorry
```

### 2. Reduction Operations (sum, max, min)
```lean
/-- Generic reduction operation pattern

    Reduces a vector to a single value by applying an associative operation.
    The type (n + 1) ensures the vector is non-empty, making reductions
    well-defined. Common reductions include sum, product, max, and min.
-/
def reduce {n : Nat} (arr : Vector T (n + 1)) : Id T :=
  sorry

/-- Specification: Reductions aggregate all elements

    The specific property depends on the reduction operation:
    - Sum: result = arr[0] + arr[1] + ... + arr[n]
    - Max: result ≥ all elements, and result ∈ arr
    - Product: result = arr[0] * arr[1] * ... * arr[n]
    
    Non-empty vectors ensure the reduction is always defined.
-/
theorem reduce_spec {n : Nat} (arr : Vector T (n + 1)) :
    ⦃⌜True⌝⦄
    reduce arr
    ⦃⇓res => property_of_result⦄ := by
  sorry
```

### 3. Index-returning Operations (argmax, argmin)
```lean
/-- Generic pattern for operations returning indices

    Returns the index of an element satisfying some extremal property.
    The proof h : n > 0 ensures the vector is non-empty, and the return
    type Fin n guarantees the index is valid. Ties are typically broken
    by returning the first occurrence.
-/
def argop {n : Nat} (arr : Vector T n) (h : n > 0) : Id (Fin n) :=
  sorry

/-- Specification: Index operations return valid extremal indices

    The returned index satisfies an extremal property:
    - argmax: arr[idx] is maximal, first occurrence for ties
    - argmin: arr[idx] is minimal, first occurrence for ties
    - argsort: returns permutation indices for sorted order
    
    The specification must capture both the extremal property and
    the tie-breaking behavior (usually first occurrence).
-/
theorem argop_spec {n : Nat} (arr : Vector T n) (h : n > 0) :
    ⦃⌜n > 0⌝⦄
    argop arr h
    ⦃⇓idx => property_of_index⦄ := by
  sorry
```

### 4. Array Generation (zeros, ones, arange)
```lean
/-- Generic pattern for array generation functions

    Creates a new vector of specified size with elements following a pattern.
    Common generators include:
    - zeros/ones: constant values
    - arange: arithmetic progression
    - linspace: evenly spaced values
    - random: values from a distribution
-/
def generate (n : Nat) (params...) : Id (Vector T n) :=
  sorry

/-- Specification: Generated arrays follow predictable patterns

    Each element is computed by a formula depending on its index:
    - zeros: arr[i] = 0
    - ones: arr[i] = 1
    - arange(start, step): arr[i] = start + i * step
    - linspace(start, stop, n): arr[i] = start + i * (stop - start) / (n - 1)
    
    The specification captures the generation formula precisely.
-/
theorem generate_spec (n : Nat) (params...) :
    ⦃⌜constraints_on_params⌝⦄
    generate n params
    ⦃⇓arr => ∀ i : Fin n, arr.get i = formula⦄ := by
  sorry
```

## Key Decisions When Generating

1. **Parameter Selection**: 
   - Ignore `axis`, `out`, `keepdims` for 1D specifications
   - Focus on core mathematical behavior

2. **Type Selection**:
   - Use `Float` for general numeric operations
   - Use `Int` for index operations
   - Use `Bool` for comparison results

3. **Precondition Extraction**:
   - "non-empty" → `(h : n > 0)` or `Vector T (n + 1)`
   - "positive values" → `∀ i : Fin n, arr.get i > 0`
   - Division operations → non-zero divisors

4. **Postcondition Formulation**:
   - Express the mathematical property precisely
   - Use `∀ i : Fin n` for element-wise properties
   - Use `∃ i : Fin n` for existence properties

## File Naming Convention

For Coq function `coq.function_name`:
- File: `Coq_FunctionName.lean`
- Location: `DafnySpecs/dfy_syntax_from_doc/`
- Examples:
  - `coq.argmax` → `Coq_Argmax.lean`
  - `coq.array_equal` → `Coq_ArrayEqual.lean`
  - `coq.dot` → `Coq_Dot.lean`

## Generation Prompt Template

"Given the Coq function documentation below, generate a Lean 4 specification using Vector types and Hoare triple syntax. Extract the core mathematical behavior from the documentation, determine appropriate preconditions, and express the postcondition precisely. Include comprehensive natural language explanations in the documentation comments that explain the mathematical formulas, parameters, and properties captured by the specification. Save the output to `DafnySpecs/dfy_syntax_from_doc/Coq_[FunctionName].lean`. Focus on 1D array behavior and ignore parameters like axis, out, and keepdims."

## Checklist for Generated Specifications

- [ ] Imports are present: `Std.Do.Triple` and `Std.Tactic.Do`
- [ ] Function name follows Lean conventions (camelCase)
- [ ] Appropriate use of `{n : Nat}` for vector sizes
- [ ] Preconditions correctly extracted from documentation
- [ ] Postcondition captures the mathematical property
- [ ] Natural language explanations provided for both definition and specification
- [ ] Mathematical formulas clearly explained in comments
- [ ] File saved with correct naming convention
- [ ] All functions end with `:= sorry`
- [ ] All theorems end with `:= by sorry`

## Writing Formal Proofs

### Pre-Proof Verification

Before writing formal proofs, always verify the function implementation:

1. **Test Function Behavior First**
   - Check that the function itself compiles and works correctly
   - Use `#eval` to test simple cases
   - Verify the function logic matches the specification
   - Fix any implementation issues before attempting proofs

2. **Use MCP Tools for Lean Feedback**
   - `mcp__lean-lsp-mcp__lean_diagnostic_messages`: Get all diagnostic messages (errors, warnings, infos) for the file
   - `mcp__lean-lsp-mcp__lean_goal`: Check the proof state at specific locations
   - `mcp__lean-lsp-mcp__lean_hover_info`: Get documentation about Lean syntax and functions
   - `mcp__lean-lsp-mcp__lean_leansearch`: Search for relevant theorems using natural language
   - `mcp__lean-lsp-mcp__lean_loogle`: Search for lemmas by name, type, or pattern
   - `mcp__lean-lsp-mcp__lean_state_search`: Find theorems based on current proof state

3. **Incremental Proof Development**
   - Start with `sorry` and gradually fill in proof steps
   - Use named holes (`?holeName`) to work on parts incrementally
   - Check compilation after each significant change
   - Keep proofs simple - let tactics like `simp`, `grind`, and `canonical` do the heavy lifting

### Proof Writing Process

1. **Analyze the Goal**
   ```lean
   -- Use lean_goal to see what needs to be proved
   -- Check at line before and after key positions
   ```

2. **Search for Relevant Lemmas**
   ```lean
   -- Use lean_leansearch with natural language descriptions
   -- Use lean_loogle for pattern-based searches
   -- Use lean_state_search when stuck in a proof
   ```

3. **Write the Proof Incrementally**
   ```lean
   theorem my_theorem : ... := by
     -- Step 1: Unfold definitions
     unfold my_function
     -- Check goal state with lean_goal
     
     -- Step 2: Apply relevant lemmas
     apply some_lemma
     -- Check new goal state
     
     -- Step 3: Simplify
     simp
     -- Check if solved or what remains
     
     sorry  -- For remaining goals
   ```

4. **Compile and Debug**
   - After each proof step, run `lake build` to check for errors
   - Use `lean_diagnostic_messages` to understand any issues
   - If stuck, use `lean_hover_info` to understand syntax or functions

### Common Proof Patterns in FloatSpec

1. **Hoare Triple Proofs**
   ```lean
   theorem spec : ⦃⌜precondition⌝⦄ function ⦃⇓result => postcondition⦄ := by
     -- Usually start by unfolding the function definition
     unfold function
     -- Apply Hoare triple rules
     -- Prove precondition implies postcondition
     sorry
   ```

2. **Integer/Real Properties**
   ```lean
   -- For integer division/modulo
   use Int.emod_add_ediv, Int.ediv_add_emod
   
   -- For real number properties
   use Real.sqrt_sq, Real.sq_sqrt
   
   -- For inequalities
   use linarith, omega
   ```

3. **Induction Proofs**
   ```lean
   -- For natural numbers
   induction n with
   | zero => sorry
   | succ n ih => sorry
   
   -- For lists/vectors
   induction v with
   | nil => sorry
   | cons h t ih => sorry
   ```

### Debugging Tips

1. **When Proofs Don't Compile**
   - Check exact error with `lean_diagnostic_messages`
   - Verify all imports are present
   - Ensure theorem statement matches function signature
   - Check that preconditions are properly stated

2. **When Stuck in a Proof**
   - Use `lean_goal` to see current proof state
   - Try `lean_state_search` to find applicable lemmas
   - Simplify the goal with `simp` or `grind`
   - Break complex goals into smaller lemmas

3. **Performance Issues**
   - Avoid deep recursion in proofs
   - Use `simp only [specific_lemmas]` instead of bare `simp`
   - Consider marking functions as `noncomputable` if needed

### Best Practices

1. **Always compile after each change** - Don't accumulate errors
2. **Use MCP tools liberally** - They provide crucial feedback
3. **Start simple** - Prove basic properties before complex ones
4. **Document proof strategies** - Add comments explaining key steps
5. **Reuse proven lemmas** - Build a library of helper lemmas

### Example Workflow

```bash
# 1. Check initial compilation
lake build

# 2. Use MCP to check for errors
# (Use lean_diagnostic_messages on the file)

# 3. Start with simplest theorem
# (Add proof steps incrementally)

# 4. After each proof step
lake build  # Verify it still compiles

# 5. When stuck, use MCP tools to search for help
# (lean_leansearch, lean_loogle, lean_state_search)

# 6. Complete the proof or leave sorry for later
```

Remember: **Function correctness comes before proof correctness**. Always ensure the implementation works before proving properties about it.

## Lessons from Hoare Triple Proof Writing in FloatSpec

Based on experience writing proofs for `Zpower_Zpower_nat_spec`, `Zdiv_mod_mult_spec`, and `ZOdiv_plus_spec`, here are critical insights:

### Understanding the Hoare Triple System

1. **The wp⟦...⟧ Predicate**: The Hoare triple system uses a weakest precondition predicate. When you see error messages like `wp⟦expr⟧ ⇓ result => ...`, this indicates the proof system is expecting you to prove properties about the weakest precondition.

2. **Id Monad Handling**: Functions return `Id T` rather than plain `T`. The `Id.run` is implicit in the Hoare triple system, so avoid explicitly calling `.run` in proofs.

### Successful Proof Patterns

#### Pattern 1: Simple Conditional with Matching Postcondition
```lean
theorem simple_spec (args) :
    ⦃⌜precondition⌝⦄
    function args
    ⦃⇓result => ⌜result = expected⌝⦄ := by
  intro h
  unfold function
  simp [h]  -- When precondition directly determines the branch
  rfl       -- When result matches expected exactly
```

#### Pattern 2: Case Split on If-Then-Else
```lean
theorem conditional_spec (args) :
    ⦃⌜precondition⌝⦄
    function_with_if args
    ⦃⇓result => ⌜result = if condition then x else y⌝⦄ := by
  intro h
  unfold function_with_if
  split
  · -- True case
    rename_i h_true
    -- Prove the condition holds and simplify
    simp [h_true]
    rfl
  · -- False case  
    rename_i h_false
    -- Prove the condition fails and simplify
    simp [h_false]
    rfl
```

#### Pattern 3: Complex Boolean Conditions
When dealing with `decide` and boolean conditions in if-statements:
```lean
-- Extract boolean conditions from decide
have h_cond : actual_condition := by
  simp at h_bool_expr
  exact h_bool_expr.1  -- or .2 for second component of &&
```

### Common Pitfalls and Solutions

1. **Unsolved Goals with `simp`**: 
   - Problem: `simp [h]` doesn't always work, especially with complex conditions
   - Solution: Use `split` to case-split, then handle each branch explicitly

2. **Boolean Expression Handling**:
   - Problem: `(decide (a ≠ 0) && decide (b ≠ 0)) = true`
   - Solution: Use `simp` to convert to logical form, then extract components

3. **Negation of Conjunctions**:
   - Problem: After `push_neg`, `¬(a ≠ 0 && b ≠ 0)` becomes `a ≠ 0 → b = 0`
   - Solution: Use `by_cases` to handle the implication:
   ```lean
   by_cases ha : a = 0
   · simp [ha]; rfl
   · have hb : b = 0 := h_impl ha
     simp [hb]; rfl
   ```

4. **Or in Postconditions**:
   - Problem: Postcondition has `if a = 0 || b = 0 then ...`
   - Solution: Prove which branch applies based on preconditions, then simplify

### Proof Strategy Checklist

1. **Understand the Function**: 
   - Check the exact if-conditions
   - Note whether conditions use `&&`, `||`, or implications
   - Verify the return values match the specification

2. **Match Patterns**:
   - Simple functions without conditionals → direct `simp` and `rfl`
   - Single if-then-else → use `split` tactic
   - Nested conditions → multiple `split` or `by_cases`

3. **Debug Failed Proofs**:
   - Check error messages for the exact goal state
   - Use `#check` to verify types
   - Add intermediate `have` statements to break down complex goals
   - When `simp` fails, try manual simplification with specific lemmas

4. **Complete Each Branch**:
   - Every `split` or `by_cases` branch needs completion
   - Usually ends with `rfl` after simplification
   - Don't forget `rfl` after `simp` when goals look identical

### Build Verification Protocol

**CRITICAL**: After EVERY proof modification:
1. Save the file
2. Run `lake build` immediately
3. Check for compilation errors
4. Fix errors before proceeding to next proof
5. Never batch multiple proof changes without verification

This incremental approach prevents accumulating errors and makes debugging much easier.