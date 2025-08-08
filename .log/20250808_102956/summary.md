# Commit Summary: Replace Float with Real (ℝ)

## Overview
This commit implements a critical architectural fix by replacing Lean's built-in `Float` type with mathematical real numbers (`ℝ`) from Mathlib throughout the entire FloatSpec codebase.

## Problem Addressed
The codebase was using `Float` to formalize floating-point arithmetic, creating a circular definition where we were using floating-point numbers to define floating-point numbers themselves. This is fundamentally incorrect for formal verification.

## Solution Implemented
- Replaced all occurrences of `Float` type with `ℝ` (Real) from Mathlib
- This matches the approach used in the original Coq Flocq library which uses `R` (Coq's real number type)

## Technical Changes
1. **Dependencies**: Added Mathlib dependency to `lakefile.lean`
2. **Type Replacements**: Systematically replaced `: Float` with `: ℝ` across all files
3. **Imports**: Added `import Mathlib.Data.Real.Basic` and `open Real` to all affected files
4. **Operations**: Updated absolute value from `.abs` to `|·|` notation
5. **Computability**: Added `noncomputable` modifiers to functions involving real operations

## Files Modified
- **54 files changed** across the entire codebase:
  - All Core modules (Zaux, Raux, Defs, Float_prop, Round_pred, Generic_fmt, etc.)
  - All Calc modules (Bracket, Operations, Div, Sqrt, Round, Plus)
  - All Prop modules (7 property files)
  - All IEEE754 modules (Binary, BinarySingleNaN, Bits, PrimFloat)
  - All Pff modules (Pff, Pff2Flocq, Pff2FlocqAux)

## Impact
This change ensures the formalization correctly uses infinite-precision mathematical real numbers for defining floating-point semantics, avoiding the circular definition problem and enabling proper formal verification of floating-point arithmetic properties.

## Build Status
The project builds successfully with all changes applied.