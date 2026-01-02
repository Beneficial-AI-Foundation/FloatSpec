-- Project linters (prefer grind over omega, etc.)
import FloatSpec.Linter.OmegaLinter

-- Core floating-point functionality
import FloatSpec.src.Core

-- Calculation modules  
import FloatSpec.src.Calc

-- Property analysis and error bounds
import FloatSpec.src.Prop
-- VCFloat-style error bound scaffolding
import FloatSpec.src.ErrorBound

-- IEEE 754 standard implementation
import FloatSpec.src.IEEE754
-- Simproc helpers for bit-level computations
import FloatSpec.src.IEEE754.SimprocBits
-- Simproc helpers for BinarySingleNaN classifiers
import FloatSpec.src.IEEE754.SimprocBSN
-- Simproc helpers for FullFloat/StandardFloat classifiers and ops
import FloatSpec.src.IEEE754.SimprocBinary

-- Simproc helpers for Id/wp Hoare triples
import FloatSpec.src.SimprocWP

-- Legacy Pff compatibility
import FloatSpec.src.Pff

/-!
# FloatSpec

Complete IEEE 754 floating-point formalization in Lean 4
Transformed from the Flocq floating-point library

This library provides:
- Core floating-point functionality and generic formats
- Calculation operations (addition, multiplication, division, square root)
- Property analysis and error bounds 
- Full IEEE 754 standard implementation
- Legacy Pff compatibility layer
-/

/-- Version string for the FloatSpec library -/
def FloatSpec.version : String := "0.7.0"
