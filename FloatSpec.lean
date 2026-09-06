-- Project linters (prefer grind over omega, etc.)
import FloatSpec.Linter.OmegaLinter
import FloatSpec.src.Version

-- Core floating-point functionality
import FloatSpec.src.Core

-- Calculation modules  
import FloatSpec.src.Calc

-- Compatibility layer
import FloatSpec.src.Compat

-- Property analysis and error bounds
import FloatSpec.src.Prop

-- VCFloat-style error bound support
import FloatSpec.src.ErrorBound

-- IEEE 754 standard implementation
import FloatSpec.src.IEEE754
import FloatSpec.src.IEEE754.BitsSourceFacade

-- Simproc helpers for Id/wp Hoare triples
import FloatSpec.src.SimprocWP

-- Legacy Pff compatibility
import FloatSpec.src.Pff

/-!
# FloatSpec

Complete floating-point formalization in Lean 4
Transformed from the Flocq floating-point library

This library provides:
- Core floating-point functionality and generic formats
- Calculation operations (addition, multiplication, division, square root)
- Property analysis and error bounds
- VCFloat-style error-bound support
- IEEE 754 standard implementation
- Legacy Pff compatibility layer
-/

/-- Version string for the FloatSpec library -/
def FloatSpec.version : String := "0.7.0"
