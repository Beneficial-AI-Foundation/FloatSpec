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
