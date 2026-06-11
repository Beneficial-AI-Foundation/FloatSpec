-- Project linters (prefer grind over omega, etc.)
import FloatSpec.Linter.OmegaLinter

-- Core floating-point functionality
import FloatSpec.src.Core

-- Calculation modules  
import FloatSpec.src.Calc

-- VCFloat-style error bound support
import FloatSpec.src.ErrorBound

-- Simproc helpers for Id/wp Hoare triples
import FloatSpec.src.SimprocWP

/-!
# FloatSpec

Core floating-point formalization in Lean 4
Transformed from the Flocq floating-point library

This library provides:
- Core floating-point functionality and generic formats
- Calculation operations (addition, multiplication, division, square root)
- VCFloat-style error-bound support

The translated `Prop`, `Pff`, and `IEEE754` layers are built by the explicit
`FloatSpecAudit` target while their Flocq alignment is checked separately from
this trusted aggregate. Import their leaf modules directly when working on
their ports.
-/

/-- Version string for the FloatSpec library -/
def FloatSpec.version : String := "0.7.0"
