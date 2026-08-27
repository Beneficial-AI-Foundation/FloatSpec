-- Top-level src module aggregating all FloatSpec.src submodules

-- Core floating-point functionality
import FloatSpec.src.Core

-- Calculation operations
import FloatSpec.src.Calc

-- Compatibility layer
import FloatSpec.src.Compat

-- Property analysis and error bounds
import FloatSpec.src.Prop

-- Error bound scaffolding
import FloatSpec.src.ErrorBound

-- IEEE 754 standard implementation
import FloatSpec.src.IEEE754

-- Simproc helpers
import FloatSpec.src.SimprocWP

-- Legacy Pff compatibility
import FloatSpec.src.Pff
