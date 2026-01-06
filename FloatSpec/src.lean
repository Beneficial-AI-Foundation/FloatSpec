-- Top-level src module aggregating all FloatSpec.src submodules

-- Core floating-point functionality
import FloatSpec.src.Core

-- Calculation operations
import FloatSpec.src.Calc

-- Compatibility layer
import FloatSpec.src.Compat

-- Property analysis and error bounds
-- Note: FloatSpec.src.Prop currently has all imports commented out

-- Error bound scaffolding
import FloatSpec.src.ErrorBound

-- IEEE 754 standard implementation
import FloatSpec.src.IEEE754

-- Legacy Pff compatibility
import FloatSpec.src.Pff

-- Simproc helpers
import FloatSpec.src.SimprocWP

