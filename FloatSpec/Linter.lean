import FloatSpec.Linter.OmegaLinter
import FloatSpec.Linter.SimpOnlyLinter
import FloatSpec.Linter.IdReturnLinter
import FloatSpec.Linter.HoareStyleLinter

/-! # FloatSpec Linters

Project-specific linters for FloatSpec development.

**Available Linters:**
- {lit}`linter.preferGrind`: Warns when {lit}`omega` is used, suggests {lit}`grind` instead.
- {lit}`linter.preferSimp`: Warns when {lit}`simp only` is used, suggests {lit}`simp` instead.
- {lit}`linter.noIdReturn`: Warns when {lit}`def`/{lit}`abbrev` returns {lean}`Id`.
- {lit}`linter.hoareStyle`: Warns on non-True Hoare preconditions and trivial postconditions.

**Disabling:** Use {lit}`set_option linter.preferGrind false` or similar.
-/
