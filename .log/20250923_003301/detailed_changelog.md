# Detailed Changelog

- Commit: 404de5b
- Subject: chore: reorganize scripts under scripts/; update Core modules; remove obsolete notes
- Author: htlou <lht_pku@stu.pku.edu.cn>
- Date: 2025-09-23T00:32:43+08:00

## Overview
This commit includes script reorganization and updates to core Lean modules. Obsolete notes are removed.

## Changes
- D	FloatSpec/PROOF_NOTES.md
- D	FloatSpec/notes/Raux-LPO_min.md
- M	FloatSpec/src/Core/FIX.lean
- M	FloatSpec/src/Core/FLT.lean
- M	FloatSpec/src/Core/FLX.lean
- M	FloatSpec/src/Core/FTZ.lean
- M	FloatSpec/src/Core/Float_prop.lean
- M	FloatSpec/src/Core/Generic_fmt.lean
- M	FloatSpec/src/Core/Raux.lean
- M	FloatSpec/src/Core/Round_NE.lean
- M	FloatSpec/src/Core/Round_generic.lean
- M	FloatSpec/src/Core/Round_pred.lean
- R100	complete_import.sh	scripts/complete_import.sh
- R100	iterate.sh	scripts/iterate.sh
- R072	iterate_codex.sh	scripts/iterate_codex_2.sh
- R100	iterate_with_kill.sh	scripts/iterate_with_kill.sh

## File Stats
Lines added/removed per file:

- +Author: 	-htlou 	<lht_pku@stu.pku.edu.cn>
- +0 	-23 	FloatSpec/PROOF_NOTES.md
- +0 	-18 	FloatSpec/notes/Raux-LPO_min.md
- +3 	-3 	FloatSpec/src/Core/FIX.lean
- +3 	-3 	FloatSpec/src/Core/FLT.lean
- +3 	-3 	FloatSpec/src/Core/FLX.lean
- +3 	-3 	FloatSpec/src/Core/FTZ.lean
- +708 	-17 	FloatSpec/src/Core/Float_prop.lean
- +179 	-57 	FloatSpec/src/Core/Generic_fmt.lean
- +312 	-11 	FloatSpec/src/Core/Raux.lean
- +49 	-49 	FloatSpec/src/Core/Round_NE.lean
- +941 	-144 	FloatSpec/src/Core/Round_generic.lean
- +141 	-141 	FloatSpec/src/Core/Round_pred.lean

## Impact
- Development scripts are now consistently located under scripts/.
- Core files updated; run `lake build` to verify.
- Removed outdated notes to reduce clutter.
