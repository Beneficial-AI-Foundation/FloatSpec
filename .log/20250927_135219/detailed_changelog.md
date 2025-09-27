# Detailed Changelog

- Commit: 19da3a6
- Subject: chore: update Core rounding/formatting modules; tweak lakefile; manage scripts
- Author: htlou <lht_pku@stu.pku.edu.cn>
- Date: 2025-09-27T13:52:00+08:00

## Overview
This commit updates core Lean modules and scripts as described below.

## Changes
- M	FloatSpec/src/Core/FIX.lean
- M	FloatSpec/src/Core/FLT.lean
- M	FloatSpec/src/Core/FLX.lean
- M	FloatSpec/src/Core/FTZ.lean
- M	FloatSpec/src/Core/Generic_fmt.lean
- M	FloatSpec/src/Core/Round_NE.lean
- M	FloatSpec/src/Core/Round_generic.lean
- M	FloatSpec/src/Core/Round_pred.lean
- M	FloatSpec/src/Core/Ulp.lean
- M	lakefile.lean
- A	scripts/full_prompt.md
- D	scripts/iterate_codex_2.sh
- A	scripts/iterate_new_import.sh

## Impact
- Core rounding/formatting modules updated; ensure project builds (lake build).
- Script management adjustments and cleanup.
