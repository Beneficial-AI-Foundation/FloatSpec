# Restore exact Pff `Closestbbext`

Source commit: `f2687409821be7748f919ff6fec7816da5629c52`

## Changes

- Added exact public `Closestbbext` under the expanded upstream GenericDek
  section assumptions.
- Represented the supplied bound extension as
  `plusExp b ((bext.dExp - b.dExp + 1).toNat)` using its equal mantissa bound
  and strictly larger exponent field.
- Reused exact `Closestbbplus` to transfer closestness to the arbitrary
  extended bound without adding premises or weakening the payload.
- Updated `MISSING_INFRASTRUCTURE.md` from 59 to 58 active semantic gaps and
  made `Underf_Err1` the next target.

## Verification

- Default subscription harness attempt
  `.change_log/codex_attempt_20260721_103346`: failed before proof work because
  the configured `gpt-5.6-sol` requires a newer Codex CLI.
- Explicit `gpt-5.5` subscription attempt
  `.change_log/codex_attempt_20260721_103544`: proved the theorem and ran its
  nested focused check, audits, and full build.
- Upstream statement and section assumptions: checked against
  `/mnt2/users/kaile/hantao/flocq-upstream/src/Pff/Pff.v:16381`.
- Independent focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with
  exit code 0.
- `git diff --check`: passed.
- Placeholder audit: all 11 categories reported zero findings.
- Direct live-hole search found no `sorry`, `axiom`, or `admit` declaration.
- Status report: 58 Lean files with zero `sorry`, `axiom`, `admit`, or
  placeholder findings.
- Full `lake build`: passed all 3345 jobs.
- Normalized classifier: `proved`, build `pass`, Coq alignment `checked`,
  local target gate `pass`.
- `scripts/check_diff_trust.sh` is absent from this checkout.
