#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: scripts/check_diff_trust.sh [--base REF] [--allow-statement-changes]

Fail if the current diff introduces proof-trust hazards:
new sorry/admit/axiom, True placeholders, placeholder comments, identity stubs,
or theorem/def/class statement changes without an allow flag.

Options:
  --base REF                    Compare against REF instead of the git index.
  --allow-statement-changes     Do not fail on changed theorem/def/class headers.
  -h,--help                     Show this help.
USAGE
}

base=""
allow_statement_changes=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --base)
      base="${2:-}"
      if [[ -z "$base" ]]; then
        echo "--base requires a ref" >&2
        exit 2
      fi
      shift 2
      ;;
    --allow-statement-changes)
      allow_statement_changes=true
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

diff_tmp="$(mktemp)"
audit_tmp="$(mktemp)"
statement_tmp="$(mktemp)"
trap 'rm -f "$diff_tmp" "$audit_tmp" "$statement_tmp"' EXIT

if [[ -n "$base" ]]; then
  git diff --unified=0 "$base" -- '*.lean' >"$diff_tmp"
else
  git diff --cached --unified=0 -- '*.lean' >"$diff_tmp"
  if [[ ! -s "$diff_tmp" ]]; then
    git diff --unified=0 -- '*.lean' >"$diff_tmp"
  fi
fi

if [[ ! -s "$diff_tmp" ]]; then
  echo "trust diff gate: no Lean diff to check"
  exit 0
fi

scripts/audit_placeholders.sh --json --diff >"$audit_tmp"

python3 - "$audit_tmp" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as f:
    data = json.load(f)

blocking = [
    finding
    for finding in data["findings"]
    if finding["kind"] in {
        "sorry",
        "axiom",
        "admit",
        "true_definition",
        "true_relation",
        "decide_true",
        "obvious_decide_true",
        "placeholder_text",
        "conclusion_as_hypothesis",
        "identity_hint",
        "public_true_theorem",
    }
]

if blocking:
    print("trust diff gate: blocking placeholder findings", file=sys.stderr)
    for finding in blocking[:80]:
        print(
            f"{finding['path']}:{finding['line']}:"
            f"{finding['kind']}: {finding['text']}",
            file=sys.stderr,
        )
    if len(blocking) > 80:
        print(f"... {len(blocking) - 80} more", file=sys.stderr)
    sys.exit(1)
PY

awk '
  /^\+/ && $0 !~ /^\+\+\+/ {
    line=substr($0, 2)
    if (line ~ /^[[:space:]]*(theorem|lemma|def|class|instance)[[:space:]]/) {
      print line
    }
  }
' "$diff_tmp" >"$statement_tmp"

if [[ -s "$statement_tmp" && "$allow_statement_changes" != true ]]; then
  echo "trust diff gate: theorem/def/class headers changed; pass --allow-statement-changes only with a Coq-alignment note" >&2
  sed 's/^/  /' "$statement_tmp" >&2
  exit 1
fi

echo "trust diff gate: pass"
