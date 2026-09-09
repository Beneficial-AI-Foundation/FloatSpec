#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: scripts/audit_placeholders.sh [--json] [--diff] [--fail-on-findings] [PATH...]

Scan Lean sources for placeholder hazards: sorry/admit/axiom, True
placeholders, placeholder comments, identity/constant stubs, and common
semantic-weakening markers.

Options:
  --json    Emit JSON instead of text.
  --diff    Scan only added lines in the current git diff.
  --fail-on-findings  Exit nonzero when any finding is reported.
  -h,--help Show this help.

If no PATH is supplied, FloatSpec/ is scanned.
USAGE
}

json=false
diff_only=false
fail_on_findings=false
paths=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --json)
      json=true
      shift
      ;;
    --diff)
      diff_only=true
      shift
      ;;
    --fail-on-findings)
      fail_on_findings=true
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      paths+=("$1")
      shift
      ;;
  esac
done

if [[ ${#paths[@]} -eq 0 ]]; then
  paths=(FloatSpec)
fi

pattern_file="$(mktemp)"
scan_file="$(mktemp)"
trap 'rm -f "$pattern_file" "$scan_file"' EXIT

cat >"$pattern_file" <<'PATTERNS'
sorry	^\s*sorry\b|\bsorry\b
axiom	^\s*(private\s+)?axiom\b
admit	^\s*admit\b|\badmit\b
true_definition	:\s*Prop\s*:=\s*True\b|:\s*True\s*:=\s*True\.intro\b
true_relation	fun\s+(_|[A-Za-z][A-Za-z0-9_']*)\s+(_|[A-Za-z][A-Za-z0-9_']*)\s*=>\s*True\b
decide_true	decide\s*(\(\s*)?True(\s*\))?
obvious_decide_true	decide\s*\(\s*\(?\s*0\s*:\s*ℝ\s*\)?\s*≤\s*0\s*\)
placeholder_text	placeholder|stub|fake|dummy|temporar|TODO|FIXME|mode is ignored|mode.*ignored|always returns|constant.*placeholder
conclusion_as_hypothesis	conclusion.*hypothesis|postcondition.*precondition|assum.*conclusion
identity_hint	identity/no-op|no-op placeholder|returns the input|return the input
public_true_theorem	theorem\s+[A-Za-z0-9_'.]+\b.*:\s*True\b
PATTERNS

if "$diff_only"; then
  git diff --unified=0 -- "${paths[@]}" |
    awk '
      /^diff --git / {
        file=$4
        sub(/^b\//, "", file)
      }
      /^\+\+\+ b\// {
        file=$2
        sub(/^b\//, "", file)
      }
      /^@@ / {
        if (match($0, /\+([0-9]+)/, m)) line=m[1]; else line=0
        next
      }
      /^\+/ && $0 !~ /^\+\+\+/ {
        text=substr($0, 2)
        if (file ~ /\.lean$/) {
          printf "%s:%d:%s\n", file, line, text
        }
        line++
        next
      }
    ' >"$scan_file"
else
  rg -n -H --glob '*.lean' '.*' "${paths[@]}" >"$scan_file" || true
fi

# The Hoare-style linter contains syntax patterns that intentionally match
# trivial postconditions. These lines are tooling logic, not theorem/spec
# payloads, and are already documented as non-payload scanner noise.
filtered_scan_file="$(mktemp)"
awk -F: '
  $1 == "FloatSpec/Linter/HoareStyleLinter.lean" &&
    index($3, "`(term|") && index($3, "=> True) => true") { next }
  # Commented-out examples can mention relation-erased rounding attempts with
  # `fun _ _ => True`. They are not active declarations or spec payloads.
  $0 ~ /^[^:]+:[0-9]+:[[:space:]]*--/ && index($0, "fun _ _ => True") { next }
  { print }
' "$scan_file" >"$filtered_scan_file"
mv "$filtered_scan_file" "$scan_file"

# Scan Lean syntax, not prose in line or nested block comments.  Keeping the
# original path and line number makes findings stable while preventing words
# such as "temporarily" or "admit" in audit explanations from becoming trust
# failures.  String contents are retained because placeholder code can occur in
# generated declarations, but comment delimiters inside strings are ignored.
code_scan_file="$(mktemp)"
python3 - "$scan_file" "$code_scan_file" <<'PY'
import sys

source, destination = sys.argv[1:3]
block_depth = 0

with open(source, encoding="utf-8", errors="replace") as src, \
     open(destination, "w", encoding="utf-8") as dst:
    for raw in src:
        raw = raw.rstrip("\n")
        parts = raw.split(":", 2)
        if len(parts) != 3:
            continue
        path, line, text = parts
        out = []
        i = 0
        in_string = False
        escaped = False
        while i < len(text):
            if block_depth:
                if text.startswith("/-", i):
                    block_depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    block_depth -= 1
                    i += 2
                else:
                    i += 1
                continue
            ch = text[i]
            if in_string:
                out.append(ch)
                if escaped:
                    escaped = False
                elif ch == "\\":
                    escaped = True
                elif ch == '"':
                    in_string = False
                i += 1
                continue
            if ch == '"':
                in_string = True
                out.append(ch)
                i += 1
            elif text.startswith("--", i):
                break
            elif text.startswith("/-", i):
                block_depth = 1
                i += 2
            else:
                out.append(ch)
                i += 1
        dst.write(f"{path}:{line}:{''.join(out)}\n")
PY
mv "$code_scan_file" "$scan_file"

if "$json"; then
  python3 - "$pattern_file" "$scan_file" "$fail_on_findings" <<'PY'
import json
import re
import sys

patterns = []
with open(sys.argv[1], encoding="utf-8") as f:
    for raw in f:
        raw = raw.rstrip("\n")
        if not raw:
            continue
        name, pattern = raw.split("\t", 1)
        flags = re.IGNORECASE if name in {"placeholder_text", "identity_hint", "conclusion_as_hypothesis"} else 0
        patterns.append((name, re.compile(pattern, flags)))

findings = []
counts = {name: 0 for name, _ in patterns}

with open(sys.argv[2], encoding="utf-8", errors="replace") as f:
    for raw in f:
        raw = raw.rstrip("\n")
        parts = raw.split(":", 2)
        if len(parts) != 3:
            continue
        path, line_s, text = parts
        try:
            line = int(line_s)
        except ValueError:
            line = None
        for name, regex in patterns:
            if regex.search(text):
                counts[name] += 1
                findings.append({
                    "kind": name,
                    "path": path,
                    "line": line,
                    "text": text.strip(),
                })

print(json.dumps({"counts": counts, "findings": findings}, indent=2, sort_keys=True))
if sys.argv[3] == "true" and findings:
    raise SystemExit(1)
PY
else
  any=false
  while IFS=$'\t' read -r name pattern; do
    if [[ "$name" == "placeholder_text" || "$name" == "identity_hint" || "$name" == "conclusion_as_hypothesis" ]]; then
      matches="$(rg -n -i "$pattern" "$scan_file" || true)"
    else
      matches="$(rg -n "$pattern" "$scan_file" || true)"
    fi
    count="$(printf '%s\n' "$matches" | sed '/^$/d' | wc -l | tr -d ' ')"
    printf '%s: %s\n' "$name" "$count"
    if [[ "$count" != "0" ]]; then
      any=true
      printf '%s\n' "$matches" | sed 's/^/  /'
    fi
  done <"$pattern_file"
  if ! "$any"; then
    echo "No placeholder-pattern findings."
  fi
  if "$fail_on_findings" && "$any"; then
    exit 1
  fi
fi
