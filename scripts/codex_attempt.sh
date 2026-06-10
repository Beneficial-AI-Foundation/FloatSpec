#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: scripts/codex_attempt.sh --target TARGET [--reason REASON] [--timeout-sec N] [--model MODEL] [--reasoning-effort LEVEL] [--provider MODE] [--build] [--smoke]

Run one Codex proof/pipeline attempt with structured artifacts.

Options:
  --target TARGET   Required target, e.g. FloatSpec/src/Core/Ulp.lean:2526.
  --reason REASON   Attempt reason. Default: unspecified.
  --timeout-sec N   Codex timeout. Default: 1800.
  --model MODEL     Codex model to use, e.g. gpt-5.5. Default: config default.
  --reasoning-effort LEVEL
                   Model reasoning effort, e.g. high. Default: config default.
  --provider MODE   Codex auth/provider path: config, subscription, or api.
                   Default: config.
  --api-base-url URL
                   API base URL for --provider api. Default: https://api3.xhub.chat/v1.
  --api-env-key NAME
                   Environment variable holding the API key for --provider api.
                   Default: XHUB_API_KEY.
  --api-wire-api API
                   Codex wire API for --provider api, e.g. responses or messages.
                   Default: responses.
  --api-provider-id ID
                   Temporary Codex provider id for --provider api.
                   Default: floatspec_api.
  --build           Run lake build after Codex and record the build gate.
  --smoke           Do not allow edits; ask Codex only to run/read pipeline tools.
  -h,--help         Show this help.

Artifacts are written under .change_log/codex_attempt_<timestamp>/.
USAGE
}

target=""
reason="unspecified"
timeout_sec=1800
model=""
reasoning_effort=""
provider="config"
api_base_url="https://api3.xhub.chat/v1"
api_env_key="XHUB_API_KEY"
api_wire_api="responses"
api_provider_id="floatspec_api"
run_build=false
smoke=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --target)
      target="${2:-}"
      shift 2
      ;;
    --reason)
      reason="${2:-}"
      shift 2
      ;;
    --timeout-sec)
      timeout_sec="${2:-}"
      shift 2
      ;;
    --model)
      model="${2:-}"
      shift 2
      ;;
    --reasoning-effort)
      reasoning_effort="${2:-}"
      shift 2
      ;;
    --provider)
      provider="${2:-}"
      shift 2
      ;;
    --api-base-url)
      api_base_url="${2:-}"
      shift 2
      ;;
    --api-env-key)
      api_env_key="${2:-}"
      shift 2
      ;;
    --api-wire-api)
      api_wire_api="${2:-}"
      shift 2
      ;;
    --api-provider-id)
      api_provider_id="${2:-}"
      shift 2
      ;;
    --build)
      run_build=true
      shift
      ;;
    --smoke)
      smoke=true
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

if [[ -z "$target" ]]; then
  echo "--target is required" >&2
  usage >&2
  exit 2
fi

case "$provider" in
  config|subscription|api)
    ;;
  *)
    echo "--provider must be one of: config, subscription, api" >&2
    exit 2
    ;;
esac

if [[ "$provider" == "api" ]]; then
  if [[ -z "$api_base_url" || -z "$api_env_key" || -z "$api_wire_api" || -z "$api_provider_id" ]]; then
    echo "--provider api requires non-empty --api-base-url, --api-env-key, --api-wire-api, and --api-provider-id" >&2
    exit 2
  fi
  if [[ -z "${!api_env_key:-}" ]]; then
    echo "--provider api requires environment variable ${api_env_key} to be set" >&2
    exit 2
  fi
fi

timestamp="$(date +%Y%m%d_%H%M%S)"
attempt_dir=".change_log/codex_attempt_${timestamp}"
mkdir -p "$attempt_dir"

scripts/status_report.sh --json >"${attempt_dir}/status_before.json"
git status --porcelain=v1 --untracked-files=all | LC_ALL=C sort >"${attempt_dir}/git_status_before.txt"

prompt_file="${attempt_dir}/prompt.md"
codex_log="${attempt_dir}/codex.jsonl"
codex_stderr="${attempt_dir}/codex.stderr.log"
codex_last="${attempt_dir}/codex_last_message.md"
build_log="${attempt_dir}/build.log"
trust_log="${attempt_dir}/trust_gate.log"
attempt_json="${attempt_dir}/attempt.json"
target_path="${target%%:*}"
target_before="${attempt_dir}/target_before.lean"
target_after="${attempt_dir}/target_after.lean"
target_diff="${attempt_dir}/target_diff.patch"
deps_log="${attempt_dir}/sorry_dependency_audit.json"
provider_log="${attempt_dir}/codex_provider.txt"

if [[ -f "$target_path" ]]; then
  cp "$target_path" "$target_before"
fi

if "$smoke"; then
  cat >"$prompt_file" <<EOF
You are testing the FloatSpec Codex pipeline harness. Do not modify files.

Target: \`${target}\`
Reason: \`${reason}\`

Run or inspect these commands/files only:

- \`scripts/status_report.sh --markdown\`
- \`scripts/audit_placeholders.sh --json FloatSpec\`
- \`FloatSpec/docs/TRUST_TIERS.md\`
- \`FloatSpec/docs/PIPELINE_IMPROVEMENTS_FROM_VERINA.md\`

Report whether the tools are callable and whether the trust/status separation is visible.
EOF
else
  cat >"$prompt_file" <<EOF
You are working in the FloatSpec repository.

Target: \`${target}\`
Reason: \`${reason}\`

Follow these mandatory pipeline rules:

1. Read \`FloatSpec/docs/TRUST_TIERS.md\` and \`FloatSpec/docs/PIPELINE_IMPROVEMENTS_FROM_VERINA.md\`.
2. Repair only the target item. Do not broaden scope.
3. Compare against upstream Flocq when changing a statement or definition.
4. Do not add \`sorry\`, \`axiom\`, \`admit\`, \`:= True\`, \`fun _ _ => True\`, identity stubs, conclusion-as-hypothesis patches, or mode-erased placeholders.
5. If the target is blocked by a missing foundational theorem, stop with a blocker report instead of weakening semantics.
6. Run \`scripts/check_diff_trust.sh\` before finishing.
7. If you changed code, explain the build command used and the remaining gate status.

The final answer must say one of: proved, blocked, failed, or no_action.
EOF
fi

codex_cmd=(codex exec)
if [[ -n "$model" ]]; then
  codex_cmd+=(--model "$model")
fi
if [[ -n "$reasoning_effort" ]]; then
  codex_cmd+=(-c "model_reasoning_effort=\"$reasoning_effort\"")
fi
case "$provider" in
  config)
    ;;
  subscription)
    codex_cmd+=(-c 'model_provider="openai"')
    ;;
  api)
    codex_cmd+=(
      -c "model_provider=\"${api_provider_id}\""
      -c "model_providers.${api_provider_id}.name=\"FloatSpec API Provider\""
      -c "model_providers.${api_provider_id}.base_url=\"${api_base_url}\""
      -c "model_providers.${api_provider_id}.env_key=\"${api_env_key}\""
      -c "model_providers.${api_provider_id}.wire_api=\"${api_wire_api}\""
    )
    ;;
esac

{
  printf 'provider_mode=%s\n' "$provider"
  printf 'model=%s\n' "${model:-config_default}"
  printf 'reasoning_effort=%s\n' "${reasoning_effort:-config_default}"
  if [[ "$provider" == "api" ]]; then
    printf 'api_provider_id=%s\n' "$api_provider_id"
    printf 'api_base_url=%s\n' "$api_base_url"
    printf 'api_env_key=%s\n' "$api_env_key"
    printf 'api_env_key_set=%s\n' "yes"
    printf 'api_wire_api=%s\n' "$api_wire_api"
  elif [[ "$provider" == "subscription" ]]; then
    printf 'forced_model_provider=%s\n' "openai"
  fi
} >"$provider_log"

timeout "$timeout_sec" \
  "${codex_cmd[@]}" \
    --cd "$PWD" \
    --json \
    --output-last-message "$codex_last" \
    --dangerously-bypass-approvals-and-sandbox \
    "$(cat "$prompt_file")" >"$codex_log" 2>"$codex_stderr" || true

git status --porcelain=v1 --untracked-files=all | LC_ALL=C sort >"${attempt_dir}/git_status_after.txt"
python3 - "${attempt_dir}/git_status_before.txt" "${attempt_dir}/git_status_after.txt" "${attempt_dir}/changed_during_attempt.txt" <<'PY'
import sys

before_path, after_path, out_path = sys.argv[1:4]
before = set(open(before_path, encoding="utf-8", errors="replace").read().splitlines())
after = set(open(after_path, encoding="utf-8", errors="replace").read().splitlines())

paths = []
for line in sorted(after - before):
    if len(line) >= 4:
        paths.append(line[3:])

with open(out_path, "w", encoding="utf-8") as f:
    for path in paths:
        f.write(path + "\n")
PY

if [[ -f "$target_path" && -f "$target_before" ]]; then
  cp "$target_path" "$target_after"
  if ! diff -q "$target_before" "$target_after" >/dev/null 2>&1; then
    diff -u "$target_before" "$target_after" >"$target_diff" || true
    if ! rg -Fx "$target_path" "${attempt_dir}/changed_during_attempt.txt" >/dev/null 2>&1; then
      printf '%s\n' "$target_path" >>"${attempt_dir}/changed_during_attempt.txt"
    fi
  fi
fi

build_status="not_run"
if "$run_build"; then
  if lake build >"$build_log" 2>&1; then
    build_status="pass"
  else
    build_status="fail"
  fi
fi

if scripts/check_diff_trust.sh --allow-statement-changes >"$trust_log" 2>&1; then
  :
else
  :
fi

result="blocked"
blocker=""
if "$smoke"; then
  result="no_action"
elif [[ -f "$codex_last" ]]; then
  if rg -i "^proved\\b" "$codex_last" >/dev/null 2>&1; then
    result="proved"
  elif rg -i "^no_action\\b|^no action\\b" "$codex_last" >/dev/null 2>&1; then
    result="no_action"
  elif rg -i "^failed\\b" "$codex_last" >/dev/null 2>&1; then
    result="failed"
  fi
fi

if [[ ( "$result" == "proved" || "$result" == "no_action" ) && -f "$target_path" && -x scripts/sorry_dependency_audit.py ]]; then
  if scripts/sorry_dependency_audit.py --target "$target" --json >"$deps_log"; then
    :
  else
    result="blocked"
    blocker="target proof reaches existing sorry/admit/axiom-backed declarations; see ${deps_log}"
  fi
fi

if [[ "$result" == "blocked" && -z "$blocker" && -f "$codex_last" ]]; then
  blocker="$(
    python3 - "$codex_last" <<'PY'
import pathlib
import sys

text = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace").strip()
lines = [line.strip() for line in text.splitlines()]
if lines and lines[0].lower() == "blocked":
    lines = lines[1:]
summary = " ".join(line for line in lines if line)
print(summary[:1200])
PY
  )"
fi

classify_cmd=(scripts/classify_attempt.py
  --target "$target" \
  --reason "$reason" \
  --result "$result" \
  --build "$build_status" \
  --build-log "$build_log" \
  --blocker "$blocker" \
  --coq-alignment not_checked \
  --model "${model:-config_default}" \
  --reasoning-effort "${reasoning_effort:-config_default}" \
  --provider-mode "$provider" \
  --changed-files-file "${attempt_dir}/changed_during_attempt.txt" \
  --output "$attempt_json")
if [[ "$provider" == "api" ]]; then
  classify_cmd+=(
    --api-provider-id "$api_provider_id"
    --api-base-url "$api_base_url"
    --api-env-key "$api_env_key"
    --api-wire-api "$api_wire_api"
  )
fi
"${classify_cmd[@]}" >"${attempt_dir}/attempt.stdout.json"

scripts/status_report.sh --json >"${attempt_dir}/status_after.json"

echo "$attempt_dir"
