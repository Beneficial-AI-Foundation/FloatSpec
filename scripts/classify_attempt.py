#!/usr/bin/env python3
"""Create a structured FloatSpec proof-attempt record.

The script intentionally treats build success, local target completion, and
trust checks as separate gates. It can be used after an agent run or for a
blocked report.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
from datetime import datetime, timezone


def run(cmd: list[str]) -> tuple[int, str]:
    proc = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return proc.returncode, proc.stdout


def git_changed_files() -> list[str]:
    code, out = run(["git", "diff", "--name-only"])
    if code != 0:
        return []
    return [line for line in out.splitlines() if line]


def count_target_sorry(target: str | None) -> int | None:
    if not target:
        return None
    path_text, _, line_text = target.partition(":")
    path = pathlib.Path(path_text)
    if not path.exists() or path.suffix != ".lean":
        return None
    text = path.read_text(encoding="utf-8", errors="replace")
    if not line_text.isdigit():
        return len(re.findall(r"\bsorry\b", text))

    target_line = int(line_text)
    starts = list(
        re.finditer(
            r"^(?:(?:private|protected|noncomputable|unsafe)\s+)*"
            r"(?:theorem|lemma|def|instance|axiom)\s+\S+",
            text,
            flags=re.MULTILINE,
        )
    )
    if not starts:
        return len(re.findall(r"\bsorry\b", text))

    line_starts = [(text.count("\n", 0, m.start()) + 1, i) for i, m in enumerate(starts)]
    chosen_index = None
    for line, index in line_starts:
        if line <= target_line:
            chosen_index = index
        else:
            break
    if chosen_index is None:
        return None

    start = starts[chosen_index].start()
    end = starts[chosen_index + 1].start() if chosen_index + 1 < len(starts) else len(text)
    return len(re.findall(r"\bsorry\b", text[start:end]))


def scan_diff_trust() -> tuple[bool, str]:
    code, out = run(["scripts/check_diff_trust.sh", "--allow-statement-changes"])
    return code == 0, out


def classify_nontriviality(changed_files: list[str]) -> str:
    proof_text = []
    for file in changed_files:
        path = pathlib.Path(file)
        if path.suffix == ".lean" and path.exists():
            proof_text.append(path.read_text(encoding="utf-8", errors="replace"))
    text = "\n".join(proof_text)
    if re.search(r"\b(induction|strongRecOn|cases|match|by_cases|constructor)\b", text):
        return "structural"
    if re.search(r"\b(round|ulp|generic_format|Valid_rnd|Monotone_exp|Zfloor|Zceil)\b", text):
        return "semantic"
    if re.search(r"\b(ring|omega|linarith|nlinarith|rw|calc|simp_all)\b", text):
        return "routine"
    if re.search(r"\b(rfl|simp|intro)\b", text):
        return "definitional"
    return "not_applicable"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--target", default=None, help="Target theorem/file, e.g. FloatSpec/src/Core/Ulp.lean:2526")
    parser.add_argument("--reason", default="unspecified")
    parser.add_argument("--result", choices=["proved", "blocked", "failed", "no_action"], default="blocked")
    parser.add_argument("--build-log", default=None)
    parser.add_argument("--build", choices=["pass", "fail", "not_run"], default="not_run")
    parser.add_argument("--blocker", default="")
    parser.add_argument("--coq-alignment", choices=["checked", "not_checked", "not_applicable"], default="not_checked")
    parser.add_argument("--model", default="not_recorded")
    parser.add_argument("--reasoning-effort", default="not_recorded")
    parser.add_argument("--provider-mode", choices=["config", "subscription", "api"], default="config")
    parser.add_argument("--api-provider-id", default=None)
    parser.add_argument("--api-base-url", default=None)
    parser.add_argument("--api-env-key", default=None)
    parser.add_argument("--api-wire-api", default=None)
    parser.add_argument("--statement-changed", action="store_true")
    parser.add_argument("--changed-files-file", default=None)
    parser.add_argument("--output", default=None)
    args = parser.parse_args()

    if args.changed_files_file:
        changed_files_path = pathlib.Path(args.changed_files_file)
        if changed_files_path.exists():
            changed_files = [
                line.strip()
                for line in changed_files_path.read_text(encoding="utf-8", errors="replace").splitlines()
                if line.strip()
            ]
        else:
            changed_files = []
    else:
        changed_files = git_changed_files()
    trust_ok, trust_output = scan_diff_trust()
    target_sorry_count = count_target_sorry(args.target)

    record = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "target": args.target,
        "reason": args.reason,
        "result": args.result,
        "build": args.build,
        "build_log": args.build_log,
        "model": args.model,
        "reasoning_effort": args.reasoning_effort,
        "provider_mode": args.provider_mode,
        "api_provider_id": args.api_provider_id,
        "api_base_url": args.api_base_url,
        "api_env_key": args.api_env_key,
        "api_wire_api": args.api_wire_api,
        "local_target_gate": "unknown" if target_sorry_count is None else ("pass" if target_sorry_count == 0 else "fail"),
        "trust_gate": "pass" if trust_ok else "fail",
        "trust_gate_output": trust_output.strip(),
        "no_new_sorry": trust_ok,
        "no_axiom_or_admit": trust_ok,
        "no_placeholder_semantics": trust_ok,
        "coq_alignment": args.coq_alignment,
        "statement_changed": args.statement_changed,
        "blocker": args.blocker,
        "changed_files": changed_files,
        "nontriviality": classify_nontriviality(changed_files),
    }

    text = json.dumps(record, indent=2, sort_keys=True) + "\n"
    if args.output:
        pathlib.Path(args.output).parent.mkdir(parents=True, exist_ok=True)
        pathlib.Path(args.output).write_text(text, encoding="utf-8")
    print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
