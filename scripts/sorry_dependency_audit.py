#!/usr/bin/env python3
"""Conservative dependency audit for proof attempts.

This is intentionally text-based. It does not try to replace Lean dependency
analysis; it catches the common FloatSpec failure mode where a local `sorry` is
removed by routing the proof through an existing `sorry`-backed bridge theorem.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys


DECL_RE = re.compile(
    r"^(?P<prefix>\s*)(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?P<kind>theorem|lemma|def|instance|axiom)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b",
    re.MULTILINE,
)


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    text = re.sub(r"--.*", "", text)
    return text


def mask_comments(text: str) -> str:
    def blank(match: re.Match[str]) -> str:
        chunk = match.group(0)
        return "".join("\n" if char == "\n" else " " for char in chunk)

    text = re.sub(r"/-.*?-/", blank, text, flags=re.DOTALL)
    text = re.sub(r"--.*", blank, text)
    return text


def lean_files(root: pathlib.Path) -> list[pathlib.Path]:
    return [
        path
        for path in root.rglob("*.lean")
        if ".lake" not in path.parts and ".change_log" not in path.parts
    ]


def split_decls(path: pathlib.Path) -> list[dict[str, object]]:
    text = path.read_text(encoding="utf-8", errors="replace")
    search_text = mask_comments(text)
    matches = list(DECL_RE.finditer(search_text))
    decls: list[dict[str, object]] = []
    for index, match in enumerate(matches):
        start = match.start()
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        body = text[start:end]
        line = text.count("\n", 0, start) + 1
        decls.append(
            {
                "name": match.group("name").split(".")[-1],
                "full_name": match.group("name"),
                "kind": match.group("kind"),
                "path": str(path),
                "line": line,
                "body": body,
                "clean_body": strip_comments(body),
                "has_placeholder": match.group("kind") == "axiom"
                or bool(re.search(r"\b(sorry|admit)\b", strip_comments(body))),
            }
        )
    return decls


def target_block(path: pathlib.Path, line: int | None) -> dict[str, object] | None:
    decls = split_decls(path)
    if line is None:
        return decls[0] if decls else None
    best = None
    for decl in decls:
        if int(decl["line"]) <= line:
            best = decl
        else:
            break
    return best


def referenced_names(text: str, known: set[str]) -> set[str]:
    clean = strip_comments(text)
    tokens = set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", clean))
    suffixes = {token.split(".")[-1] for token in tokens}
    return suffixes & known


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--target", required=True, help="Target as path or path:line")
    parser.add_argument("--root", default="FloatSpec/src")
    parser.add_argument("--max-depth", type=int, default=6)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    target_text = args.target
    path_text, _, line_text = target_text.partition(":")
    target_path = pathlib.Path(path_text)
    line = int(line_text) if line_text.isdigit() else None
    if not target_path.exists():
        print(f"target path does not exist: {target_path}", file=sys.stderr)
        return 2

    root = pathlib.Path(args.root)
    all_decls: list[dict[str, object]] = []
    for file in lean_files(root):
        all_decls.extend(split_decls(file))

    by_name: dict[str, list[dict[str, object]]] = {}
    for decl in all_decls:
        by_name.setdefault(str(decl["name"]), []).append(decl)

    block = target_block(target_path, line)
    if block is None:
        print(f"no declaration found for target: {target_text}", file=sys.stderr)
        return 2

    known = set(by_name)
    queue: list[tuple[str, dict[str, object], list[str]]] = [
        (str(block["name"]), block, [str(block["name"])])
    ]
    seen: set[tuple[str, str]] = set()
    findings: list[dict[str, object]] = []

    while queue:
        _, decl, chain = queue.pop(0)
        key = (str(decl["path"]), str(decl["name"]))
        if key in seen or len(chain) > args.max_depth + 1:
            continue
        seen.add(key)

        if bool(decl["has_placeholder"]) and len(chain) > 1:
            findings.append(
                {
                    "chain": chain,
                    "name": decl["name"],
                    "kind": decl["kind"],
                    "path": decl["path"],
                    "line": decl["line"],
                }
            )
            continue

        for name in sorted(referenced_names(str(decl["clean_body"]), known)):
            if name == decl["name"]:
                continue
            for next_decl in by_name.get(name, []):
                next_key = (str(next_decl["path"]), str(next_decl["name"]))
                if next_key not in seen:
                    queue.append((name, next_decl, chain + [name]))

    result = {
        "target": target_text,
        "declaration": {
            "name": block["name"],
            "path": block["path"],
            "line": block["line"],
        },
        "max_depth": args.max_depth,
        "placeholder_dependency_count": len(findings),
        "placeholder_dependencies": findings,
    }

    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        if findings:
            print("sorry dependency audit: found placeholder-backed dependency")
            for finding in findings[:20]:
                chain = " -> ".join(str(x) for x in finding["chain"])
                print(f"{finding['path']}:{finding['line']}: {chain}")
            if len(findings) > 20:
                print(f"... {len(findings) - 20} more")
        else:
            print("sorry dependency audit: pass")

    return 1 if findings else 0


if __name__ == "__main__":
    raise SystemExit(main())
