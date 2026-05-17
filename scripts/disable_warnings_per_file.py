#!/usr/bin/env python3
"""Disable linters based on `lake build` warnings.

Usage: lake build 2>&1 | scripts/disable_warnings_per_file.py
   or: scripts/disable_warnings_per_file.py <build-log>

Parses warnings and automatically prepends `set_option linter.<name> false`
or `set_option warn.sorry false` strictly AFTER all imports in the `.lean` files.
"""
from __future__ import annotations

import re
import sys
from collections import defaultdict
from pathlib import Path

# Matches standard warning lines and captures the file path and message
WARNING_RE = re.compile(r"^warning:\s*(?P<path>[^:]+\.lean):\d+:\d+:\s*(?P<msg>.*)")

# Matches the linter suppression suggestion
LINTER_NOTE_RE = re.compile(r"^Note: This linter can be disabled with `(set_option [^`]+)`")

# Matches imports so we don't inject options above them
# Handles: "import X", "public import X", "private import X", and "prelude"
IMPORT_RE = re.compile(r"^(?:(?:public|private)\s+)?import\s+|^prelude\b")


def parse_log(lines: list[str]) -> dict[str, set[str]]:
    """Return a mapping of file paths to a set of `set_option` commands."""
    by_file = defaultdict(set)
    current_file = None

    for line in lines:
        # Check if this line is a new warning header
        m_warn = WARNING_RE.match(line)
        if m_warn:
            current_file = m_warn.group("path")
            msg = m_warn.group("msg")

            # Hardcoded handling for the `sorry` warning
            if "declaration uses `sorry`" in msg:
                by_file[current_file].add("set_option warn.sorry false")
            continue

        # Check if the line suggests a linter disable option
        m_note = LINTER_NOTE_RE.match(line)
        if m_note and current_file:
            by_file[current_file].add(m_note.group(1))

    return by_file


def insert_options(content: str, needed: set[str]) -> tuple[str, bool]:
    """Insert `set_option` commands strictly after the last import."""
    if not needed:
        return content, False

    lines = content.splitlines(keepends=True)

    # 1. Find the index of the last import statement
    last_import_idx = -1
    for i, line in enumerate(lines):
        if IMPORT_RE.match(line.strip()):
            last_import_idx = i

    # 2. Determine where to insert
    insert_idx = last_import_idx + 1 if last_import_idx != -1 else 0

    # 3. Advance past any blank lines immediately after the imports for neatness
    while insert_idx < len(lines) and lines[insert_idx].strip() == "":
        insert_idx += 1

    # Format the block of options
    opts_str = "\n".join(sorted(needed)) + "\n"

    # Insert into lines
    if insert_idx == 0:
        lines.insert(0, opts_str + "\n")
    else:
        # If we are inserting lower down, keep the spacing clean
        lines.insert(insert_idx, opts_str + "\n")

    return "".join(lines), True


def main() -> int:
    if len(sys.argv) > 1:
        with open(sys.argv[1], encoding="utf-8") as f:
            lines = f.read().splitlines()
    else:
        lines = sys.stdin.read().splitlines()

    by_file = parse_log(lines)
    print(f"Found suppressions for {len(by_file)} files.", file=sys.stderr)

    total_fixed = 0
    for path, opts in by_file.items():
        p = Path(path)
        if not p.exists():
            print(f"  skip (missing): {path}", file=sys.stderr)
            continue

        content = p.read_text(encoding="utf-8")

        # Filter out options that are already present in the file
        needed = {o for o in opts if o not in content}
        if not needed:
            continue

        new_content, changed = insert_options(content, needed)
        if changed:
            p.write_text(new_content, encoding="utf-8")
            print(f"  {path}: added {len(needed)} suppression(s)")
            total_fixed += 1

    print(f"\nTotal files updated: {total_fixed}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
