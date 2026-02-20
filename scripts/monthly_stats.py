#!/usr/bin/env python3
"""
Generate monthly commit statistics for a git repository.

Shows total lines added/removed per month, along with commit counts.
This is an optimized version that uses a single git log call.
"""

import subprocess
import sys
import re
from collections import defaultdict


def get_monthly_stats() -> dict[str, dict[str, int]]:
    """
    Get statistics for each month using a single git log command.

    Returns a dict mapping month -> {commits, additions, deletions}.
    """
    stats: dict[str, dict[str, int]] = defaultdict(
        lambda: {"commits": 0, "additions": 0, "deletions": 0}
    )

    # Use a single git log command with numstat and custom format
    # The --numstat option shows additions/deletions per file
    result = subprocess.run(
        [
            "git", "log",
            "--numstat",
            "--format=COMMIT:%ad",
            "--date=format:%Y-%m"
        ],
        capture_output=True,
        text=True,
        check=True,
    )

    current_month = None

    for line in result.stdout.split("\n"):
        line = line.strip()
        if not line:
            continue

        if line.startswith("COMMIT:"):
            current_month = line[7:]  # Extract the month (YYYY-MM)
            if current_month:
                stats[current_month]["commits"] += 1
        elif current_month:
            # Parse numstat line: additions<tab>deletions<tab>filename
            parts = line.split("\t")
            if len(parts) >= 2:
                additions, deletions = parts[0], parts[1]
                # Handle binary files (shown as -)
                if additions != "-":
                    try:
                        stats[current_month]["additions"] += int(additions)
                    except ValueError:
                        pass
                if deletions != "-":
                    try:
                        stats[current_month]["deletions"] += int(deletions)
                    except ValueError:
                        pass

    return dict(stats)


def print_stats(stats: dict[str, dict[str, int]]) -> None:
    """Print the statistics in a formatted table."""
    if not stats:
        print("No commits found.")
        return

    # Sort months chronologically
    months = sorted(stats.keys())

    # Calculate totals
    total_commits = sum(s["commits"] for s in stats.values())
    total_additions = sum(s["additions"] for s in stats.values())
    total_deletions = sum(s["deletions"] for s in stats.values())

    # Print header
    print("=" * 72)
    print("                     MONTHLY COMMIT STATISTICS")
    print("=" * 72)
    print()
    print(f"{'Month':<12} {'Commits':>10} {'Additions':>15} {'Deletions':>15} {'Net':>14}")
    print("-" * 72)

    # Print each month
    for month in months:
        s = stats[month]
        net = s["additions"] - s["deletions"]
        net_str = f"+{net:,}" if net >= 0 else f"{net:,}"
        print(
            f"{month:<12} {s['commits']:>10,} {s['additions']:>15,} {s['deletions']:>15,} {net_str:>14}"
        )

    # Print totals
    print("-" * 72)
    net_total = total_additions - total_deletions
    net_total_str = f"+{net_total:,}" if net_total >= 0 else f"{net_total:,}"
    print(
        f"{'TOTAL':<12} {total_commits:>10,} {total_additions:>15,} {total_deletions:>15,} {net_total_str:>14}"
    )
    print("=" * 72)


def export_csv(stats: dict[str, dict[str, int]], filename: str) -> None:
    """Export statistics to a CSV file."""
    months = sorted(stats.keys())
    with open(filename, "w") as f:
        f.write("month,commits,additions,deletions,net\n")
        for month in months:
            s = stats[month]
            net = s["additions"] - s["deletions"]
            f.write(f"{month},{s['commits']},{s['additions']},{s['deletions']},{net}\n")
    print(f"\nCSV exported to: {filename}")


def main() -> None:
    """Main entry point."""
    import argparse

    parser = argparse.ArgumentParser(
        description="Generate monthly commit statistics for a git repository."
    )
    parser.add_argument(
        "--csv",
        metavar="FILE",
        help="Export statistics to a CSV file",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output in JSON format",
    )
    args = parser.parse_args()

    try:
        stats = get_monthly_stats()

        if args.json:
            import json
            print(json.dumps(stats, indent=2, sort_keys=True))
        else:
            print_stats(stats)

        if args.csv:
            export_csv(stats, args.csv)

    except subprocess.CalledProcessError as e:
        print(f"Error running git command: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
