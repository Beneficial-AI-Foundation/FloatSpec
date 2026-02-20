#!/usr/bin/env bash
#
# Generate monthly commit statistics for a git repository.
# Shows total lines added/removed per month, along with commit counts.
#
# Usage: ./monthly_stats.sh [--csv output.csv]
#

set -e

CSV_OUTPUT=""

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --csv)
            CSV_OUTPUT="$2"
            shift 2
            ;;
        *)
            echo "Unknown option: $1" >&2
            echo "Usage: $0 [--csv output.csv]" >&2
            exit 1
            ;;
    esac
done

# Only analyze changes in the FloatSpec/ directory
TARGET_DIR="FloatSpec/"

echo "Analyzing git history for $TARGET_DIR ($(git rev-list --count HEAD -- $TARGET_DIR) commits)..." >&2

# Get stats directly using git log with shortstat, filtered by directory
git log --format='%ad' --date=format:'%Y-%m' --shortstat -- "$TARGET_DIR" | \
    awk '
    BEGIN {
        total_processed = 0
    }
    /^[0-9]{4}-[0-9]{2}$/ {
        current_month = $0
        if (!(current_month in commits)) {
            printf "Processing month: %s...\n", current_month > "/dev/stderr"
        }
        commits[current_month]++
        total_processed++
        if (total_processed % 500 == 0) {
            printf "  Processed %d commits...\n", total_processed > "/dev/stderr"
        }
        next
    }
    /file(s)? changed/ {
        insertions = 0
        deletions = 0

        for (i = 1; i <= NF; i++) {
            if ($(i+1) ~ /insertion/) {
                insertions = $i
            }
            if ($(i+1) ~ /deletion/) {
                deletions = $i
            }
        }

        additions[current_month] += insertions
        deletions_arr[current_month] += deletions
        # Calculate pure add (net change) for this commit and accumulate
        commit_net = insertions - deletions
        pure_add[current_month] += commit_net
        next
    }
    END {
        n = asorti(commits, sorted_months)

        total_commits = 0
        total_additions = 0
        total_deletions = 0
        total_pure_add = 0

        printf "========================================================================================\n"
        printf "                    MONTHLY COMMIT STATISTICS (FloatSpec/)\n"
        printf "========================================================================================\n\n"
        printf "%-12s %10s %15s %15s %14s %14s\n", "Month", "Commits", "Additions", "Deletions", "Net", "Pure Add"
        printf "----------------------------------------------------------------------------------------\n"

        for (i = 1; i <= n; i++) {
            month = sorted_months[i]
            c = commits[month]
            a = additions[month] + 0
            d = deletions_arr[month] + 0
            net = a - d
            pa = pure_add[month] + 0

            total_commits += c
            total_additions += a
            total_deletions += d
            total_pure_add += pa

            if (net >= 0) {
                net_str = "+" net
            } else {
                net_str = "" net
            }

            if (pa >= 0) {
                pa_str = "+" pa
            } else {
                pa_str = "" pa
            }

            printf "%-12s %10d %15d %15d %14s %14s\n", month, c, a, d, net_str, pa_str
        }

        printf "----------------------------------------------------------------------------------------\n"
        net_total = total_additions - total_deletions
        if (net_total >= 0) {
            net_total_str = "+" net_total
        } else {
            net_total_str = "" net_total
        }
        if (total_pure_add >= 0) {
            pa_total_str = "+" total_pure_add
        } else {
            pa_total_str = "" total_pure_add
        }
        printf "%-12s %10d %15d %15d %14s %14s\n", "TOTAL", total_commits, total_additions, total_deletions, net_total_str, pa_total_str
        printf "========================================================================================\n"
    }
    '

# Also export CSV if requested
if [[ -n "$CSV_OUTPUT" ]]; then
    echo "" >&2
    echo "Exporting to $CSV_OUTPUT..." >&2

    git log --format='%ad' --date=format:'%Y-%m' --shortstat -- "$TARGET_DIR" | \
        awk '
        /^[0-9]{4}-[0-9]{2}$/ {
            current_month = $0
            if (!(current_month in commits)) {
                printf "Processing month: %s...\n", current_month > "/dev/stderr"
            }
            commits[current_month]++
            next
        }
        /file(s)? changed/ {
            insertions = 0
            deletions = 0

            for (i = 1; i <= NF; i++) {
                if ($(i+1) ~ /insertion/) {
                    insertions = $i
                }
                if ($(i+1) ~ /deletion/) {
                    deletions = $i
                }
            }

            additions[current_month] += insertions
            deletions_arr[current_month] += deletions
            commit_net = insertions - deletions
            pure_add[current_month] += commit_net
            next
        }
        END {
            n = asorti(commits, sorted_months)
            print "month,commits,additions,deletions,net,pure_add"
            for (i = 1; i <= n; i++) {
                month = sorted_months[i]
                c = commits[month]
                a = additions[month] + 0
                d = deletions_arr[month] + 0
                net = a - d
                pa = pure_add[month] + 0
                printf "%s,%d,%d,%d,%d,%d\n", month, c, a, d, net, pa
            }
        }
        ' > "$CSV_OUTPUT"

    echo "CSV exported to: $CSV_OUTPUT" >&2
fi
