#!/usr/bin/env bash
# Aggregates metrics per-stage into metrics per-run
#   <run dir>/*_report.json + <run dir>/metadata.json -> <output>.json + <output>.metadata.json

set -euo pipefail

if [ $# -ne 2 ]; then
    echo "Usage: $0 <run dir> <output metrics file (.json)>" >&2
    exit 1
fi
run=${1%/}
out=$2
case "$out" in
    *.json) ;;
    *) echo "Output file must end with '.json': $out" >&2; exit 1 ;;
esac

# Return nothing if pattern is not matched (by default leaves the pattern as a literal string)
shopt -s nullglob
files=("$run"/*_report.json)
if [ ${#files[@]} -eq 0 ]; then
    echo "$run: no '*_report.json' files" >&2
    exit 1
fi
if [ ! -f "$run/metadata.json" ]; then
    echo "$run: no 'metadata.json'" >&2
    exit 1
fi

mkdir -p "$(dirname "$out")"

# Expect the same units across the stages
jq -s '
    ([.[].units // {} | to_entries[]] | group_by(.key) | map(select(map(.value) | unique | length > 1) | .[0].key))
        as $conflicts
    | if $conflicts != [] then error("reports disagree on the units of: \($conflicts | join(", "))") else . end
    | reduce .[] as $report ({}; . * $report)
' "${files[@]}" > "$out"

metadata=${out%.json}.metadata.json
jq . "$run/metadata.json" > "$metadata"

echo "Merged ${#files[@]} report(s) into $out, metadata in $metadata"
