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
found=("$run"/*_report.json)
if [ ${#found[@]} -eq 0 ]; then
    echo "$run: no '*_report.json' files" >&2
    exit 1
fi

# Skip the reports that aren't valid JSON
files=()
for file in "${found[@]}"; do
    if jq empty "$file" &> /dev/null; then
        files+=("$file")
    else
        echo "::warning::$file: invalid JSON, skipping it"
    fi
done
if [ ${#files[@]} -eq 0 ]; then
    echo "$run: no valid '*_report.json' files" >&2
    exit 1
fi
if [ ! -f "$run/metadata.json" ]; then
    echo "$run: no 'metadata.json'" >&2
    exit 1
fi

mkdir -p "$(dirname "$out")"

tmp=$(mktemp "$out.XXXXXX")
trap 'rm -f "$tmp"' EXIT

# Expect the same units across the stages
jq -s '
    ([.[].units // {} | to_entries[]] | group_by(.key) | map(select(map(.value) | unique | length > 1) | .[0].key))
        as $conflicts
    | if $conflicts != [] then error("reports disagree on the units of: \($conflicts | join(", "))") else . end
    | reduce .[] as $report ({}; . * $report)
' "${files[@]}" > "$tmp"

metadata=${out%.json}.metadata.json
jq . "$run/metadata.json" > "$metadata"
mv "$tmp" "$out"

echo "Merged ${#files[@]} of ${#found[@]} report(s) into $out, metadata in $metadata"
