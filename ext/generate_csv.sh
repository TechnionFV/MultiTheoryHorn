#!/bin/bash
set -euo pipefail

# Usage: ./merge.sh <header.csv>

if [[ $# -ne 1 ]]; then
    echo "Usage: $0 <header.csv>" >&2
    exit 1
fi

header_file="$1"

if [[ ! -f "$header_file" ]]; then
    echo "Error: header file '$header_file' not found" >&2
    exit 1
fi

dir="$(dirname "$header_file")"
output_file="$dir/results.csv"

# Write header to output file
head -n 1 "$header_file" > "$output_file"

# Append all .stats files in the same folder
for f in "$dir"/*.stats; do
    [[ -e "$f" ]] || continue
    sed -n '1p' "$f" >> "$output_file"
done

echo "Merged $(ls "$dir"/*.stats | wc -l) .stats files into $output_file"
