#!/usr/bin/env bash
# Profile all of Mathlib under nanoda: export, streamed into the converter (no NDJSON on disk),
# then check every node once in one environment, recording each one's time.
set -euo pipefail
OUT=$1
WL=/Users/adamscrivener/Projects/Jam/witness-lean
X=/Users/adamscrivener/Projects/Jam/tools/lean4export/.lake/build/bin/lean4export
HOST=$WL/target/release/lean-host
T0=$(date +%s)
echo "== export | convert ($(date +%T))"
(cd "$WL/check/testdata/primes" && lake env "$X" Mathlib) | "$HOST" convert - "$OUT/pack" --pack
echo "converted in $(( $(date +%s) - T0 )) s; pack $(du -sh "$OUT/pack" | cut -f1)"
python3 -I - "$OUT/pack" <<'PY'
import sys
d = sys.argv[1]
with open(f"{d}/manifest.json") as f, open(f"{d}/manifest.jsonl", "w") as out:
    for line in f:
        line = line.strip().rstrip(",")
        if line and line not in "[]":
            out.write(line + "\n")
PY
echo "== profile ($(date +%T))"
T0=$(date +%s)
"$HOST" profile "$OUT/pack" "$OUT/profile"
echo "profiled in $(( $(date +%s) - T0 )) s"
echo "== done"
