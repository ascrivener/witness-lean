#!/usr/bin/env bash
# The fact DAG of one heavy Mathlib declaration: export its closure, check it trusting the rest of
# the closure under instrumented nanoda (call spans and cache hits), then fact_dag.py.
#   dag.sh OUTDIR NAME
set -euo pipefail
OUT=$1 NAME=$2
WL=/Users/adamscrivener/Projects/Jam/witness-lean
MEM=/Users/adamscrivener/Projects/Jam/witness-lean-mem
X=/Users/adamscrivener/Projects/Jam/tools/lean4export/.lake/build/bin/lean4export
D=$OUT/$NAME
mkdir -p "$D"
T0=$(date +%s)
(cd "$WL/check/testdata/primes" && lake env "$X" Mathlib -- "$NAME") | "$WL/target/release/lean-host" convert - "$D/nodes" | tail -1
python3 -I "$WL/tools/lean/lean_plan.py" "$D/nodes" --goal "$NAME" > "$D/goal-plan.json" 2>/dev/null
python3 -I - "$D/goal-plan.json" "$D/plan.json" <<'PY'
import json, sys
plan = json.load(open(sys.argv[1]))
goal = next(b for b in plan if "goal" in b)
lib = [h for b in plan if "subjects" in b for h in b["subjects"]]
json.dump([{"depth": 0, "subjects": [goal["goal"]], "trusted": lib}], open(sys.argv[2], "w"))
PY
"$WL/target/release/lean-host" args "$D/nodes" "$D/plan.json" 0 "$D/args-full" >/dev/null
echo "$NAME: closure and arguments in $(( $(date +%s) - T0 )) s"
: > "$D/pieces.txt"
NANODA_SPANS="$D/spans.bin" NANODA_HITS="$D/hits.bin" NANODA_PROF_MS=100000 \
	"$MEM/target-hits/release/lean-host" run "$D/args-full" > "$D/run.out" 2>&1
grep -E '^(true|false) in' "$D/run.out"
python3 -I "$MEM/tools/lean/fact_dag.py" "$D" | grep -v '^iteration' > "$D/dag.out"
cat "$D/dag.out"
