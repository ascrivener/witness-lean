#!/usr/bin/env bash
# Measure one kernel call of a declaration in PolkaVM, as a piece with its facts.
#   step.sh DIR CALL
set -euo pipefail
D=$1 C=$2
WL=/Users/adamscrivener/Projects/Jam/witness-lean
MEM=/Users/adamscrivener/Projects/Jam/witness-lean-mem
SIM=/Users/adamscrivener/Projects/Jam/witness-main/target/release/witness-sim
JAM=/private/tmp/claude-501/-Users-adamscrivener-Projects-Jam-witness--claude-worktrees-witness-frontrunning-large-proofs-fdbdde/8a47abbb-2b4b-4b0e-bde3-a8bf5e5545cf/scratchpad/jam/lean-check.jam
# The facts the call needs: entries it hits that were made before it.
python3 -I - "$D" "$C" > "$D/step-$C.txt" <<'PY'
import sys
import numpy as np
d, c = sys.argv[1], int(sys.argv[2])
sp = np.fromfile(f"{d}/spans.bin", dtype="<u8").reshape(-1, 3)
end = int(sp[sp[:, 0] == c][0, 1])
h = np.fromfile(f"{d}/hits.bin", dtype="<u8").reshape(-1, 2)
sel = (h[:, 0] >= c) & (h[:, 0] <= end) & (h[:, 1] < c)
print(" ".join(map(str, [c] + sorted(set(h[sel, 1].tolist())))))
PY
mkdir -p "$D/dump"
NANODA_PIECES="$D/step-$C.txt" NANODA_REPLAY=1 NANODA_DUMP="$D/dump" NANODA_PROF_MS=100000 \
	"$MEM/target-hits/release/lean-host" run "$D/args-full" 2>&1 | grep -E '^replay|^(true|false) in'
# The environment as the check would trust it: what the kernel looks up.
if [ ! -f "$D/args" ]; then
	"$WL/target/release/lean-host" trace "$D/nodes" "$D/plan.json" "$D/traced.json" 1000000 | tail -1
	"$WL/target/release/lean-host" args "$D/nodes" "$D/traced.json" 0 "$D/args" >/dev/null
fi
"$MEM/target-hits/release/lean-host" piece-args "$D/args" "$D/dump/$C.piece" "$D/step-$C.args"
echo "piece $(wc -c < "$D/dump/$C.piece") bytes, environment $(wc -c < "$D/args") bytes"
"$SIM" check "$JAM" "$D/step-$C.args" 100000000000 2>&1 | tail -1
