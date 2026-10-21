#!/usr/bin/env bash
# Regenerate the Lean check's test fixtures from the Lean project in lean/.
#
#   LEAN4EXPORT=path/to/lean4export check/testdata/make.sh
#
# Needs elan (the toolchain in lean/lean-toolchain) and a lean4export built for it.
#
# - env-two-layer-N.bin: the statement environment of GoalTwo (2 + 2 = 4), cut into three layers.
# - env-five-layer-2.bin: GoalTwo's last layer, edited to say 2 + 2 = 5.
# - env-f.bin: the environment of GoalF, over the poster's own definition myF, in one layer.
# - delta-*.bin: solver deltas: honest proofs of GoalTwo and GoalF, and attacks (a theorem of the
#   wrong statement, a def instead of a theorem, an extra axiom, sorry, and a redefinition of myF).
set -euo pipefail
: "${LEAN4EXPORT:?set LEAN4EXPORT to the lean4export binary}"
here=$(cd "$(dirname "$0")" && pwd)
tools=$here/../../tools/lean
work=$(mktemp -d)
(
	cd "$here/lean"
	lake build >/dev/null
	lake build Fixtures.Redefine >/dev/null
	lake env "$LEAN4EXPORT" Fixtures.Statements -- GoalTwo >"$work/env-two.ndjson"
	lake env "$LEAN4EXPORT" Fixtures.Statements -- GoalF >"$work/env-f.ndjson"
	for t in goal_two goal_f goal_wrong goal_def goal_two_axiom goal_two_sorry; do
		lake env "$LEAN4EXPORT" Fixtures.Solutions -- $t >"$work/full-$t.ndjson"
	done
	lake env "$LEAN4EXPORT" Fixtures.Redefine -- goal_f >"$work/full-redefine.ndjson"
)
cd "$work"
python3 "$tools/lean_layers.py" env-two.ndjson 12000 env-two-layer >/dev/null
for t in goal_two goal_wrong goal_def goal_two_axiom goal_two_sorry; do
	python3 "$tools/lean_delta.py" env-two.ndjson full-$t.ndjson >delta-$t.ndjson
done
python3 "$tools/lean_delta.py" env-f.ndjson full-goal_f.ndjson >delta-goal_f.ndjson
python3 "$tools/lean_delta.py" env-f.ndjson full-redefine.ndjson >delta-redefine.ndjson
# GoalTwo edited to say 2 + 2 = 5, which the honest proof doesn't prove.
sed 's/"natVal":"4"}/"natVal":"5"}/' env-two-layer-2.ndjson >env-five-layer-2.ndjson
for f in env-two-layer-*.ndjson env-five-layer-2.ndjson env-f.ndjson delta-*.ndjson; do
	python3 "$tools/lean_bin.py" "$f" >"$here/${f%.ndjson}.bin"
done
echo "fixtures written to $here"
