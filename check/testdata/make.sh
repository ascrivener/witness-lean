#!/usr/bin/env bash
# Regenerate the Lean check's test fixtures from the Lean project in lean/.
#
#   LEAN4EXPORT=path/to/lean4export check/testdata/make.sh
#
# Needs elan (the toolchain in lean/lean-toolchain) and a lean4export built for it.
#
# Each fixture NAME.pack holds every node of one theorem's closure, in dependency order (the
# theorem's statement last), then every proof (see tools/lean/lean_pack.py):
# - two: an honest proof of GoalTwo (2 + 2 = 4); f: of GoalF, over the poster's own myF.
# - wrong, def, axiom, sorry: attacks on GoalTwo (a theorem of another statement, a def instead of
#   a theorem, an extra axiom, sorry).
# - redefine: GoalF proved over the solver's own myF.
# - five: GoalTwo edited to say 2 + 2 = 5, with the honest proof of 2 + 2 = 4.
set -euo pipefail
: "${LEAN4EXPORT:?set LEAN4EXPORT to the lean4export binary}"
here=$(cd "$(dirname "$0")" && pwd)
tools=$here/../../tools/lean
work=$(mktemp -d)
(
	cd "$here/lean"
	lake build >/dev/null
	lake build Fixtures.Redefine >/dev/null
	for t in goal_two goal_f goal_wrong goal_def goal_two_axiom goal_two_sorry; do
		lake env "$LEAN4EXPORT" Fixtures.Solutions -- $t >"$work/$t.ndjson"
	done
	lake env "$LEAN4EXPORT" Fixtures.Redefine -- goal_f >"$work/redefine.ndjson"
)
cd "$work"
sed 's/"natVal":"4"}/"natVal":"5"}/' goal_two.ndjson >five.ndjson
for pair in two:goal_two f:goal_f wrong:goal_wrong def:goal_def axiom:goal_two_axiom \
	sorry:goal_two_sorry redefine:redefine five:five; do
	name=${pair%%:*} src=${pair#*:}
	python3 "$tools/lean_nodes.py" $src.ndjson nodes-$name 2>/dev/null
	python3 "$tools/lean_pack.py" nodes-$name >"$here/$name.pack"
done
echo "fixtures written to $here"
