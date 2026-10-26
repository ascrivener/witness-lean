#!/usr/bin/env bash
# Attest all of Mathlib in witness-sim, start to finish and resumably.
#
#   scripts/mathlib-full.sh RUN_DIR
#
# Run it detached (`tmux new -d -s mathlib 'scripts/mathlib-full.sh ~/mathlib-run'`, or a
# systemd unit), and run it again after any stop: each step is skipped once its output exists, and
# attesting resumes from the simulated chain's state. Everything lives in RUN_DIR, which needs well
# over 40 GB; keep it off /tmp, which a reboot can clear. Progress goes to RUN_DIR/run.log and
# stdout.
#
# Steps:
# 1. export Mathlib (from check/testdata/primes) and convert it to a pack, streamed;
# 2. profile it (`lean-host profile`);
# 3. lay it out (tools/lean/mathlib_work.py): batches, and heavy declarations split into judgment
#    ops, each heavy op planned near the limit run in PolkaVM;
# 4. check every item natively (tools/lean/check_layout.py);
# 5. attest in witness-sim (scripts/mathlib-sim.sh), then resume with attest-batches.py.
#
# Environment:
#   WITNESS_DIR   a witness checkout (default: ../witness beside this repo)
#   LEAN4EXPORT   lean4export built for this toolchain (default: lean4export on PATH)
#   PYTHON        a python3 with numpy (default: python3)
#   JOBS          parallel jobs (default: cores less one)
#   ATTESTERS     attesters, as a1,a2,... (default: three a core)
#   NAMES         declarations whose closure alone to export (space-separated), for a smoke test
set -euo pipefail
cd "$(dirname "$0")/.."
REPO=$PWD
RUN=$(mkdir -p "${1:?usage: mathlib-full.sh RUN_DIR}" && cd "$1" && pwd)
WITNESS_DIR=$(cd "${WITNESS_DIR:-$REPO/../witness}" && pwd)
LEAN4EXPORT=${LEAN4EXPORT:-$(command -v lean4export || true)}
PYTHON=${PYTHON:-python3}
CORES=$(nproc 2>/dev/null || sysctl -n hw.ncpu)
JOBS=${JOBS:-$((CORES > 1 ? CORES - 1 : 1))}
ATTESTERS=${ATTESTERS:-$("$PYTHON" -c "print(','.join(f'a{i}' for i in range(1, 3 * $CORES + 1)))")}
PACK=$RUN/pack PROFILE=$RUN/profile WORK=$RUN/work
HOST=$REPO/target/release/lean-host
SIM=$WITNESS_DIR/target/release/witness-sim
exec > >(tee -a "$RUN/run.log") 2>&1
step() { printf '\n== %s: %s\n' "$(date '+%F %T')" "$*"; }
[ -x "$LEAN4EXPORT" ] || { echo "set LEAN4EXPORT to a lean4export binary for $(cat check/testdata/primes/lean-toolchain)"; exit 1; }
"$PYTHON" -c "import numpy" || { echo "$PYTHON needs numpy"; exit 1; }

step "building ($CORES cores, $JOBS jobs)"
cargo build -q --release -p lean-host
cargo jam-build --out-dir out >/dev/null
(cd "$WITNESS_DIR" && cargo build -q --release -p witness-sim -p witness-cli)

if [ ! -f "$PACK/pack.idx" ]; then
	step "exporting and converting Mathlib${NAMES:+ (only: $NAMES)}"
	rm -rf "$PACK"
	# shellcheck disable=SC2086 # NAMES is a list
	(cd check/testdata/primes && lake env "$LEAN4EXPORT" Mathlib ${NAMES:+-- $NAMES}) | "$HOST" convert - "$PACK" --pack
fi
if [ ! -f "$PACK/manifest.jsonl" ]; then
	"$PYTHON" -c "import json, sys; [print(json.dumps(e)) for e in json.load(open(sys.argv[1]))]" "$PACK/manifest.json" >"$PACK/manifest.jsonl.tmp"
	mv "$PACK/manifest.jsonl.tmp" "$PACK/manifest.jsonl"
	rm "$PACK/manifest.json"  # as big again, and nothing here reads it
fi
if [ ! -f "$PROFILE.order" ]; then
	step "profiling"
	"$HOST" profile "$PACK" "$PROFILE"
fi
if [ ! -f "$WORK/items" ]; then
	step "laying out"
	mkdir -p "$WORK"
	"$PYTHON" tools/lean/mathlib_work.py "$PACK" "$PROFILE" "$WORK" --jobs "$JOBS" --lean-host "$HOST" \
		--sim "$SIM" --check "$REPO/out/lean-check.jam" >"$WORK/items.tmp"
	mv "$WORK/items.tmp" "$WORK/items"
fi
step "$(cat "$WORK/items") items"
if [ ! -f "$WORK/checked" ]; then
	step "checking every item natively"
	"$PYTHON" tools/lean/check_layout.py "$HOST" "$WORK" --jobs "$JOBS"
	touch "$WORK/checked"
fi
if [ ! -d "$WORK/sim" ]; then
	step "attesting in witness-sim"
	ATTESTERS=$ATTESTERS WITNESS_DIR=$WITNESS_DIR scripts/mathlib-sim.sh "$WORK" "$WORK/sim"
else
	step "resuming the attestation in witness-sim"
	cd "$WORK"
	WITNESS_SIM_DIR=$WORK/sim "$PYTHON" "$WITNESS_DIR/scripts/attest-batches.py" "$WORK" \
		--witness "$WITNESS_DIR/target/release/witness" --service 1 --check "$WORK/lean-check.jam" \
		--check-gas 5000000000 --attesters "$ATTESTERS" --sim "$SIM"
fi
step "done: every item attested"
