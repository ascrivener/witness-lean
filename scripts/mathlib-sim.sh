#!/usr/bin/env bash
# Attest all of Mathlib in witness-sim: the WORK directory tools/lean/mathlib_work.py lays out,
# heavy declarations' judgment ops included.
#
#   WITNESS_DIR=path/to/witness scripts/mathlib-sim.sh WORK [STATE]
#
# witness-sim runs witness's service and this repo's check in PolkaVM, with PolkaJam's gas, and
# refines a round's items in parallel (as many attesters as ATTESTERS names, default eight, each
# filling a package of its own). STATE (default WORK/sim) keeps the simulated chain. Prints a line
# a round (attest-batches.py), and the gas and bytes each item was given go to WORK/estimates.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${WITNESS_DIR:?set WITNESS_DIR to a witness checkout}"
WORK=$(cd "${1:?usage: mathlib-sim.sh WORK [STATE]}" && pwd)
export WITNESS_SIM_DIR=${2:-$WORK/sim}
mkdir -p "$WITNESS_SIM_DIR"
SIM=$WITNESS_DIR/target/release/witness-sim
W=$WITNESS_DIR/target/release/witness
CHECK=$WORK/lean-check.jam
GAS=5000000000

step() { printf '\n== %s\n' "$*"; }
item() { [ -n "$1" ] || { echo "no payload" >&2; exit 1; }; "$SIM" item "$SVC" "$1" >/dev/null; }

step "building"
cargo jam-build --out-dir out >/dev/null
cp out/lean-check.jam "$CHECK"
(cd "$WITNESS_DIR" && cargo build -q --release -p witness-sim -p witness-cli && cargo jam-build --out-dir out -p witness-service >/dev/null)

step "deploying witness (state: $WITNESS_SIM_DIR)"
# The memo gas is witness_types::DEPOSIT_GAS, what a deposit into witness must carry.
"$SIM" create-service "$WITNESS_DIR/out/witness-service.jam" 10000000000 --min-memo-gas 300000 >/dev/null
SVC=$((16#$("$SIM" list | tail -1 | cut -f1)))
echo "service $SVC"
item "$($W propose --service "$SVC" --nonce 0 --fee-asset test --commit-deposit 10 --attest-deposit 10)"

ATTESTERS=${ATTESTERS:-a1,a2,a3,a4,a5,a6,a7,a8}
for who in ${ATTESTERS//,/ }; do item "$($W mint --to "$who" --amount 100000000)"; done
BATCHES=$(ls "$WORK" | grep -c '^batch-[0-9]*\.subjects$')
step "attesters ($ATTESTERS) attest Mathlib: $BATCHES batches"
python3 "$WITNESS_DIR/scripts/attest-batches.py" "$WORK" --witness "$W" --service "$SVC" --check "$CHECK" \
	--check-gas $GAS --attesters "$ATTESTERS" --sim "$SIM"
