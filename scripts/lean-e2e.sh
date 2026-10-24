#!/usr/bin/env bash
# A Lean proof bounty, end to end, on a local PolkaJam testnet (v0.1.29):
#
#   WITNESS_DIR=path/to/witness LEAN4EXPORT=path/to/lean4export POLKAJAM_DIR=... \
#     scripts/lean-e2e.sh [gcd|primes|flt4|fta]
#
# - gcd (the default): gcd a b = gcd b a, over Lean core (check/testdata/lean). Fits the
#   testnet's "tiny" refine limit of 10⁹ gas.
# - primes: there are infinitely many primes, proved by Mathlib's Nat.exists_infinite_primes
#   (check/testdata/primes): 2,942 nodes in 112 batches over 73 depths. The heaviest batch uses
#   about 1.25×10⁹ gas, so it needs a testnet with the full spec's 5×10⁹ refine gas (see README).
# - flt4: x⁴ + y⁴ ≠ z⁴, Mathlib's fermatLastTheoremFour, revealed as is (in the primes project):
#   7,579 nodes in 269 batches over 91 depths. Like primes, it needs the full spec's refine gas.
# - fta: the fundamental theorem of algebra, Mathlib's Complex.exists_root: 46,201 nodes in 2,416
#   batches over 293 depths. The heaviest (iteratedFDerivWithin_succ_apply_right) uses 4.1×10⁹ gas.
#
# The solver's export is converted to content-addressed nodes (tools/lean/lean_nodes.py), and
# everything but the solver's theorem is planned into batches by dependency depth
# (lean_plan.py): that's the library, attested once, batch by batch, each trusting the nodes it
# needs from earlier batches. Batches that don't depend on each other go in parallel: several
# attesters (ATTESTERS), each filling a work package of its own with several batches a round
# (witness's scripts/attest-batches.py). The poster's bounty names the theorem's
# statement node by hash, and cites one attested node so every attestation a reveal uses shares
# its pins. A theorem whose proof alone is too slow for a batch is split into smaller theorems
# where that helps (lean_split.py; the statement, and so its hash, stays). The solver commits,
# then reveals the theorem and its proof, trusting the attested nodes it needs. Every attest and
# the reveal must fit one refine; the node log (target witness) shows the gas each used. Each op
# carries the blobs it uses (the check, a batch's nodes, the trusted nodes) as extrinsics, so on a
# testnet items go through witness's scripts/jam-submit.py, and the chain holds only records.
#
# WITNESS_DIR is a checkout of witness (at the commit Cargo.toml pins), for the service and its CLI.
# Needs elan, and a lean4export built for the project's lean-toolchain. The primes project fetches
# Mathlib's build from its cache (`lake exe cache get`), which needs cache.mathlib.org. Like
# e2e.sh, starts a testnet unless JAM_RPC is set. With WITNESS_SIM=1 it runs against witness's
# tools/witness-sim instead: the same ops, rules and check (in PolkaVM, with PolkaJam's gas),
# natively, in a minute or two. No PolkaJam needed; a testnet stays the judge of what fits.
set -euo pipefail
: "${LEAN4EXPORT:?set LEAN4EXPORT to the lean4export binary}"
: "${WITNESS_DIR:?set WITNESS_DIR to a witness checkout}"
WITNESS_DIR=$(cd "$WITNESS_DIR" && pwd)
case "${1:-gcd}" in
	gcd)
		PROJECT=check/testdata/lean SOLUTION_MODULE=Fixtures.Solutions THEOREM=goal_gcd GAS=950000000 ;;
	primes)
		PROJECT=check/testdata/primes SOLUTION_MODULE=Primes.Solution THEOREM=goal_primes GAS=4500000000 ;;
	flt4)
		PROJECT=check/testdata/primes SOLUTION_MODULE=Mathlib.NumberTheory.FLT.Four
		THEOREM=fermatLastTheoremFour GAS=4500000000 ;;
	fta)
		PROJECT=check/testdata/primes SOLUTION_MODULE=Mathlib.Analysis.Complex.Polynomial.Basic
		THEOREM=Complex.exists_root GAS=4500000000 ;;
	*) echo "usage: $0 [gcd|primes|flt4|fta]" >&2; exit 2 ;;
esac
cd "$(dirname "$0")/.."
JAMT=${POLKAJAM_DIR:+$POLKAJAM_DIR/}jamt
TESTNET=${POLKAJAM_DIR:+$POLKAJAM_DIR/}polkajam-testnet
# Seconds between polls of the chain.
POLL=2
W=$WITNESS_DIR/target/release/witness
submit() { python3 "$WITNESS_DIR/scripts/jam-submit.py" "$@"; }
TMP=$(mktemp -d)
LOG=$TMP/testnet.log
# This run's own copy of the check blob, so another run rebuilding out/ can't change it midway.
CHECK=$TMP/lean-check.jam
# Where the CLI writes an op's extrinsics, and where an op waits to be submitted: an op that
# trusts many nodes, each with its Merkle path, can pass what one command-line argument may hold.
X=$TMP/extrinsics OP=$TMP/op.hex

step() { printf '\n== %s\n' "$*"; }
fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }
slot() { "$JAMT" inspect slot; }
wait_slot() { while [ "$(slot)" -lt "$1" ]; do sleep $POLL; done; }
storage() {
	local v
	# jamt cuts values over 1 KiB short; witness-sim doesn't.
	if [ "${JAM_RPC:-}" = sim ]; then
		v=$("$JAMT" inspect storage --raw "$SVC" "$($W key "$@")" 2>/dev/null || true)
	else
		v=$(python3 "$WITNESS_DIR/scripts/jam-storage.py" "$SVC" "$($W key "$@")" 2>/dev/null || true)
	fi
	case $v in 0x*) echo "$v" ;; *) echo "" ;; esac
}
show() {
	local kind=$1; shift
	local v; v=$(storage "$@")
	if [ -n "$v" ]; then $W decode "--$kind" "$v"; else echo none; fi
}
expect() {
	local what=$1 pattern=$2; shift 2
	local out=
	for _ in $(seq 1 60); do
		out=$(show "$@")
		if grep -qE "$pattern" <<<"$out"; then echo "ok: $what"; return; fi
		sleep $POLL
	done
	fail "$what: wanted /$pattern/, got: $out"
}
# Submit PAYLOAD with the extrinsics the CLI last wrote, if any.
item() {
	[ -n "$1" ] || fail "no payload"
	printf '%s' "$1" >"$OP"
	submit "$SVC" "@$OP" $(ls "$X"/* 2>/dev/null) >/dev/null
	rm -rf "$X"
	wait_slot $(( $(slot) + 1 ))
}
join() { local IFS=,; echo "$*"; }

# Account nonces, so the script can send each account's signed ops in turn.
declare -A NONCE=([alice]=0 [bob]=0)
# Set N to WHO's next nonce, and count it as used (in this shell: not in a $(...) subshell).
take() { N=${NONCE[$1]}; NONCE[$1]=$((N + 1)); }

# Send WHO's signed op PAYLOAD (made with nonce N) and wait until it's applied, which bumps WHO's
# nonce. The testnet sometimes drops a package after refine, so resubmit a couple of times; if an
# earlier copy lands late, the next is refused for its stale nonce, so it's harmless.
signed() {
	local who=$1 payload=$2
	[ -n "$payload" ] || fail "no payload"
	local extrinsics=($(ls "$X"/* 2>/dev/null))
	printf '%s' "$payload" >"$OP"
	for attempt in 1 2 3; do
		submit "$SVC" "@$OP" "${extrinsics[@]}" >/dev/null
		for _ in $(seq 1 30); do
			grep -q "nonce: ${NONCE[$who]}" <<<"$(show account --account "$who")" && { rm -rf "$X"; return; }
			sleep $POLL
		done
		echo "op $N by $who not applied after attempt $attempt"
	done
	fail "op $N by $who never applied"
}

step "exporting the proof ($THEOREM) and converting it to nodes"
(
	cd "$PROJECT"
	if grep -q mathlib lakefile.toml; then lake exe cache get >/dev/null; fi
	lake build >/dev/null
	lake env "$LEAN4EXPORT" "$SOLUTION_MODULE" -- "$THEOREM" >"$TMP/full.ndjson"
)
python3 tools/lean/lean_nodes.py "$TMP/full.ndjson" "$TMP/nodes"
# Plan; then trust only what the kernel touches, and split batches too slow for a refine
# (lean-host trace, at TRACE_MS native milliseconds a batch).
plan() {
	python3 tools/lean/lean_plan.py "$TMP/nodes" --goal "$THEOREM" >"$TMP/plan.json"
	[ -n "${GAS_PER_MS:-}" ] || calibrate
	./target/release/lean-host trace "$TMP/nodes" "$TMP/plan.json" "$TMP/plan-traced.json" "$TRACE_MS" \
		| tee "$TMP/trace.log"
	mv "$TMP/plan-traced.json" "$TMP/plan.json"
}
# A batch may use TRACE_GAS (by default about what 100 ms was where these budgets were first set),
# and a theorem split off a proof STMT_GAS to check its statement (lean_split.py --stmt-ms). Both
# are budgeted in native time, so turn them into milliseconds on this machine: gas_per_ms.py
# checks a few batches natively and in witness-sim. TRACE_MS and STMT_MS set the times directly.
# The rate also turns each batch's traced time into the gas its check is estimated to use, which
# attesting budgets packages by.
calibrate() {
	GAS_PER_MS=$(python3 tools/lean/gas_per_ms.py ./target/release/lean-host "$WITNESS_DIR/target/release/witness-sim" \
		"$CHECK" "$TMP/nodes" "$TMP/plan.json")
	TRACE_MS=${TRACE_MS:-$(( ${TRACE_GAS:-2900000000} / GAS_PER_MS ))}
	STMT_MS=${STMT_MS:-$(( (${STMT_GAS:-290000000} + GAS_PER_MS - 1) / GAS_PER_MS ))}
	echo "$(( GAS_PER_MS / 1000000 ))M gas per native ms: batches up to $TRACE_MS ms, split-off statements up to $STMT_MS ms"
}
cargo build -q --release -p lean-host
cargo jam-build --out-dir out >/dev/null
cp out/lean-check.jam "$CHECK"
(cd "$WITNESS_DIR" && cargo build -q --release -p witness-sim)
plan
# A theorem slower than that on its own: split its proof into smaller theorems where that helps
# (lean_split.py), and plan again.
mapfile -t OVER < <(sed -n 's/^over [^:]*: //p' "$TMP/trace.log")
if [ ${#OVER[@]} -gt 0 ]; then
	SPLIT=$(LEAN4EXPORT=$LEAN4EXPORT python3 tools/lean/lean_split.py "$PROJECT" "$SOLUTION_MODULE" "$TMP/nodes" "${OVER[@]}" \
		--stmt-ms "${STMT_MS:-10}")
	if [ -n "$SPLIT" ]; then
		echo "split: $SPLIT" | tr '\n' ' '; echo
		plan
	fi
fi
W_DIR=$TMP/w
BATCHES=$(python3 tools/lean/lean_batches.py "$TMP/nodes" "$TMP/plan.json" "$W_DIR" --gas-per-ms "$GAS_PER_MS")
PINS=$(cat "$W_DIR/pins")
GOAL=$(cat "$W_DIR/goal.hash")

if [ -n "${WITNESS_SIM:-}" ]; then
	step "using witness-sim (state: $TMP/sim)"
	JAMT=$WITNESS_DIR/target/release/witness-sim POLL=0 JAM_RPC=sim
	submit() { "$JAMT" item "$@"; }
	export WITNESS_SIM_DIR=$TMP/sim
	LOG=$WITNESS_SIM_DIR/log
elif [ -z "${JAM_RPC:-}" ]; then
	step "starting testnet (log: $LOG)"
	"$TESTNET" >"$LOG" 2>&1 &
	TESTNET_PID=$!
	trap 'pkill -P $TESTNET_PID 2>/dev/null; kill $TESTNET_PID 2>/dev/null || true' EXIT
	for _ in $(seq 1 60); do "$JAMT" list >/dev/null 2>&1 && break; sleep 2; done
fi

step "building and deploying"
(cd "$WITNESS_DIR" && cargo build -q --release -p witness-cli && cargo jam-build --out-dir out -p witness-service >/dev/null)
before=$("$JAMT" list | wc -l)
# The memo gas is witness_types::DEPOSIT_GAS, what a deposit into witness must carry.
"$JAMT" create-service "$WITNESS_DIR/out/witness-service.jam" 10000000000 --min-memo-gas 300000 >/dev/null
for _ in $(seq 1 40); do [ "$("$JAMT" list | wc -l)" -gt "$before" ] && break; sleep $POLL; done
SVC=$((16#$("$JAMT" list | tail -1 | cut -f1)))
echo "service $SVC"
for _ in $(seq 1 40); do "$JAMT" inspect final service "$SVC" >/dev/null 2>&1 && break; sleep $POLL; done
wait_slot $(( $(slot) + 3 ))
# The first configuration, by the test build's admin, applies at once: deposits in the faucet's
# test asset.
item "$($W propose --service "$SVC" --nonce 0 --fee-asset test --commit-deposit 10 --attest-deposit 10)"
expect "witness configured" 'fee_asset: Some' config --config

# Library attesters, each with its own nonces and core (attest-batches.py): by default as many as the
# testnet has cores. PACKAGE_GAS caps the refine gas in a package: a local testnet's validators
# share one machine, which drops packages it can't refine in time; SETTLE_SLOTS waits after each
# round lands, while they audit it.
ATTESTERS=${ATTESTERS:-pat,quinn}
step "library attesters ($ATTESTERS) attest the library: $BATCHES batches"
for who in alice bob ${ATTESTERS//,/ }; do item "$($W mint --to "$who" --amount 1000000)"; done
expect "${ATTESTERS%%,*} has the test asset" '^1000000$' balance --balance "${ATTESTERS%%,*}" --asset test
if [ "${JAM_RPC:-}" = sim ]; then CHAIN=(--sim "$JAMT"); else CHAIN=(); fi
python3 "$WITNESS_DIR/scripts/attest-batches.py" "$W_DIR" --witness "$W" --service "$SVC" --check "$CHECK" \
	--params "$PINS" --check-gas $GAS --attesters "$ATTESTERS" \
	${PACKAGE_GAS:+--package-gas "$PACKAGE_GAS"} ${SETTLE_SLOTS:+--settle "$SETTLE_SLOTS"} "${CHAIN[@]}"

step "alice posts the bounty: a proof of the statement node $GOAL"
CITE=$(cat "$W_DIR/goal.cite")
take alice
signed alice "$($W create --service "$SVC" --maker alice --nonce $N --check $CHECK --params "$GOAL$PINS" \
	--blobs "$CITE" --reward 500 --check-gas $GAS --expiry $(( $(slot) + 2000 )))"
expect "bounty 0 open" 'status: Open' bounty --bounty 0

step "bob commits, then reveals his theorem and its proof"
take bob
signed bob "$($W commit --service "$SVC" --bounty 0 --hunter bob --nonce $N --salt 0x0b0b \
	--witness-file "$W_DIR/goal.pack" 2>/dev/null)"
expect "bob committed" "nonce: ${NONCE[bob]}" account --account bob
wait_slot $(( $(slot) + 2 ))
item "$($W reveal --bounty 0 --check $CHECK --params "$GOAL$PINS" --blobs "$CITE" --trust "$(cat "$W_DIR/goal.trust")" \
	--check-gas $GAS --hunter bob --salt 0x0b0b --witness-file "$W_DIR/goal.pack" --extrinsics "$X")"
expect "bob's proof opens the claim window" 'Revealing' bounty --bounty 0

printf '\nLean end-to-end checks passed (%s)\n' "${1:-gcd}"
if [ -z "${JAM_RPC:-}" ] || [ -n "${WITNESS_SIM:-}" ]; then
	grep -h 'check used' "$LOG" | grep -oE 'check used [0-9]+' | sort -u -t' ' -k3 -n | tail -3
fi
