#!/usr/bin/env bash
# A Lean proof bounty, end to end, on a local PolkaJam testnet (v0.1.29):
#
#   WITNESS_DIR=path/to/witness LEAN4EXPORT=path/to/lean4export POLKAJAM_DIR=... \
#     scripts/lean-e2e.sh [gcd|primes|flt4]
#
# - gcd (the default): gcd a b = gcd b a, over Lean core (check/testdata/lean). Fits the
#   testnet's "tiny" refine limit of 10⁹ gas.
# - primes: there are infinitely many primes, proved by Mathlib's Nat.exists_infinite_primes
#   (check/testdata/primes): 2,942 nodes in 112 batches over 73 depths. The heaviest batch uses
#   about 1.25×10⁹ gas, so it needs a testnet with the full spec's 5×10⁹ refine gas (see README).
# - flt4: x⁴ + y⁴ ≠ z⁴, Mathlib's fermatLastTheoremFour, revealed as is (in the primes project):
#   7,579 nodes in 269 batches over 91 depths. Like primes, it needs the full spec's refine gas.
#
# The solver's export is converted to content-addressed nodes (tools/lean/lean_nodes.py), and
# everything but the solver's theorem is planned into batches by dependency depth
# (lean_plan.py): that's the library, which an attester attests once, batch by batch, each
# trusting the nodes it needs from earlier batches. The poster's bounty names the theorem's
# statement node by hash, and cites one attested node so every attestation a reveal uses shares
# its pins. The solver commits, then reveals the theorem and its proof, trusting the attested
# nodes it needs. Every attest and the reveal must fit one refine; the node log (target witness)
# shows the gas each used.
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
	*) echo "usage: $0 [gcd|primes|flt4]" >&2; exit 2 ;;
esac
cd "$(dirname "$0")/.."
JAMT=${POLKAJAM_DIR:+$POLKAJAM_DIR/}jamt
TESTNET=${POLKAJAM_DIR:+$POLKAJAM_DIR/}polkajam-testnet
# Seconds between polls of the chain.
POLL=2
W=$WITNESS_DIR/target/debug/witness
TMP=$(mktemp -d)
LOG=$TMP/testnet.log
CHECK=out/lean-check.jam

step() { printf '\n== %s\n' "$*"; }
fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }
slot() { "$JAMT" inspect slot; }
wait_slot() { while [ "$(slot)" -lt "$1" ]; do sleep $POLL; done; }
storage() {
	local v
	v=$("$JAMT" inspect storage --raw "$SVC" "$($W key "$@")" 2>/dev/null || true)
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
item() { [ -n "$1" ] || fail "no payload"; "$JAMT" item "$SVC" "$1" >/dev/null; wait_slot $(( $(slot) + 1 )); }
# Provide preimages, then wait until refine can look them up. Big ones take a few slots to land,
# and refine reads the chain as of an anchor that trails the best block.
provide() { for f in "$@"; do "$JAMT" provide "$SVC" "$f" >/dev/null; done; wait_slot $(( $(slot) + 6 )); }
join() { local IFS=,; echo "$*"; }

# Account nonces, so the script can send each account's signed ops in turn.
declare -A NONCE=([alice]=0 [pat]=0 [bob]=0)
# Set N to WHO's next nonce, and count it as used (in this shell: not in a $(...) subshell).
take() { N=${NONCE[$1]}; NONCE[$1]=$((N + 1)); }

# Send WHO's signed op PAYLOAD (made with nonce N) and wait until it's applied, which bumps WHO's
# nonce. The testnet sometimes drops a package after refine, so resubmit a couple of times; if an
# earlier copy lands late, the next is refused for its stale nonce, so it's harmless.
signed() {
	local who=$1 payload=$2
	[ -n "$payload" ] || fail "no payload"
	for attempt in 1 2 3; do
		"$JAMT" item "$SVC" "$payload" >/dev/null
		for _ in $(seq 1 30); do
			grep -q "nonce: ${NONCE[$who]}" <<<"$(show account --account "$who")" && return
			sleep $POLL
		done
		echo "op $N by $who not applied after attempt $attempt"
	done
	fail "op $N by $who never applied"
}

# Pin FILES as WHO, MAX_PINS (64) at a time, then provide them.
pin() {
	local who=$1; shift
	local files=("$@")
	for ((i = 0; i < ${#files[@]}; i += 64)); do
		take "$who"
		signed "$who" "$($W pin --service "$SVC" --owner "$who" --nonce $N --blobs "$(join "${files[@]:i:64}")")"
	done
	expect "$who pinned ${#files[@]} blobs" "nonce: ${NONCE[$who]}" account --account "$who"
	provide "$@"
}

step "exporting the proof ($THEOREM) and converting it to nodes"
(
	cd "$PROJECT"
	if grep -q mathlib lakefile.toml; then lake exe cache get >/dev/null; fi
	lake build >/dev/null
	lake env "$LEAN4EXPORT" "$SOLUTION_MODULE" -- "$THEOREM" >"$TMP/full.ndjson"
)
python3 tools/lean/lean_nodes.py "$TMP/full.ndjson" "$TMP/nodes"
python3 tools/lean/lean_plan.py "$TMP/nodes" --goal "$THEOREM" >"$TMP/plan.json"
W_DIR=$TMP/w
BATCHES=$(python3 tools/lean/lean_batches.py "$TMP/nodes" "$TMP/plan.json" "$W_DIR")
PINS=$(cat "$W_DIR/pins")
GOAL=$(cat "$W_DIR/goal.hash")
for ((n = 0; n < BATCHES; n++)); do
	"$W" bundle --subjects "$(cat "$W_DIR/batch-$n.subjects")" --out "$W_DIR/batch-$n.bundle" >/dev/null
done

if [ -n "${WITNESS_SIM:-}" ]; then
	step "using witness-sim (state: $TMP/sim)"
	(cd "$WITNESS_DIR" && cargo build -q --release -p witness-sim)
	JAMT=$WITNESS_DIR/target/release/witness-sim POLL=0 JAM_RPC=sim
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
(cd "$WITNESS_DIR" && cargo build -q -p witness-cli && cargo jam-build --out-dir out -p witness-service >/dev/null)
cargo jam-build --out-dir out >/dev/null
before=$("$JAMT" list | wc -l)
"$JAMT" create-service "$WITNESS_DIR/out/witness-service.jam" 10000000000 >/dev/null
for _ in $(seq 1 40); do [ "$("$JAMT" list | wc -l)" -gt "$before" ] && break; sleep $POLL; done
SVC=$((16#$("$JAMT" list | tail -1 | cut -f1)))
echo "service $SVC"
for _ in $(seq 1 40); do "$JAMT" inspect final service "$SVC" >/dev/null 2>&1 && break; sleep $POLL; done
wait_slot $(( $(slot) + 3 ))

step "a library attester attests the library: $BATCHES batches"
for who in alice pat bob; do item "$($W mint --to $who --amount 1000000)"; done
expect "pat has points" 'balance: 1000000' account --account pat
BUNDLES=()
for ((n = 0; n < BATCHES; n++)); do BUNDLES+=("$W_DIR/batch-$n.bundle"); done
pin pat $CHECK "${BUNDLES[@]}"
for ((n = 0; n < BATCHES; n++)); do
	take pat
	trust=$(cat "$W_DIR/batch-$n.trust")
	signed pat "$($W attest --service "$SVC" --attester pat --nonce $N --check $CHECK --params "$PINS" \
		--subjects "$W_DIR/batch-$n.bundle" ${trust:+--trust "$trust"} --witness-file "$W_DIR/batch-$n.proofs" \
		--check-gas $GAS --claim-out "$W_DIR/batch-$n.claim" 2>/dev/null)"
	expect "batch $n attested" 'Attestation \{ claim' attestation --attestation "$W_DIR/batch-$n.claim"
done

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
	--check-gas $GAS --hunter bob --salt 0x0b0b --witness-file "$W_DIR/goal.pack")"
expect "bob's proof opens the claim window" 'Revealing' bounty --bounty 0

printf '\nLean end-to-end checks passed (%s)\n' "${1:-gcd}"
if [ -z "${JAM_RPC:-}" ] || [ -n "${WITNESS_SIM:-}" ]; then
	grep -h 'check used' "$LOG" | grep -oE 'check used [0-9]+' | sort -u -t' ' -k3 -n | tail -3
fi
