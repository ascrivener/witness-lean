#!/usr/bin/env bash
# A Lean proof bounty, end to end, on a local PolkaJam testnet (v0.1.29):
#
#   WITNESS_DIR=path/to/witness LEAN4EXPORT=path/to/lean4export POLKAJAM_DIR=... \
#     scripts/lean-e2e.sh [gcd|primes]
#
# - gcd (the default): gcd a b = gcd b a, over Lean core (check/testdata/lean). Fits the
#   testnet's "tiny" refine limit of 10⁹ gas.
# - primes: there are infinitely many primes, proved by Mathlib's Nat.exists_infinite_primes
#   (check/testdata/primes). Its dependency closure is 2,945 declarations, 1.5 MB in the
#   binary format, and the last layers spend about 1.5×10⁹ gas just parsing the layers before
#   them, so it needs a testnet with the full spec's 5×10⁹ refine gas (see README).
#
# The poster's statement environment is cut into layers that a library attester pins and attests,
# one after another, and the bounty cites that chain. The solver's proof delta is cut into layers
# too: the solver commits first, then attests all but the last on top of the bounty's chain, and
# reveals with them as extra layers and the last as the witness. Every attest and the reveal must
# fit one refine, parsing included; the node log (target witness) shows the gas each used.
#
# WITNESS_DIR is a checkout of witness (at the commit Cargo.toml pins), for the service and its CLI.
# Needs elan, and a lean4export built for the project's lean-toolchain. The primes project fetches
# Mathlib's build from its cache (`lake exe cache get`), which needs cache.mathlib.org. Like
# e2e.sh, starts a testnet unless JAM_RPC is set.
set -euo pipefail
: "${LEAN4EXPORT:?set LEAN4EXPORT to the lean4export binary}"
: "${WITNESS_DIR:?set WITNESS_DIR to a witness checkout}"
WITNESS_DIR=$(cd "$WITNESS_DIR" && pwd)
case "${1:-gcd}" in
	gcd)
		PROJECT=check/testdata/lean STATEMENT_MODULE=Fixtures.Statements STATEMENT=GoalGcd
		SOLUTION_MODULE=Fixtures.Solutions THEOREM=goal_gcd
		ENV_LAYER=1000000 DELTA_LAYER=220000 GAS=950000000 ;;
	primes)
		PROJECT=check/testdata/primes STATEMENT_MODULE=Primes.Statement STATEMENT=GoalPrimes
		SOLUTION_MODULE=Primes.Solution THEOREM=goal_primes
		ENV_LAYER=300000 DELTA_LAYER=160000 GAS=4500000000 ;;
	*) echo "usage: $0 [gcd|primes]" >&2; exit 2 ;;
esac
cd "$(dirname "$0")/.."
JAMT=${POLKAJAM_DIR:+$POLKAJAM_DIR/}jamt
TESTNET=${POLKAJAM_DIR:+$POLKAJAM_DIR/}polkajam-testnet
W=$WITNESS_DIR/target/debug/witness
TMP=$(mktemp -d)
LOG=$TMP/testnet.log
CHECK=out/lean-check.jam
NAMES="$STATEMENT"$'\n'"$THEOREM"

step() { printf '\n== %s\n' "$*"; }
fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }
slot() { "$JAMT" inspect slot; }
wait_slot() { while [ "$(slot)" -lt "$1" ]; do sleep 2; done; }
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
		sleep 3
	done
	fail "$what: wanted /$pattern/, got: $out"
}
item() { [ -n "$1" ] || fail "no payload"; "$JAMT" item "$SVC" "$1" >/dev/null; wait_slot $(( $(slot) + 1 )); }
# Provide preimages, then wait until refine can look them up. Big ones take a few slots to land,
# and refine reads the chain as of an anchor that trails the best block.
provide() { for f in "$@"; do "$JAMT" provide "$SVC" "$f" >/dev/null; done; wait_slot $(( $(slot) + 6 )); }
# `ls` a set of layer files in layer order.
layers() { ls "$@" | sort -t- -k2 -n; }
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
			sleep 3
		done
		echo "op $N by $who not applied after attempt $attempt"
	done
	fail "op $N by $who never applied"
}

# Pin FILES as WHO, then provide them.
pin() {
	local who=$1; shift
	for f in "$@"; do take "$who"; signed "$who" "$($W pin --service "$SVC" --owner "$who" --nonce $N --blob "$f")"; done
	expect "$who pinned $# blobs" "nonce: ${NONCE[$who]}" account --account "$who"
	provide "$@"
}

# Attest LAYERS as WHO, each on the chain of CLAIMS before it (a comma-separated list, possibly
# empty), adding each new claim to CLAIMS.
CLAIMS=
attest() {
	local who=$1; shift
	for f in "$@"; do
		local claim=${f%.bin}.claim
		take "$who"
		signed "$who" "$($W attest --service "$SVC" --attester "$who" --nonce $N --check $CHECK \
			--subject "$f" ${CLAIMS:+--chain "$CLAIMS"} --check-gas $GAS --claim-out "$claim" 2>/dev/null)"
		expect "$(basename "$f") attested" 'Attestation \{ claim' attestation --attestation "$claim"
		CLAIMS=${CLAIMS:+$CLAIMS,}$claim
	done
}

step "exporting the bounty and the proof ($STATEMENT, $THEOREM)"
(
	cd "$PROJECT"
	if grep -q mathlib lakefile.toml; then lake exe cache get >/dev/null; fi
	lake build >/dev/null
	lake env "$LEAN4EXPORT" "$STATEMENT_MODULE" -- "$STATEMENT" >"$TMP/env.ndjson"
	lake env "$LEAN4EXPORT" "$SOLUTION_MODULE" -- "$THEOREM" >"$TMP/full.ndjson"
)
python3 tools/lean/lean_delta.py "$TMP/env.ndjson" "$TMP/full.ndjson" >"$TMP/delta.ndjson"
python3 tools/lean/lean_layers.py "$TMP/env.ndjson" $ENV_LAYER "$TMP/env" >/dev/null
python3 tools/lean/lean_layers.py "$TMP/delta.ndjson" $DELTA_LAYER "$TMP/delta" >/dev/null
for f in "$TMP"/env-*.ndjson "$TMP"/delta-*.ndjson; do python3 tools/lean/lean_bin.py "$f" >"${f%.ndjson}.bin"; done
mapfile -t ENV < <(layers "$TMP"/env-*.bin)
mapfile -t DELTA < <(layers "$TMP"/delta-*.bin)
EXTRA=("${DELTA[@]:0:${#DELTA[@]}-1}")
WITNESS=${DELTA[-1]}
echo "statement environment: ${#ENV[@]} layers; proof: ${#EXTRA[@]} extra layers and a $(wc -c <"$WITNESS")-byte witness"

if [ -z "${JAM_RPC:-}" ]; then
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
for _ in $(seq 1 40); do [ "$("$JAMT" list | wc -l)" -gt "$before" ] && break; sleep 3; done
SVC=$((16#$("$JAMT" list | tail -1 | cut -f1)))
echo "service $SVC"
for _ in $(seq 1 40); do "$JAMT" inspect final service "$SVC" >/dev/null 2>&1 && break; sleep 3; done
wait_slot $(( $(slot) + 3 ))

step "a library attester attests the statement environment"
for who in alice pat bob; do item "$($W mint --to $who --amount 1000000)"; done
expect "pat has points" 'balance: 1000000' account --account pat
pin pat $CHECK "${ENV[@]}"
attest pat "${ENV[@]}"
BOUNTY_CHAIN=$CLAIMS

step "alice posts the bounty on the attested environment"
take alice
signed alice "$($W create --service "$SVC" --maker alice --nonce $N --check $CHECK --params-str "$NAMES" \
	--blobs "$(sed 's/^/claim:/; s/,/,claim:/g' <<<"$BOUNTY_CHAIN")" --reward 500 --check-gas $GAS \
	--expiry $(( $(slot) + 2000 )))"
expect "bounty 0 open" 'status: Open' bounty --bounty 0

step "bob commits, then attests his ${#EXTRA[@]} library layers on the bounty's chain"
# Committing first: attesting publishes the layers, and the earliest commitment wins.
take bob
signed bob "$($W commit --service "$SVC" --bounty 0 --hunter bob --nonce $N --salt 0x0b0b \
	--witness-file "$WITNESS" 2>/dev/null)"
expect "bob committed" "nonce: ${NONCE[bob]}" account --account bob
pin bob "${EXTRA[@]}"
attest bob "${EXTRA[@]}"
EXTRA_CLAIMS=${CLAIMS#"$BOUNTY_CHAIN"}
EXTRA_CLAIMS=${EXTRA_CLAIMS#,}

step "bob reveals the rest of the proof"
item "$($W reveal --bounty 0 --check $CHECK --params-str "$NAMES" \
	--blobs "$(sed 's/^/claim:/; s/,/,claim:/g' <<<"$BOUNTY_CHAIN")" ${EXTRA_CLAIMS:+--extra "$EXTRA_CLAIMS"} \
	--check-gas $GAS --hunter bob --salt 0x0b0b --witness-file "$WITNESS")"
expect "bob's proof opens the claim window" 'Revealing' bounty --bounty 0

printf '\nLean end-to-end checks passed (%s)\n' "${1:-gcd}"
if [ -z "${JAM_RPC:-}" ]; then
	grep -h 'check used' "$LOG" | grep -oE 'check used [0-9]+' | sort -u -t' ' -k3 -n | tail -3
fi
