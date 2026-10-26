#!/usr/bin/env bash
# Set up a fresh Ubuntu machine (22.04 or 24.04, x86_64) to attest all of Mathlib.
#
#   GITHUB_TOKEN=… bash vm-setup.sh [DIR]
#
# GITHUB_TOKEN reads ascrivener/witness and ascrivener/witness-lean, which are private (a
# fine-grained token with read access to their contents will do). It's kept in git's credential
# store on this machine, for cargo to fetch witness-lean's witness dependency too. DIR (default
# ~/jam) gets both repositories and lean4export. Then:
#
#   tmux new -d -s mathlib "LEAN4EXPORT=DIR/lean4export/.lake/build/bin/lean4export \
#       DIR/witness-lean/scripts/mathlib-full.sh ~/mathlib-run"
#
# Safe to run again.
set -euo pipefail
: "${GITHUB_TOKEN:?set GITHUB_TOKEN to a token that reads ascrivener/witness and ascrivener/witness-lean}"
DIR=$(mkdir -p "${1:-$HOME/jam}" && cd "${1:-$HOME/jam}" && pwd)
step() { printf '\n== %s\n' "$*"; }

step "packages"
sudo apt-get update -q
sudo apt-get install -yq build-essential clang lld pkg-config libssl-dev git curl tmux python3 python3-numpy

# PolkaVM's sandbox needs userfaultfd: without it, witness-sim reports every check as BadCheckBlob.
step "userfaultfd for PolkaVM"
echo 'vm.unprivileged_userfaultfd = 1' | sudo tee /etc/sysctl.d/60-polkavm.conf >/dev/null
sudo sysctl -q -p /etc/sysctl.d/60-polkavm.conf

step "Rust"
if ! command -v rustup >/dev/null; then
	curl -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal
fi
# shellcheck disable=SC1091
. "$HOME/.cargo/env"
rustup toolchain install stable --profile minimal -c rust-src
command -v cargo-jam-build >/dev/null || cargo install cargo-jam-build --version 0.1.29 --locked

step "GitHub access"
git config --global credential.helper store
printf 'https://x-access-token:%s@github.com\n' "$GITHUB_TOKEN" >"$HOME/.git-credentials"
chmod 600 "$HOME/.git-credentials"
# cargo fetches git dependencies with git, so it uses the same credentials.
mkdir -p "$HOME/.cargo"
grep -q 'git-fetch-with-cli' "$HOME/.cargo/config.toml" 2>/dev/null ||
	printf '[net]\ngit-fetch-with-cli = true\n' >>"$HOME/.cargo/config.toml"

step "repositories"
for repo in witness witness-lean; do
	[ -d "$DIR/$repo" ] || git clone -q "https://github.com/ascrivener/$repo.git" "$DIR/$repo"
	git -C "$DIR/$repo" pull -q --ff-only
done

step "Lean"
if ! command -v elan >/dev/null; then
	curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
fi
# shellcheck disable=SC1091
. "$HOME/.elan/env"
TOOLCHAIN=$(cat "$DIR/witness-lean/check/testdata/primes/lean-toolchain")
# lean4export at the commit that bumped it to this toolchain.
[ -d "$DIR/lean4export" ] || git clone -q https://github.com/leanprover/lean4export.git "$DIR/lean4export"
git -C "$DIR/lean4export" checkout -q df81913
[ "$(cat "$DIR/lean4export/lean-toolchain")" = "$TOOLCHAIN" ] || echo "warning: lean4export's toolchain isn't $TOOLCHAIN"
(cd "$DIR/lean4export" && lake build lean4export)

step "Mathlib (its build cache)"
(cd "$DIR/witness-lean/check/testdata/primes" && lake exe cache get && lake build)

step "building"
(cd "$DIR/witness-lean" && cargo build -q --release -p lean-host && cargo jam-build --out-dir out >/dev/null)
(cd "$DIR/witness" && cargo build -q --release -p witness-sim -p witness-cli)

cat <<EOF

Ready. Start the run with:

  tmux new -d -s mathlib "LEAN4EXPORT=$DIR/lean4export/.lake/build/bin/lean4export $DIR/witness-lean/scripts/mathlib-full.sh \$HOME/mathlib-run"

Watch it with: tail -f ~/mathlib-run/run.log   (or: tmux attach -t mathlib)
EOF
