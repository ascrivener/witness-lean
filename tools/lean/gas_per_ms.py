#!/usr/bin/env python3
"""Measure what a native millisecond of the Lean check costs in gas, on this machine.

    gas_per_ms.py LEAN_HOST WITNESS_SIM CHECK DIR PLAN [SAMPLES]

`lean-host trace` and lean_split.py budget batches in native time, but what has to fit a refine
is gas, and how much gas a native millisecond is worth depends on the machine (about 29M where the
defaults were set, 77M on an M3). So check SAMPLES batches of PLAN (default 16, spread over it)
both ways: natively with `lean-host run` (the fastest of three), and in PolkaVM with witness-sim's
`check`, which charges PolkaJam's gas. Prints the highest gas per millisecond among them, an
integer: dividing a gas budget by it gives a time budget that fits on this machine. Batches that
check in under MIN_MS natively are skipped while there are others, as fixed costs dominate them.
"""

import json
import os
import re
import subprocess
import sys
import tempfile

MIN_MS = 5.0
UNITS = {"s": 1e3, "ms": 1.0, "µs": 1e-3, "us": 1e-3, "ns": 1e-6}


def millis(debug):
    """A Rust Duration's Debug form ("10.2ms", "1.5s", "950µs") in milliseconds."""
    m = re.fullmatch(r"([0-9.]+)(s|ms|µs|us|ns)", debug)
    if not m:
        raise ValueError(f"not a duration: {debug}")
    return float(m.group(1)) * UNITS[m.group(2)]


def native_ms(lean_host, args):
    best = None
    for _ in range(3):
        out = subprocess.run([lean_host, "run", args], check=True, capture_output=True, text=True).stdout
        ok, t = re.fullmatch(r"(true|false) in (\S+)\s*", out).groups()
        if ok != "true":
            raise SystemExit(f"gas_per_ms.py: the check rejected {args}")
        best = min(millis(t), best or float("inf"))
    return best


def gas(witness_sim, check, args):
    p = subprocess.run([witness_sim, "check", check, args, str(10**11)], capture_output=True, text=True)
    m = re.search(r"Ok\(\(\)\): used (\d+) gas", p.stdout + p.stderr)
    if not m:
        raise SystemExit(f"gas_per_ms.py: witness-sim check failed: {p.stdout}{p.stderr}")
    return int(m.group(1))


def main(lean_host, witness_sim, check, d, plan, samples=16):
    with open(plan) as f:
        batches = [n for n, b in enumerate(json.load(f)) if b.get("subjects")]
    picks = sorted({batches[i * len(batches) // samples] for i in range(samples)})
    rows = []
    with tempfile.TemporaryDirectory() as tmp:
        for n in picks:
            args = os.path.join(tmp, f"args-{n}")
            subprocess.run([lean_host, "args", d, plan, str(n), args], check=True, capture_output=True)
            rows.append((native_ms(lean_host, args), gas(witness_sim, check, args), n))
    timed = [r for r in rows if r[0] >= MIN_MS] or rows
    for t, g, n in timed:
        print(f"batch {n}: {g} gas in {t:.2f} ms native, {g / t / 1e6:.1f}M gas/ms", file=sys.stderr)
    print(int(max(g / t for t, g, _ in timed)))


if __name__ == "__main__":
    if len(sys.argv) not in (6, 7):
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    main(*sys.argv[1:6], *map(int, sys.argv[6:]))
