#!/usr/bin/env python3
"""Check every item of a mathlib_work.py layout natively, in parallel; exit nonzero if any fails.

    check_layout.py LEAN_HOST WORK [--jobs N]

Each item's check arguments are made with `lean-host batch-args WORK N ARGS` and checked with
`lean-host run ARGS`, as witness-sim would check them in PolkaVM but natively: minutes for all of
Mathlib, and a failure found here is cheaper than one found attesting. Prints a line a failure and
one every 10,000 items.
"""
import argparse
import os
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor


def main():
    p = argparse.ArgumentParser(usage=__doc__)
    p.add_argument("lean_host"); p.add_argument("work")
    p.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) - 1))
    a = p.parse_args()
    count = 0
    while os.path.exists(f"{a.work}/batch-{count}.subjects"):
        count += 1
    tmp = tempfile.mkdtemp(dir=a.work)

    def one(n):
        args = f"{tmp}/{n}.args"
        subprocess.run([a.lean_host, "batch-args", a.work, str(n), args], check=True)
        r = subprocess.run([a.lean_host, "run", args], capture_output=True, text=True)
        os.remove(args)
        return n, r.stdout.strip(), r.stderr.strip()[-300:]

    bad, start = 0, time.time()
    with ThreadPoolExecutor(a.jobs) as pool:
        for k, (n, out, err) in enumerate(pool.map(one, range(count)), 1):
            if not out.startswith("true"):
                bad += 1
                print(f"FAIL {n}: {out} {err}", flush=True)
            if k % 10000 == 0:
                print(f"{k} of {count} checked, {bad} failed, {time.time() - start:.0f} s", flush=True)
    os.rmdir(tmp)
    print(f"checked {count} items natively: {bad} failed, {time.time() - start:.0f} s", flush=True)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
