#!/usr/bin/env python3
"""Run the Lean Kernel Arena's soundness regression tests through the Lean check.

    LEAN4EXPORT=path/to/lean4export arena_bugs.py ARENA PROJECT [NAME...]

ARENA is a checkout of https://github.com/leanprover/lean-kernel-arena; its tests/bugs/*.yaml
each give an export (a prebuilt `file`, or a `leanfile` to build and export) that a sound kernel
must reject. PROJECT is a Lean project whose toolchain the check is for (check/testdata/lean): a
`leanfile` is built in a copy of it (a `module` in its Arena project, on that project's
toolchain). Each export is converted to nodes (lean_nodes.py) and checked
two ways:

- by the kernel, pinning the export's own nodes for the kernel's special names (`lean-host
  nodes`), as an attacker on the check's toolchain would have them. This is the test: it passes
  if the kernel refuses a node.
- by the check itself, planned into batches and attested with its built-in pins (`lean-host
  plan`). An export from another toolchain declares `Nat` and the like by nodes the check
  doesn't pin, so it's refused for that alone.

Prints a line a test: `rejected` (by the kernel; and whether the check refused it too),
`ACCEPTED` (by the kernel: a soundness bug), `unconverted` (lean_nodes.py refused the export, so
the kernel never saw it: an attacker writes nodes directly, so this proves nothing) or `unbuilt`
(it didn't build on this toolchain). Exits nonzero if any test was accepted. NAMEs pick tests.
"""

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


def field(yaml, key):
    m = re.search(rf"^{key}:\s*(.+)$", yaml, re.M)
    return m.group(1).strip() if m else None


def export_leanfile(arena, project, leanfile, decls, out, log):
    """Build `leanfile` as module Test in a copy of `project`, and export `decls` of it."""
    with tempfile.TemporaryDirectory() as tmp:
        shutil.copy(f"{project}/lean-toolchain", tmp)
        with open(f"{tmp}/lakefile.toml", "w") as f:
            f.write('name = "test"\ndefaultTargets = ["Test"]\n\n[[lean_lib]]\nname = "Test"\n')
        shutil.copy(f"{arena}/{leanfile}", f"{tmp}/Test.lean")
        build = subprocess.run(["lake", "build"], cwd=tmp, capture_output=True, text=True)
        if build.returncode != 0:
            log.write(build.stdout + build.stderr)
            return False
        with open(out, "w") as f:
            r = subprocess.run(["lake", "env", os.environ["LEAN4EXPORT"], "Test", "--", *decls],
                               cwd=tmp, stdout=f, stderr=log)
        return r.returncode == 0


def run(arena, project, name, work):
    yaml = open(f"{arena}/tests/bugs/{name}.yaml").read()
    export, log = f"{work}/export.ndjson", open(f"{work}/log", "w")
    if field(yaml, "file"):
        shutil.copy(f"{arena}/{field(yaml, 'file')}", export)
    elif field(yaml, "leanfile"):
        decls = json.loads(field(yaml, "export-decls") or "[]")
        if not export_leanfile(arena, project, field(yaml, "leanfile"), decls, export, log):
            return "unbuilt"
    elif field(yaml, "module"):
        # A module of an Arena project (`dir`), built on that project's own toolchain and exported
        # with its own lean4export: our converter reads the format.
        project_dir, module = f"{arena}/{field(yaml, 'dir')}", field(yaml, "module")
        decls = json.loads(field(yaml, "export-decls") or "[]")
        if subprocess.run(["lake", "build", module, "lean4export"], cwd=project_dir, stdout=log, stderr=log).returncode:
            return "unbuilt"
        with open(export, "w") as f:
            if subprocess.run(["lake", "exe", "lean4export", module, "--", *decls], cwd=project_dir,
                              stdout=f, stderr=log).returncode:
                return "unbuilt"
    else:
        return "unbuilt"
    py = [sys.executable, "-I"]
    if subprocess.run([*py, f"{HERE}/lean_nodes.py", export, f"{work}/nodes"], stdout=log, stderr=log).returncode:
        return "unconverted"
    with open(f"{work}/plan.json", "w") as f:
        if subprocess.run([*py, f"{HERE}/lean_plan.py", f"{work}/nodes"], stdout=f, stderr=log).returncode:
            return "unconverted"
    host = f"{ROOT}/target/release/lean-host"
    # The kernel, on the export's own pins: a node it refuses is an error line, a panic is a
    # refusal too (as on the PVM), and only a clean run accepted everything.
    k = subprocess.run([host, "nodes", f"{work}/nodes"], capture_output=True, text=True)
    log.write(k.stdout + k.stderr)
    if k.returncode == 0 and not k.stderr.strip():
        return "ACCEPTED"
    reason = (k.stderr.strip().splitlines() or ["exit status " + str(k.returncode)])[0]
    reason = re.sub(r"^check panicked: panicked at ", "", reason)[:100]
    # The check, with its built-in pins: `lean-host plan` prints "batch N: true in ...", or false.
    c = subprocess.run([host, "plan", f"{work}/nodes", f"{work}/plan.json"], capture_output=True, text=True)
    refused = c.returncode != 0 or "false" in re.findall(r"^batch \d+: (true|false) ", c.stdout, re.M)
    return f"rejected ({reason}){'' if refused else '; the check ACCEPTED it'}"


def main(arena, project, names):
    names = names or sorted(f[:-5] for f in os.listdir(f"{arena}/tests/bugs") if f.endswith(".yaml"))
    accepted = 0
    for name in names:
        with tempfile.TemporaryDirectory() as work:
            outcome = run(arena, project, name, work)
            if not outcome.startswith("rejected"):
                detail = open(f"{work}/log").read().strip().splitlines()[-1:] or [""]
                outcome += f"  ({detail[0][:120]})"
        accepted += outcome.startswith("ACCEPTED")
        print(f"{name}: {outcome}", flush=True)
    sys.exit(1 if accepted else 0)


if __name__ == "__main__":
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    main(sys.argv[1], sys.argv[2], sys.argv[3:])
