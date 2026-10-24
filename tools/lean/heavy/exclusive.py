"""The calls with the most exclusive time (their own, not their sub-calls'), from NANODA_SPANS,
named from run.out's `node` lines where logged (calls of 2 ms or more)."""
import sys
import numpy as np
d = sys.argv[1]
sp = np.fromfile(f"{d}/spans.bin", dtype="<u8").reshape(-1, 3)
n = int(sp[:, 0].max())
end = np.zeros(n + 1, dtype=np.int64); us = np.zeros(n + 1, dtype=np.int64)
end[sp[:, 0]] = sp[:, 1]; us[sp[:, 0]] = sp[:, 2]
excl = us.copy()
stack = []
for i in range(1, n + 1):
    while stack and end[stack[-1]] < i:
        stack.pop()
    if stack:
        excl[stack[-1]] -= us[i]
    stack.append(i)
names = {}
for l in open(f"{d}/run.out"):
    if l.startswith("node "):
        p = l.split()
        names[int(p[1])] = (p[3], int(p[2]))
top = np.argsort(-excl)[:12]
print(f"{n} calls; exclusive time: total {excl[1:].sum()/1e3:.0f} ms, over 1 ms in {(excl > 1000).sum()} calls")
for i in top:
    nm, dep = names.get(int(i), ("?", -1))
    print(f"  call {i}: {excl[i]/1e3:7.1f} ms exclusive of {us[i]/1e3:7.1f} ms, {nm} at depth {dep}")
