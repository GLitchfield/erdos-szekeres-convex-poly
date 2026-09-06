#!/usr/bin/env python3
"""Merge sharded outputs of decomposable_additivity_test.py into one summary."""
import json, sys
from pathlib import Path
files = [Path(f) for f in sys.argv[1:-1]]; out = Path(sys.argv[-1])
total = {"contexts": 0, "nonzero_contexts": 0, "partitions": 0, "violations": 0, "slack_histogram": {}, "seconds": 0}
violations = []; meta = None
for f in files:
    d = json.load(open(f)); meta = meta or {k: d[k] for k in ("case", "recursion", "s_max", "e_max", "levels")}
    st = d["stats"]
    for k2 in ("contexts", "nonzero_contexts", "partitions", "violations", "seconds"):
        total[k2] += st[k2]
    for k2, v in st["slack_histogram"].items():
        total["slack_histogram"][k2] = total["slack_histogram"].get(k2, 0) + v
    violations += d["violations"]
total["slack_histogram"] = dict(sorted(total["slack_histogram"].items(), key=lambda kv: int(kv[0])))
out.write_text(json.dumps({**meta, "shards": len(files), "stats": total, "violations": violations[:40]}, indent=1) + "\n")
print(json.dumps({**meta, "shards": len(files), **{k: v for k, v in total.items() if k != "slack_histogram"}}))
