#!/usr/bin/env python3
"""Prints MODULE:EST_GB for the shard and representative modules of L6CheckK/F1 (run from the package root), the
heaviest first. The estimate of the peak memory of a module is that of its heaviest declaration: 2 GB plus 16 MB per
unit of cost (a leaf, or a third of a labelled diagram found), from the measurements of logs/kf1_shard_timing.log."""
import glob, re

out = []
for f in glob.glob('L6CheckK/F1/Shards/S*.lean'):
    w = 0
    for line in open(f):
        m = re.match(r'def s\d+ : Nat × Nat × List Nat := \((\d+), (\d+), \[(.*)\]\)', line)
        if m:
            codes = m.group(3).strip()
            w = max(w, int(m.group(2)) + 3 * (len(codes.split(',')) if codes else 0))
    out.append((2 + 0.016 * w, f))
for f in glob.glob('L6CheckK/F1/Reps/R*.lean'):
    out.append((5.0, f))
out.sort(reverse=True)
print(' '.join(f'{f}:{e:.1f}' for e, f in out))
