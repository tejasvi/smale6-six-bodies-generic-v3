#!/usr/bin/env python3
"""Totals of the certificate counters, read from the raw files: replay (key 'cert' of rep/p*.jsonl.replay.json) and
tsec_exact (key 'counts' of sec/p*.sec.jsonl.cert.json). Checks pruned = rat_dual + rat_ray + supp + full + fail and
lp = kept + pruned in every file; least kept slack; largest optimal value among prunes."""
import glob, json, os, sys
from collections import Counter
root = sys.argv[1]
R, S = Counter(), Counter()
bad = []
mink, maxp = float('inf'), float('-inf')
nrep = nsec = 0
for f in glob.glob(os.path.join(root, '*', 'exact6', 'c*', 'rep', 'p*.jsonl.replay.json')):
    r = json.load(open(f)); c = r['cert']; nrep += 1
    R.update(c)
    if c['pruned'] != c['rat_dual'] + c['rat_ray'] + c['supp'] + c['full'] + c['fail'] or c['lp'] != c['kept'] + c['pruned'] \
       or c['pruned'] != c['st_opt'] + c['st_inf'] + c['st_other']:
        bad.append(f)
    if r['stats']['lp'] != c['lp']:
        bad.append(('statslp', f))
    mink = min(mink, r['min_kept_slack']); maxp = max(maxp, r['max_pruned_opt'])
for f in glob.glob(os.path.join(root, '*', 'exact6', 'c*', 'sec', 'p*.sec.jsonl.cert.json')):
    r = json.load(open(f)); c = r['counts']; nsec += 1
    S.update(c)
    if c['pruned'] != c['rat_dual'] + c['rat_ray'] + c['supp'] + c['full'] + c['fail'] or c['lp'] != c['kept'] + c['pruned']:
        bad.append(f)
    if r['fails'] or r['border']:
        bad.append(('listed', f))
print('replay files', nrep, dict(R))
print('least kept slack (replay)', mink, ' largest optimal value among replay prunes', maxp)
print('sec cert files', nsec, dict(S))
print('inconsistent files', len(bad), bad[:5])
