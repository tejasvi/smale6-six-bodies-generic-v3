"""Classify the 1,033 cells left by the first pass (engine/runs/uncertified.json) by cause:
(i) the core search was stopped (reason 'core search timed out (no core)');
(ii) the core's certification ran and returned no verdict (hash present in the class's cert.jsonl with dim None);
(iii) the core's certification never ran (hash absent from cert.jsonl; the class has no cert.jsonl.done).
Also reports, for the 43 open cells, which pass-2 outcome is recorded in alt_out.jsonl / alt3_out.jsonl.
Usage: python3 -I uncert_causes.py SUPPLEMENT_ROOT"""
import json, sys, os, glob, collections
root = sys.argv[1]
unc = json.load(open(os.path.join(root, 'results', 'uncertified.json')))
coll = root
classdir = {}
for d in glob.glob(os.path.join(coll, '*', 'exact6', 'c*')):
    c = int(d.rsplit('/c', 1)[1])
    assert c not in classdir, c
    classdir[c] = d
certs = {}
for c, d in classdir.items():
    f = os.path.join(d, 'cert.jsonl')
    h = {}
    if os.path.exists(f):
        for l in open(f):
            if l.strip():
                r = json.loads(l)
                h[r['hash']] = r.get('dim_Qm')
    certs[c] = (h, os.path.exists(f + '.done'))
cause = collections.Counter()
bycls = collections.defaultdict(collections.Counter)
for u in unc:
    c = u['class']
    if u['reason'].startswith('core search timed out'):
        k = 'search stopped'
    else:
        hsh = u['reason'].split()[1]
        h, done = certs[c]
        if hsh in h:
            k = 'certification ran, no verdict (dim %s)' % h[hsh]
        else:
            k = 'certification never ran (cert.jsonl.done %s)' % done
    cause[k] += 1
    bycls[k][c] += 1
print('total', len(unc))
for k, v in cause.items():
    print(f'{v:5d}  {k}  classes: {dict(sorted(bycls[k].items()))}')
nodone = sorted(c for c, (h, done) in certs.items() if os.path.exists(os.path.join(classdir[c], 'cert.jsonl')) and not done)
print('classes with cert.jsonl but no cert.jsonl.done:', nodone)
