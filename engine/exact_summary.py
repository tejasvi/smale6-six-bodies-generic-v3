#!/usr/bin/env python3
"""Summary of the exact pipeline (jobs/exact_job.sh) from collected result directories exact6/cCLS:
per class the cells, the certified LP failures (must be 0), the exclusions by a single minimal term, the cells whose
core is verified mod p and certified over Q(m), and the unresolved cells.
Usage: exact_summary.py DIR [DIR ...] (each containing exact6/)"""
import glob, json, os, re, sys, hashlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tcorehash
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')


def canon(eqs, sats):
    """As tcert.canon: rename the variables in order of appearance."""
    order = []
    for e in eqs:
        for v in VAR.findall(e):
            if v not in order:
                order.append(v)
    ren = {v: f'v{i}' for i, v in enumerate(order)}
    f = lambda e: VAR.sub(lambda mm: ren[mm.group(0)], e)
    return order, [f(e) for e in eqs], None
tot = {'cells': 0, 'single': 0, 'cert': 0, 'unres': 0, 'fail': 0, 'border': 0, 'replay_lp': 0, 'replay_pruned': 0,
       'sec_pruned': 0}
unres_all = {}
for top in sys.argv[1:]:
    for d in sorted(glob.glob(os.path.join(top, 'exact6', 'c*'))):
        c = int(os.path.basename(d)[1:])
        rep = glob.glob(d + '/rep/p*.jsonl.replay.json')
        fail = border = 0
        for f in rep:
            r = json.load(open(f))
            cnts = r['cert']                       # treplay.py writes its certifier counters under 'cert'
            fail += cnts.get('fail', 0)
            border += cnts.get('border', 0)
            tot['replay_lp'] += cnts.get('lp', 0)
            tot['replay_pruned'] += cnts.get('pruned', 0)
        for f in glob.glob(d + '/sec/p*.sec.jsonl.cert.json'):
            r = json.load(open(f))
            fail += r['counts'].get('fail', 0)
            border += r['counts'].get('border', 0)
            tot['sec_pruned'] += r['counts'].get('pruned', 0)
        certified = {}
        cf = d + '/cert.jsonl'
        if os.path.exists(cf):
            for l in open(cf):
                r = json.loads(l)
                certified[r['hash']] = r['dim_Qm'] == -1
        ncell = sum(1 for _ in open(d + '/cells.jsonl')) if os.path.exists(d + '/cells.jsonl') else None
        single = cert = 0
        seen = set()
        for f in glob.glob(d + '/sec/p*.sec.jsonl'):
            for l in open(f):
                r = json.loads(l)
                seen.add(r['cell'])
                if 'excluded_by' in r:
                    single += 1
        for f in glob.glob(d + '/sec/p*.cores.jsonl'):
            for l in open(f):
                r = json.loads(l)
                if not r.get('verified_modp'):
                    continue
                eqs = r['core_sym']
                vs = sorted(set(v for e in eqs for v in VAR.findall(e)))
                sats = list(vs)
                bynode = {}
                for v in vs:
                    if v[0] in 'XY':
                        bynode.setdefault(v.split('_')[0], []).append(v)
                for node, lst in bynode.items():
                    for i in range(len(lst)):
                        for j in range(i + 1, len(lst)):
                            sats.append(f'({lst[i]}-{lst[j]})')
                ho, hn = tcorehash.hashes(eqs)
                if certified.get(ho) or certified.get(hn):
                    cert += 1
        unres = (ncell or 0) - single - cert
        tot['cells'] += ncell or 0
        tot['single'] += single
        tot['cert'] += cert
        tot['unres'] += unres
        tot['fail'] += fail
        tot['border'] += border
        if unres or fail or ncell is None:
            unres_all[c] = {'cells': ncell, 'seen': len(seen), 'single': single, 'cert': cert, 'unres': unres, 'fail': fail}
print(json.dumps(tot))
print('classes with unresolved cells, failures or incomplete:', json.dumps(unres_all))
