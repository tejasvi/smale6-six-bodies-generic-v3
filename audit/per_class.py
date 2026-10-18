#!/usr/bin/env python3
"""Per-class counts of the exact generic pipeline (results/exact6/cCLS; the original tree had one directory per machine), with the counting
rules of engine/exact_summary.py: cells, exclusions by a single minimal term, cells whose core is verified mod p
and certified over Q(m), and the rest. It also sums the certificate counters of the replay (treplay.py writes them
under the key 'cert') and of tsec_exact.py (key 'counts').
Usage: per_class.py EXACT_COLLECT_DIR N6_JSON CC_COMPARE_JSON > per_class.tsv"""
import glob, json, os, re, sys, hashlib

VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')
SUMKEYS = ('cells', 'single', 'cert', 'unres', 'replay_files', 'replay_lp', 'replay_pruned', 'replay_fail',
           'replay_border', 'rat_dual', 'rat_ray', 'supp', 'full', 'sec_pruned', 'sec_fail', 'sec_border',
           'failures_listed')


def canon(eqs):
    order = []
    for e in eqs:
        for v in VAR.findall(e):
            if v not in order:
                order.append(v)
    ren = {v: f'v{i}' for i, v in enumerate(order)}
    return [VAR.sub(lambda mm: ren[mm.group(0)], e) for e in eqs]


top, n6, ccc = sys.argv[1], sys.argv[2], sys.argv[3]
cls = json.load(open(n6))['classes']
cc_of = {r['ours']: r['cc'] for r in json.load(open(ccc))['per_cc']}
dirs = {}
for d in glob.glob(os.path.join(top, '*', 'exact6', 'c*')):
    dirs.setdefault(int(os.path.basename(d)[1:]), []).append(d)
tot = {k: 0 for k in SUMKEYS}
tot.update({'classes_with_cells': 0, 'min_kept_slack': float('inf'), 'max_pruned_opt': float('-inf')})
print('\t'.join(('class', 'cc', 'labelled', 'ndirs') + SUMKEYS + ('min_kept_slack', 'max_pruned_opt')))
for c in range(len(cls)):
    ds = dirs.get(c, [])
    row = {k: 0 for k in SUMKEYS}
    mk, mp = float('inf'), float('-inf')
    for d in ds:
        for f in glob.glob(d + '/rep/p*.jsonl.replay.json'):
            r = json.load(open(f))
            cnt = r['cert']
            row['replay_files'] += 1
            row['replay_lp'] += cnt['lp']
            row['replay_pruned'] += cnt['pruned']
            row['replay_fail'] += cnt['fail']
            row['replay_border'] += cnt['border']
            for key in ('rat_dual', 'rat_ray', 'supp', 'full'):
                row[key] += cnt[key]
            row['failures_listed'] += len(r.get('failures', []))
            mk = min(mk, r.get('min_kept_slack', float('inf')))
            mp = max(mp, r.get('max_pruned_opt', float('-inf')))
        for f in glob.glob(d + '/sec/p*.sec.jsonl.cert.json'):
            r = json.load(open(f))
            row['sec_pruned'] += r['counts']['pruned']
            row['sec_fail'] += r['counts']['fail']
            row['sec_border'] += r['counts']['border']
            row['failures_listed'] += len(r.get('fails', []))
        certified = {}
        if os.path.exists(d + '/cert.jsonl'):
            for l in open(d + '/cert.jsonl'):
                r = json.loads(l)
                certified[r['hash']] = r['dim_Qm'] == -1
        if os.path.exists(d + '/cells.jsonl'):
            row['cells'] += sum(1 for _ in open(d + '/cells.jsonl'))
        for f in glob.glob(d + '/sec/p*.sec.jsonl'):
            for l in open(f):
                if 'excluded_by' in json.loads(l):
                    row['single'] += 1
        for f in glob.glob(d + '/sec/p*.cores.jsonl'):
            for l in open(f):
                r = json.loads(l)
                if r.get('verified_modp') and certified.get(
                        hashlib.sha1('\n'.join(canon(r['core_sym'])).encode()).hexdigest()[:16]):
                    row['cert'] += 1
    row['unres'] = row['cells'] - row['single'] - row['cert']
    for k in SUMKEYS:
        tot[k] += row[k]
    tot['classes_with_cells'] += 1 if row['cells'] else 0
    tot['min_kept_slack'] = min(tot['min_kept_slack'], mk)
    tot['max_pruned_opt'] = max(tot['max_pruned_opt'], mp)
    print('\t'.join(str(x) for x in (c, cc_of.get(c, ''), cls[c]['labelled'], len(ds))
                    + tuple(row[k] for k in SUMKEYS) + (mk, mp)))
print('#TOTAL\t' + json.dumps(tot))
