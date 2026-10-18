#!/usr/bin/env python3
"""Compare the referee re-run of a class with the stored engine outputs.
Usage: cmp.py CLASS [CLASS ...]"""
import glob, hashlib, json, os, re, sys
from collections import Counter

STORE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')        # the supplement: results/exact6/cN
MINE = os.environ.get('RERUN_EXACT6', 'rerun/exact6')
VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')


def chash(eqs):
    order = []
    for e in eqs:
        for v in VAR.findall(e):
            if v not in order:
                order.append(v)
    ren = {v: f'v{i}' for i, v in enumerate(order)}
    return hashlib.sha1('\n'.join(VAR.sub(lambda mm: ren[mm.group(0)], e) for e in eqs).encode()).hexdigest()[:16]


def load_dir(d):
    res = {}
    cl = d + '/cells.jsonl'
    res['cells_raw'] = open(cl).read().splitlines() if os.path.exists(cl) else None
    res['cells'] = [json.loads(l) for l in res['cells_raw']] if res['cells_raw'] is not None else None
    rc = Counter()
    refs = Counter()
    for f in glob.glob(d + '/rep/p*.jsonl.replay.json'):
        r = json.load(open(f))
        rc.update(r['cert'])
        if 'ref' in r:
            refs[r['ref']['identical']] += 1
    res['rep'] = rc
    res['refs'] = refs
    sec = {}
    for f in glob.glob(d + '/sec/p*.sec.jsonl'):
        for l in open(f):
            r = json.loads(l)
            sec[r['cell']] = r
    res['sec'] = sec
    sc = Counter()
    for f in glob.glob(d + '/sec/p*.sec.jsonl.cert.json'):
        sc.update(json.load(open(f))['counts'])
    res['secc'] = sc
    cores = {}
    for f in glob.glob(d + '/sec/p*.cores.jsonl'):
        for l in open(f):
            r = json.loads(l)
            cores[r['cell']] = r
    res['cores'] = cores
    cert = {}
    if os.path.exists(d + '/cert.jsonl'):
        for l in open(d + '/cert.jsonl'):
            r = json.loads(l)
            cert[r['hash']] = r['dim_Qm']
    res['cert'] = cert
    return res


def status(R, cell):
    s = R['sec'].get(cell)
    if s is None:
        return 'missing'
    if 'excluded_by' in s:
        return 'single'
    c = R['cores'].get(cell)
    if c is None:
        return 'nocore'
    if not c.get('verified_modp'):
        return 'core_unverified'
    d = R['cert'].get(chash(c['core_sym']))
    return 'certified' if d == -1 else f'cert_dim_{d}'


for cls in sys.argv[1:]:
    c = int(cls)
    sd = glob.glob(f'{STORE}/*/exact6/c{c}')[0]
    A, B = load_dir(sd), load_dir(f'{MINE}/c{c}')
    out = {'class': c}
    out['replay_lps_stored'] = A['rep']['lp']
    out['replay_lps_rerun'] = B['rep']['lp']
    out['replay_pruned'] = (A['rep']['pruned'], B['rep']['pruned'])
    out['replay_fail_border_rerun'] = (B['rep']['fail'], B['rep']['border'])
    out['part_ref_identical'] = dict(B['refs'])
    out['cells'] = (len(A['cells']), len(B['cells']))
    out['cells_bytes_identical'] = A['cells_raw'] == B['cells_raw']
    key = lambda x: json.dumps([x['ztree'], x['wtree'], x['argmin']], sort_keys=True)
    out['cells_combinatorially_identical_in_order'] = [key(x) for x in A['cells']] == [key(x) for x in B['cells']]
    out['sec_cert_rerun'] = {k: B['secc'][k] for k in ('lp', 'pruned', 'fail', 'border')}
    out['sec_cert_stored'] = {k: A['secc'][k] for k in ('lp', 'pruned', 'fail', 'border')}
    ex_same = sys_same = 0
    ex_diff = []
    sys_diff = []
    for cell in range(len(A['cells'])):
        a, b = A['sec'].get(cell), B['sec'].get(cell)
        if a is None or b is None:
            ex_diff.append((cell, 'missing'))
            continue
        if ('excluded_by' in a) != ('excluded_by' in b) or a.get('excluded_by') != b.get('excluded_by'):
            ex_diff.append((cell, a.get('excluded_by'), b.get('excluded_by')))
        elif 'excluded_by' in a:
            ex_same += 1
        else:
            if a['system']['eqs_sym'] == b['system']['eqs_sym'] and a['system']['names'] == b['system']['names']:
                sys_same += 1
            else:
                sys_diff.append(cell)
    out['single_same'] = ex_same
    out['single_or_presence_diff'] = ex_diff[:10]
    out['n_single_or_presence_diff'] = len(ex_diff)
    out['systems_same'] = sys_same
    out['systems_diff'] = sys_diff[:10]
    out['n_systems_diff'] = len(sys_diff)
    core_same = core_diff = 0
    for cell, a in A['cores'].items():
        b = B['cores'].get(cell)
        if b is not None and a['core_sym'] == b['core_sym']:
            core_same += 1
        else:
            core_diff += 1
    out['cores_same'] = core_same
    out['cores_diff'] = core_diff
    sa = Counter(status(A, i) for i in range(len(A['cells'])))
    sb = Counter(status(B, i) for i in range(len(B['cells'])))
    out['status_stored'] = dict(sa)
    out['status_rerun'] = dict(sb)
    trans = Counter((status(A, i), status(B, i)) for i in range(len(A['cells'])))
    out['status_transitions'] = {f'{k[0]}->{k[1]}': v for k, v in trans.items()}
    out['distinct_cores'] = (len(A['cert']), len(B['cert']))
    out['cert_dims_rerun'] = dict(Counter(B['cert'].values()))
    print(json.dumps(out))
