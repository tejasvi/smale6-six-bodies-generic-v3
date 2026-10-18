#!/usr/bin/env python3
"""Independent bookkeeping of the stored exact pipeline (referee script; reads only).
Usage: bk.py EXACT_COLLECT_DIR OUT.json
For every class directory exact6/cN found under EXACT_COLLECT_DIR/*/:
  replay parts (384 .done and .replay.json; certificate counts read from the 'cert' key),
  cells.jsonl vs the concatenated parts, sec coverage (every cell exactly once), single-term exclusions,
  tsec_exact certificate counts, cores (verified mod p, hash certified in cert.jsonl), and the
  tcert hash-merge check (members of a hash group must have the same saturation set as the representative)."""
import glob, hashlib, json, os, re, sys
from collections import Counter, defaultdict

VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')


def sats_of(eqs):
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
    return sats


def canon(eqs, sats):
    order = []
    for e in eqs:
        for v in VAR.findall(e):
            if v not in order:
                order.append(v)
    ren = {v: f'v{i}' for i, v in enumerate(order)}
    f = lambda e: VAR.sub(lambda mm: ren[mm.group(0)], e)
    ceqs = [f(e) for e in eqs]
    csats = sorted(set(nrm(f(s)) for s in sats if VAR.findall(s) and all(v in ren for v in VAR.findall(s))))
    return ceqs, csats


def nrm(s):
    # (a-b) and (b-a) generate the same saturation
    m = re.fullmatch(r'\((v\d+)-(v\d+)\)', s)
    if m:
        a, b = sorted([m.group(1), m.group(2)], key=lambda t: int(t[1:]))
        return f'({a}-{b})'
    return s


def chash(ceqs):
    return hashlib.sha1('\n'.join(ceqs).encode()).hexdigest()[:16]


root, outp = sys.argv[1], sys.argv[2]
dirs = sorted(glob.glob(os.path.join(root, '*', 'exact6', 'c*')))
seen_cls = Counter(int(os.path.basename(d)[1:]) for d in dirs)
report = {'classes_found': len(seen_cls), 'dup_classes': [c for c, k in seen_cls.items() if k > 1],
          'missing_classes': [c for c in range(191) if c not in seen_cls], 'per_class': {}}
tot = Counter()
uncert = []
merge_issues = []
for d in dirs:
    c = int(os.path.basename(d)[1:])
    pc = {}
    # replay parts
    done = len(glob.glob(d + '/rep/p*.jsonl.done'))
    reps = glob.glob(d + '/rep/p*.jsonl.replay.json')
    rc = Counter()
    min_kept, max_pruned = float('inf'), float('-inf')
    nref = 0
    refbad = 0
    parts_lines = 0
    for f in reps:
        r = json.load(open(f))
        for k, v in r['cert'].items():
            rc[k] += v
        min_kept = min(min_kept, r['min_kept_slack'])
        max_pruned = max(max_pruned, r['max_pruned_opt'])
        if len(r.get('failures', [])) or len(r.get('borderline', [])):
            rc['listed_fail_or_border'] += 1
        if 'ref' in r:
            nref += 1
            refbad += 0 if r['ref']['identical'] else 1
        if r['stats']['cells'] != sum(1 for _ in open(f[:-len('.replay.json')])):
            rc['stats_cells_mismatch'] += 1
        parts_lines += r['stats']['cells']
    pc['rep_done'] = done
    pc['rep_json'] = len(reps)
    pc['rep_cert'] = dict(rc)
    pc['min_kept_slack'] = min_kept
    pc['max_pruned_opt'] = max_pruned
    pc['ref_checked'] = nref
    pc['ref_not_identical'] = refbad
    # cells
    cl = d + '/cells.jsonl'
    nc = sum(1 for _ in open(cl)) if os.path.exists(cl) else None
    pc['cells'] = nc
    pc['parts_lines'] = parts_lines
    # cells.jsonl must be the concatenation of the parts in shell glob order
    if nc:
        parts = sorted(glob.glob(d + '/rep/p*.jsonl'))       # C-locale order = bash glob order here
        h1 = hashlib.sha1()
        for f in parts:
            h1.update(open(f, 'rb').read())
        h2 = hashlib.sha1(open(cl, 'rb').read())
        pc['cells_is_concat'] = h1.hexdigest() == h2.hexdigest()
        sumx = [json.loads(l)['sumx'] for l in open(cl)]
    else:
        pc['cells_is_concat'] = None if nc is None else True
        sumx = []
    # sec
    recs = {}
    dupl = 0
    sc = Counter()
    for f in glob.glob(d + '/sec/p*.sec.jsonl'):
        for l in open(f):
            r = json.loads(l)
            if r['cell'] in recs:
                dupl += 1
            recs[r['cell']] = ('single' if 'excluded_by' in r else 'system' if 'system' in r else 'other')
    for f in glob.glob(d + '/sec/p*.sec.jsonl.cert.json'):
        r = json.load(open(f))
        for k, v in r['counts'].items():
            sc[k] += v
    pc['sec_cert'] = dict(sc)
    pc['sec_records'] = len(recs)
    pc['sec_dupl'] = dupl
    pc['sec_missing'] = [i for i in range(nc or 0) if i not in recs][:20]
    pc['sec_n_missing'] = sum(1 for i in range(nc or 0) if i not in recs)
    pc['single'] = sum(1 for v in recs.values() if v == 'single')
    pc['system'] = sum(1 for v in recs.values() if v == 'system')
    pc['other'] = sum(1 for v in recs.values() if v == 'other')
    # cert.jsonl
    cert = {}
    certrep = {}
    if os.path.exists(d + '/cert.jsonl'):
        for l in open(d + '/cert.jsonl'):
            r = json.loads(l)
            cert[r['hash']] = r['dim_Qm']
            certrep[r['hash']] = r
    # cores
    cores = {}
    cdupl = 0
    groups = defaultdict(list)
    file_order = sorted(glob.glob(d + '/sec/p*.cores.jsonl'))
    for f in file_order:
        for l in open(f):
            r = json.loads(l)
            if r['cell'] in cores:
                cdupl += 1
            eqs = r['core_sym']
            ceqs, csats = canon(eqs, sats_of(eqs))
            h = chash(ceqs)
            cores[r['cell']] = (bool(r.get('verified_modp')), h)
            groups[h].append((tuple(csats), os.path.basename(f), r['cell']))
    pc['cores'] = len(cores)
    pc['cores_dupl'] = cdupl
    ok = 0
    notver = 0
    notcert = 0
    for cell, (ver, h) in cores.items():
        if not ver:
            notver += 1
        elif cert.get(h) == -1:
            ok += 1
        else:
            notcert += 1
    pc['cores_certified'] = ok
    pc['cores_not_verified'] = notver
    pc['cores_not_certified'] = notcert
    pc['system_without_core'] = sum(1 for cell, v in recs.items() if v == 'system' and cell not in cores)
    # hash merge check: tcert used the csats of the first member in its file order (sorted? it used argv order)
    gmix = 0
    for h, mem in groups.items():
        cs = set(m[0] for m in mem)
        if len(cs) > 1:
            gmix += 1
            merge_issues.append({'class': c, 'hash': h, 'n_members': len(mem), 'n_distinct_csats': len(cs),
                                 'certified': cert.get(h), 'example': certrep.get(h, {}).get('example'),
                                 'members': [(m[1], m[2], list(m[0])) for m in mem[:6]]})
    pc['hash_groups'] = len(groups)
    pc['hash_groups_mixed_sats'] = gmix
    # unresolved cells
    for cell in range(nc or 0):
        st = recs.get(cell)
        if st == 'single':
            continue
        if cell in cores and cores[cell][0] and cert.get(cores[cell][1]) == -1:
            continue
        uncert.append({'class': c, 'cell': cell, 'sumx': sumx[cell] if cell < len(sumx) else None,
                       'why': 'no sec record' if st is None else ('no core' if cell not in cores else
                              'core not verified' if not cores[cell][0] else f'core {cores[cell][1]} dim {cert.get(cores[cell][1])}')})
    report['per_class'][c] = pc
    tot['cells'] += nc or 0
    tot['single'] += pc['single']
    tot['cores_certified'] += ok
    tot['rep_fail'] += rc['fail']
    tot['rep_border'] += rc['border']
    tot['rep_lp'] += rc['lp']
    tot['rep_pruned'] += rc['pruned']
    tot['sec_fail'] += sc['fail']
    tot['sec_border'] += sc['border']
    tot['sec_lp'] += sc['lp']
    tot['rep_incomplete'] += 0 if (done == 384 and len(reps) == 384) else 1
    tot['sec_missing'] += pc['sec_n_missing']
    tot['sec_dupl'] += dupl
    tot['mixed_groups'] += gmix
    tot['stats_cells_mismatch'] += rc['stats_cells_mismatch']
    tot['not_concat'] += 0 if pc['cells_is_concat'] in (True, None) else 1
tot['uncertified'] = len(uncert)
report['totals'] = dict(tot)
report['uncertified'] = uncert
report['merge_issues'] = merge_issues
json.dump(report, open(outp, 'w'), indent=1, default=str)
print(json.dumps(report['totals']))
print('classes found', report['classes_found'], 'dup', report['dup_classes'], 'missing', report['missing_classes'])
print('uncertified by class', dict(Counter(u['class'] for u in uncert)))
print('merge issues', len(merge_issues))
