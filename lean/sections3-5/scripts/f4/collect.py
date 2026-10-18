#!/usr/bin/env python3
"""Collect the certified cores of Proposition 5.3 and link them to their cells.

First pass (Lemma 5.2(a)): per class, the cells of exact6/c<N>/sec/p*.cores.jsonl whose core (verified mod p) has
dim_Qm = -1 in exact6/c<N>/cert.jsonl under the engine's canonical hash, excluding the single-term cells.
Second pass (Lemma 5.2(b)): the records with "certified": true of the alternative-core runs; the mass of least index
occurring in the core is set to 1, as in the engine's certification.

Each core polynomial is parsed exactly (python-flint), multiplied by the lcm of the denominators of its rational
coefficients, then m_F is replaced by 1 (second pass); the cell variables are renamed x0..x(V-1) in order of first
appearance in the stored core strings (generators in the stored order, left to right), keeping only variables that
occur in the resulting generators.  Identical generator lists are stored once, under the first 16 hex digits of the
SHA-256 of their generator block (certfmt.gen_block).

Usage: collect.py IN_DIR OUT_DIR [--replace REPL.jsonl]
--replace: records {"class", "cell", "names", "core_sym", "fixed", "source"} that replace the stored core of a cell
by another subset of its initial system (found by altcore.py and certified by lift.py); the replaced cells are
listed in logs/f4/replaced.jsonl.
IN_DIR: exact6/c<N>/cert.jsonl, exact6/c<N>/sec/p*.cores.jsonl, alt_out.jsonl, alt3_out.jsonl, uncertified.json,
        GENERIC_OPEN.txt, single_term.txt (lines "class cell" of the cells excluded by a single term).
OUT_DIR: data/f4/cores.jsonl, data/f4/links/c<N>.txt, logs/f4/collect.json."""
import glob
import hashlib
import json
import math
import os
import re
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import flint  # noqa: E402
import certfmt as CF  # noqa: E402

VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')
MASS = re.compile(r'\bm(\d)\b')


# ---- the engine's canonical hashes of a core (old: equations only; new: equations and saturation set) ----------
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


def engine_hashes(eqs):
    order = []
    for e in eqs:
        for v in VAR.findall(e):
            if v not in order:
                order.append(v)
    ren = {v: f'v{i}' for i, v in enumerate(order)}
    f = lambda e: VAR.sub(lambda mm: ren[mm.group(0)], e)  # noqa: E731
    ceqs = [f(e) for e in eqs]
    sats = sats_of(eqs)
    csats = sorted(set(f(s) for s in sats if VAR.findall(s) and all(v in ren for v in VAR.findall(s))))
    old = hashlib.sha1('\n'.join(ceqs).encode()).hexdigest()[:16]
    new = hashlib.sha1(('\n'.join(ceqs) + '\n#sat\n' + '\n'.join(csats)).encode()).hexdigest()[:16]
    return old, new


def encode_name(n):
    s = n.replace(' ', '').replace("'", '')
    assert re.fullmatch(r'[A-Za-z0-9(),]+', s), n
    return s


def fixed_mass(eqs):
    ms = sorted(set(int(k) for e in eqs for k in MASS.findall(e)))
    return ms[0] if ms else -1


def C_fixed_ok(eqs, fixed):
    """F = -1, or F is a mass that occurs in the core (Lemma 5.2(b) allows any mass; the engine used the least)."""
    return fixed == -1 or str(fixed) in MASS.findall(' '.join(eqs))


def build_core(eqs, fixed, stats):
    order = []
    for e in eqs:
        for v in VAR.findall(e):
            if v not in order:
                order.append(v)
    n0 = len(order)
    ctx = flint.fmpq_mpoly_ctx.get(CF.MASSES + tuple(f'x{j}' for j in range(n0)), 'lex')
    gens_ = ctx.gens()
    names = {m: gens_[k] for k, m in enumerate(CF.MASSES)}
    for j, v in enumerate(order):
        names[v] = gens_[CF.NMASS + j]
    gens = []
    for e in eqs:
        p = CF.parse_poly(e, ctx, names)
        d = p.to_dict()
        L = 1
        for c in d.values():
            L = L * int(c.q) // math.gcd(L, int(c.q))
        if L != 1:
            stats['scaled_' + str(L)] += 1
        g = {}
        for k, c in d.items():
            ci = int(c.p) * (L // int(c.q))
            if fixed >= 0 and k[fixed]:
                k = k[:fixed] + (0,) + k[fixed + 1:]
            g[k] = g.get(k, 0) + ci
        g = {k: c for k, c in g.items() if c}
        if not g:
            stats['zero_generator'] += 1
        gens.append(g)
    used = [j for j in range(n0) if any(k[CF.NMASS + j] for g in gens for k in g)]
    if len(used) != n0:
        stats['string_var_not_in_gens'] += 1
    pos = {j: i for i, j in enumerate(used)}
    gens2 = []
    for g in gens:
        g2 = {}
        for k, c in g.items():
            kk = [0] * (CF.NMASS + len(used))
            kk[:CF.NMASS] = k[:CF.NMASS]
            for j in used:
                kk[CF.NMASS + pos[j]] = k[CF.NMASS + j]
            g2[tuple(kk)] = c
        gens2.append(g2)
    renaming = [order[j] for j in used]
    block = CF.gen_block(len(used), fixed, gens2)
    return CF.cert_id(block), block, renaming


def main():
    ind, outd = sys.argv[1], sys.argv[2]
    stats = Counter()
    single = set()
    for ln in open(os.path.join(ind, 'single_term.txt')):
        if ln.strip():
            c, cell = map(int, ln.split())
            single.add((c, cell))
    uncert = {(r['class'], r['cell']) for r in json.load(open(os.path.join(ind, 'uncertified.json')))}
    open43 = set()
    for ln in open(os.path.join(ind, 'GENERIC_OPEN.txt')):
        if ln.strip() and not ln.startswith('#'):
            t = ln.split('\t')
            open43.add((int(t[0]), int(t[2])))
    recs = []
    seen = set()
    within = set()
    cert_neg = 0
    for d in sorted(glob.glob(os.path.join(ind, 'exact6', 'c*')), key=lambda x: int(x.rsplit('c', 1)[1])):
        c = int(d.rsplit('c', 1)[1])
        cert = {}
        if os.path.exists(os.path.join(d, 'cert.jsonl')):
            for ln in open(os.path.join(d, 'cert.jsonl')):
                r = json.loads(ln)
                cert[r['hash']] = r['dim_Qm']
        cert_neg += sum(1 for v in cert.values() if v == -1)
        for f in sorted(glob.glob(os.path.join(d, 'sec', 'p*.cores.jsonl')),
                        key=lambda x: int(os.path.basename(x)[1:].split('.')[0])):
            for ln in open(f):
                if not ln.strip():
                    continue
                r = json.loads(ln)
                stats['first_pass_core_records'] += 1
                key = (c, r['cell'])
                if key in seen:
                    stats['duplicate_core_record'] += 1
                    continue
                seen.add(key)
                if not r.get('verified_modp'):
                    stats['first_pass_not_verified_modp'] += 1
                    continue
                ho, hn = engine_hashes(r['core_sym'])
                h = hn if hn in cert else ho
                if cert.get(h) != -1:
                    stats['first_pass_core_not_certified'] += 1
                    continue
                if key in single:
                    stats['first_pass_certified_but_single_term'] += 1
                    continue
                if key in uncert:
                    stats['first_pass_certified_but_listed_uncertified'] += 1
                within.add((c, h))
                recs.append((c, r['cell'], -1, r['core_sym'], r['names'], f'{c}:{h}'))
    stats['first_pass_cells'] = len(recs)
    stats['first_pass_distinct_within_classes'] = len(within)
    stats['cert_jsonl_entries_dim_minus1'] = cert_neg
    nalt = 0
    for fn in ('alt_out.jsonl', 'alt3_out.jsonl'):
        for ln in open(os.path.join(ind, fn)):
            if not ln.strip():
                continue
            r = json.loads(ln)
            if r.get('certified') is not True:
                stats['alt_not_certified'] += 1
                continue
            key = (r['class'], r['cell'])
            if key in seen and key not in uncert:
                stats['alt_cell_has_first_pass_certificate'] += 1
            if key not in uncert:
                stats['alt_cell_not_in_uncertified'] += 1
            if key in single:
                stats['alt_cell_single_term'] += 1
            F = fixed_mass(r['core_sym'])
            if F < 0:
                stats['alt_core_without_masses'] += 1
            recs.append((r['class'], r['cell'], F, r['core_sym'], r['names'], f'{r["class"]}:cell{r["cell"]}'))
            nalt += 1
    stats['alt_cells'] = nalt
    keys = [(r[0], r[1]) for r in recs]
    stats['duplicate_cells_across_passes'] = len(keys) - len(set(keys))
    replaced = []
    if '--replace' in sys.argv:
        repl = {}
        for ln in open(sys.argv[sys.argv.index('--replace') + 1]):
            if ln.strip():
                r = json.loads(ln)
                repl[(r['class'], r['cell'])] = r
        pos = {(r[0], r[1]): i for i, r in enumerate(recs)}
        for key, r in sorted(repl.items()):
            assert key in pos, key
            old = recs[pos[key]]
            assert C_fixed_ok(r['core_sym'], r['fixed'])
            recs[pos[key]] = (key[0], key[1], r['fixed'], r['core_sym'], r['names'],
                              f'{key[0]}:cell{key[1]}:{r["source"]}')
            ocid = build_core(old[3], old[2], Counter())[0]
            replaced.append({'class': key[0], 'cell': key[1], 'engine_certid': ocid, 'engine_fixed': old[2],
                             'engine_names': [encode_name(n) for n in old[4]], 'fixed': r['fixed'],
                             'names': [encode_name(n) for n in r['names']], 'source': r['source']})
    stats['replaced_cells'] = len(replaced)
    covered = set(keys)
    stats['uncertified_minus_alt'] = len(uncert - covered)
    stats['uncertified_minus_alt_equals_open43'] = int((uncert - covered) == open43)
    stats['open43'] = len(open43)

    cores = {}
    links = defaultdict(list)
    for c, cell, F, eqs, names, ref in recs:
        assert len(eqs) == len(names)
        cid, block, ren = build_core(eqs, F, stats)
        if cid in cores:
            assert cores[cid]['block'] == block
        else:
            cores[cid] = {'certid': cid, 'fixed': F, 'nvar': len(ren), 'ngens': len(eqs),
                          'nterms': sum(1 for ln in block.split('\n') if ln and ln[0] in '-0123456789'),
                          'block': block, 'cells': 0, 'refs': set(), 'kind': 'b' if F >= 0 else 'a'}
        cores[cid]['cells'] += 1
        cores[cid]['refs'].add(ref)
        links[c].append((cell, f'{c} {cell} {cid} {F} ' + ' '.join(encode_name(n) for n in names) + ' | ' +
                         ' '.join(ren)))
    stats['distinct_cores'] = len(cores)
    stats['distinct_cores_first_pass'] = sum(1 for v in cores.values() if v['fixed'] < 0)
    stats['distinct_cores_alt'] = sum(1 for v in cores.values() if v['fixed'] >= 0)
    os.makedirs(os.path.join(outd, 'data', 'f4', 'links'), exist_ok=True)
    os.makedirs(os.path.join(outd, 'logs', 'f4'), exist_ok=True)
    with open(os.path.join(outd, 'data', 'f4', 'cores.jsonl'), 'w') as fh:
        for cid in sorted(cores):
            v = dict(cores[cid])
            v['refs'] = sorted(v['refs'])
            fh.write(json.dumps(v) + '\n')
    nl = 0
    for c in sorted(links):
        with open(os.path.join(outd, 'data', 'f4', 'links', f'c{c}.txt'), 'w') as fh:
            for cell, line in sorted(links[c]):
                fh.write(line + '\n')
                nl += 1
    if replaced:
        with open(os.path.join(outd, 'logs', 'f4', 'replaced.jsonl'), 'w') as fh:
            for r in replaced:
                key = (r['class'], r['cell'])
                r['certid'] = [ln for cl, ln in links[key[0]] if cl == key[1]][0].split()[2]
                fh.write(json.dumps(r) + '\n')
    stats['link_lines'] = nl
    stats['link_files'] = len(links)
    json.dump(dict(sorted(stats.items())), open(os.path.join(outd, 'logs', 'f4', 'collect.json'), 'w'), indent=1)
    for k, v in sorted(stats.items()):
        print(k, v)


if __name__ == '__main__':
    main()
