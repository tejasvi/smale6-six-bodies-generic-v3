#!/usr/bin/env python3
"""Second, independent check of the F4 data (untrusted; Lean re-checks everything):
(1) for every link line, the cell's core polynomials (from the engine data, or from the replacement record), parsed
    with SymPy (not with the parser of collect.py), multiplied by the lcm of their coefficient denominators, renamed
    by the link's renaming and with m_F = 1, are exactly the generators of the certificate, in the stored order, and
    the names of the link are the stored names;
(2) every certificate referenced by a link passes certfmt.verify_cert (exact identity, h free of the variables,
    h nonzero at the point, certid = SHA-256 of the generator block); no other files are in data/f4/certs/.
Usage: check.py IN_DIR RUN_DIR [--replace REPL.jsonl [--systems SYSTEMS.jsonl]] [--jobs J] [--skip-verify]
--systems: the initial systems of the replaced cells (as for altcore.py); then each (name, polynomial) pair of a
replacement core must be a pair of the cell's stored initial system.
Writes RUN_DIR/logs/f4/check.json."""
import glob
import json
import os
import re
import sys
from multiprocessing import Pool

import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import certfmt as CF  # noqa: E402

IND, RUN = sys.argv[1], sys.argv[2]
JOBS = int(sys.argv[sys.argv.index('--jobs') + 1]) if '--jobs' in sys.argv else 64
VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')
CERTS = os.path.join(RUN, 'data', 'f4', 'certs')


def cert_path(cid):
    for ext in ('.txt', '.txt.gz'):
        p = os.path.join(CERTS, cid + ext)
        if os.path.exists(p):
            return p
    return None


def gen_block_dicts(path):
    """Generators of a certificate, read up to the first cofactor line (a separate small reader)."""
    gens = []
    with CF.open_text(path) as fh:
        t = fh.readline().split()
        assert t == ['L6CERT', '1']
        t = fh.readline().split()
        nvar, fixed = int(t[3]), int(t[5])
        ng = int(fh.readline().split()[1])
        for i in range(ng):
            t = fh.readline().split()
            assert t[:2] == ['gen', str(i)]
            d = {}
            for _ in range(int(t[2])):
                a = [int(x) for x in fh.readline().split()]
                k = [0] * (6 + nvar)
                k[:6] = a[1:7]
                for q in range(a[7]):
                    k[6 + a[8 + 2 * q]] = a[9 + 2 * q]
                d[tuple(k)] = a[0]
            gens.append(d)
    return nvar, fixed, gens


def sympy_generator(e, fixed, ren):
    ms = sp.symbols('m0:6')
    loc = {f'm{k}': ms[k] for k in range(6)}
    xs = sp.symbols(f'x0:{len(ren)}') if ren else ()
    for j, v in enumerate(ren):
        loc[v] = xs[j]
    expr = sp.sympify(e.replace('^', '**'), locals=loc)
    P = sp.Poly(sp.expand(expr), *ms, *xs, domain='QQ')
    L = 1
    for c in P.coeffs():
        L = sp.ilcm(L, sp.Rational(c).q)
    d = {}
    for k, c in P.terms():
        c = sp.Rational(c) * L
        assert c.q == 1
        k = list(k)
        if fixed >= 0:
            k[fixed] = 0
        k = tuple(k)
        d[k] = d.get(k, 0) + int(c.p)
    return {k: c for k, c in d.items() if c}


CORES = {}


def check_class(item):
    cls, lines = item
    cores = CORES
    bad = []
    n = 0
    for ln in lines:
        left, right = ln.split(' | ')
        t = left.split()
        c, cell, cid, F = int(t[0]), int(t[1]), t[2], int(t[3])
        names = t[4:]
        ren = right.split()
        core_sym, snames = cores[(c, cell)]
        enc = [s.replace(' ', '').replace("'", '') for s in snames]
        if enc != names:
            bad.append((c, cell, 'names differ'))
            continue
        used = set(v for e in core_sym for v in VAR.findall(e))
        if set(ren) != used or len(ren) != len(set(ren)):
            bad.append((c, cell, 'renaming is not a bijection onto the core variables'))
            continue
        p = cert_path(cid)
        if p is None:
            bad.append((c, cell, 'no certificate'))
            continue
        nvar, fixed, gens = gen_block_dicts(p)
        if fixed != F or nvar != len(ren) or len(gens) != len(core_sym):
            bad.append((c, cell, 'header differs'))
            continue
        for i, e in enumerate(core_sym):
            if sympy_generator(e, F, ren) != gens[i]:
                bad.append((c, cell, f'generator {i} differs'))
                break
        n += 1
    return cls, n, bad


def verify_one(cid):
    p = cert_path(cid)
    ok, msg = CF.verify_cert(p, expect_id=cid)
    return cid, ok, msg


def main():
    cores = CORES
    for d in glob.glob(os.path.join(IND, 'exact6', 'c*')):
        c = int(d.rsplit('c', 1)[1])
        for f in glob.glob(os.path.join(d, 'sec', 'p*.cores.jsonl')):
            for ln in open(f):
                if ln.strip():
                    r = json.loads(ln)
                    cores.setdefault((c, r['cell']), (r['core_sym'], r['names']))
    for fn in ('alt_out.jsonl', 'alt3_out.jsonl'):
        for ln in open(os.path.join(IND, fn)):
            r = json.loads(ln)
            if r.get('certified') is True:
                cores[(r['class'], r['cell'])] = (r['core_sym'], r['names'])
    repl_bad = []
    if '--replace' in sys.argv:
        systems = {}
        if '--systems' in sys.argv:
            for ln in open(sys.argv[sys.argv.index('--systems') + 1]):
                r = json.loads(ln)
                systems[(r['class'], r['cell'])] = set(zip(r['system']['names'], r['system']['eqs_sym']))
        for ln in open(sys.argv[sys.argv.index('--replace') + 1]):
            r = json.loads(ln)
            key = (r['class'], r['cell'])
            cores[key] = (r['core_sym'], r['names'])
            # each (identity name, polynomial) of a replacement core is a pair of the cell's stored initial system
            if systems and not set(zip(r['names'], r['core_sym'])) <= systems.get(key, set()):
                repl_bad.append(key)
    items = []
    referenced = set()
    for f in sorted(glob.glob(os.path.join(RUN, 'data', 'f4', 'links', 'c*.txt'))):
        lines = [ln.rstrip('\n') for ln in open(f) if ln.strip()]
        cls = int(os.path.basename(f)[1:-4])
        for ln in lines:
            referenced.add(ln.split()[2])
        # split big classes into chunks for the pool
        for k in range(0, len(lines), 500):
            items.append((cls, lines[k:k + 500]))
    res = {'link_lines_checked': 0, 'link_problems': [], 'certificates_referenced': len(referenced),
           'replacement_pairs_not_in_system': repl_bad}
    with Pool(JOBS) as pool:
        for cls, n, bad in pool.imap_unordered(check_class, items):
            res['link_lines_checked'] += n
            res['link_problems'].extend(bad)
        if '--skip-verify' not in sys.argv:
            nok = 0
            fails = []
            for cid, ok, msg in pool.imap_unordered(verify_one, sorted(referenced, key=lambda c: -os.path.getsize(
                    cert_path(c) or __file__))):
                if ok:
                    nok += 1
                else:
                    fails.append((cid, msg))
            res['certificates_verified'] = nok
            res['certificate_failures'] = fails
    files = os.listdir(CERTS)
    res['files_in_certs'] = len(files)
    res['unreferenced_files'] = sorted(f for f in files if f.split('.')[0] not in referenced)
    res['duplicate_files'] = sorted(f for f in files if files.count(f.split('.')[0] + '.txt') +
                                    files.count(f.split('.')[0] + '.txt.gz') > 1)
    json.dump(res, open(os.path.join(RUN, 'logs', 'f4', 'check.json'), 'w'), indent=1)
    print(json.dumps({k: (v if not isinstance(v, list) else len(v)) for k, v in res.items()}))


if __name__ == '__main__':
    main()
