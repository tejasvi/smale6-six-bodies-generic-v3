#!/usr/bin/env python3
"""Referee re-certification of every distinct stored core (per class), with two systems:
  (S) Singular 4.4, exactly tcert's method: ring (0,m0..m5), iterated sat by every variable and every difference of two
      coordinates of one node, std, dim = -1;
  (M) Macaulay2, independently: coefficient field frac(QQ[m0..m5]), Rabinowitsch variable t with
      t * (product of the same saturating polynomials) - 1, Groebner basis, test 1 in the ideal.
Both say 'unit ideal over Q(m)' iff the core has no solution with all saturating factors nonzero at generic masses.
Usage: recert.py EXACT_COLLECT_DIR OUT.jsonl [--jobs J] [--timeout S] [--only-certified]"""
import glob, hashlib, json, os, re, subprocess, sys, tempfile
import multiprocessing as mp

VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')
root, outp = sys.argv[1], sys.argv[2]
jobs = int(sys.argv[sys.argv.index('--jobs') + 1]) if '--jobs' in sys.argv else 32
tmo = int(sys.argv[sys.argv.index('--timeout') + 1]) if '--timeout' in sys.argv else 900
only_cert = '--only-certified' in sys.argv
work = os.path.join(os.path.dirname(os.path.abspath(outp)), 'recert_tmp')
os.makedirs(work, exist_ok=True)


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
    return [f(e) for e in eqs], sorted(set(f(s) for s in sats)), len(order)


def collect():
    items = {}
    for d in sorted(glob.glob(os.path.join(root, '*', 'exact6', 'c*'))):
        c = int(os.path.basename(d)[1:])
        cert = {}
        if os.path.exists(d + '/cert.jsonl'):
            for l in open(d + '/cert.jsonl'):
                r = json.loads(l)
                cert[r['hash']] = r['dim_Qm']
        for f in sorted(glob.glob(d + '/sec/p*.cores.jsonl')):
            for l in open(f):
                r = json.loads(l)
                if not r.get('verified_modp'):
                    continue
                eqs = r['core_sym']
                ceqs, csats, nv = canon(eqs, sats_of(eqs))
                h = hashlib.sha1('\n'.join(ceqs).encode()).hexdigest()[:16]
                key = (c, h)
                if key not in items:
                    items[key] = {'class': c, 'hash': h, 'ceqs': ceqs, 'csats': csats, 'nv': nv,
                                  'stored_dim': cert.get(h), 'count': 0}
                items[key]['count'] += 1
    return list(items.values())


def run(cmd, path, timeout):
    try:
        out = subprocess.run(cmd + [path], capture_output=True, text=True, timeout=timeout)
        return out.stdout + out.stderr
    except subprocess.TimeoutExpired:
        return 'TIMEOUT'


def singular(it):
    vs = [f'v{i}' for i in range(it['nv'])]
    s = [f'ring R = (0,m0,m1,m2,m3,m4,m5), ({",".join(vs)}), dp;', f'ideal I = {",".join(it["ceqs"])};']
    s += [f'I = sat(I, ideal({f}));' for f in it['csats']]
    s += ['ideal G = std(I);', 'print("DIM " + string(dim(G)));', 'quit;']
    fd, path = tempfile.mkstemp(suffix='.sing', dir=work)
    with os.fdopen(fd, 'w') as fh:
        fh.write('\n'.join(s) + '\n')
    out = run(['nice', '-n', '10', 'Singular', '-q'], path, tmo)
    os.unlink(path)
    m = re.search(r'DIM (-?\d+)', out)
    return int(m.group(1)) if m else ('timeout' if out == 'TIMEOUT' else 'error')


def m2(it):
    vs = [f'v{i}' for i in range(it['nv'])]
    prod = '*'.join(it['csats']) if it['csats'] else '1'
    s = ['K = frac(QQ[m0,m1,m2,m3,m4,m5]);', f'R = K[{",".join(vs + ["tRab"])}];',
         f'I = ideal({",".join(it["ceqs"])});', f'J = I + ideal(tRab*{prod}-1);', 'G = gb J;',
         'print(if (1_R % J) == 0 then "UNIT" else "NOTUNIT");', 'exit 0;']
    fd, path = tempfile.mkstemp(suffix='.m2', dir=work)
    with os.fdopen(fd, 'w') as fh:
        fh.write('\n'.join(s) + '\n')
    out = run(['nice', '-n', '10', 'M2', '--script'], path, tmo)
    os.unlink(path)
    if 'NOTUNIT' in out:
        return 'notunit'
    if 'UNIT' in out:
        return 'unit'
    return 'timeout' if out == 'TIMEOUT' else 'error: ' + out[-300:]


def both(it):
    it = dict(it)
    it['singular_dim'] = singular(it)
    it['m2'] = m2(it)
    return it


if __name__ == '__main__':
    mp.set_start_method('fork', force=True)
    items = collect()
    if only_cert:
        items = [it for it in items if it['stored_dim'] == -1]
    print(len(items), 'distinct (class, core) items', flush=True)
    done = set()
    if os.path.exists(outp):
        for l in open(outp):
            r = json.loads(l)
            done.add((r['class'], r['hash']))
    items = [it for it in items if (it['class'], it['hash']) not in done]
    items.sort(key=lambda it: -it['count'])
    with open(outp, 'a') as f, mp.Pool(jobs) as pool:
        for r in pool.imap_unordered(both, items):
            f.write(json.dumps(r) + '\n')
            f.flush()
    print('recert done', flush=True)
