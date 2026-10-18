#!/usr/bin/env python3
"""Certify cores over Q(m): the core's equations with the random masses replaced by symbols m0..m(n-1) (ring
parameters), saturated by the position factors and E that involve its variables; certified if the saturated ideal is
the unit ideal over Q(m) (generic exclusion in characteristic 0). Cores are canonicalized (variables renamed in order
of appearance) and each distinct core is computed once.
Usage: tcert.py N MASSES(comma list, as used by tsec) OUT.jsonl CORES.jsonl [CORES.jsonl ...]"""
import json, re, sys, os, hashlib, subprocess, tempfile

n = masses = outp = files = workdir = None
VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')


def symbolic(e):
    for k, mv in enumerate(masses):
        e = e.replace(f'({mv})', f'(m{k})')
    return e


def canon(eqs, sats):
    order = []
    for e in eqs:
        for v in VAR.findall(e):
            if v not in order:
                order.append(v)
    ren = {v: f'v{i}' for i, v in enumerate(order)}
    f = lambda e: VAR.sub(lambda mm: ren[mm.group(0)], e)
    ceqs = [f(e) for e in eqs]
    csats = sorted(set(f(s) for s in sats if VAR.findall(s) and all(v in ren for v in VAR.findall(s))))
    return order, ceqs, csats


def singular_q(vars_, eqs, sats, workdir, nb, timeout=600):
    par = ','.join(f'm{k}' for k in range(nb))
    s = [f'ring R = (0,{par}), ({",".join(vars_)}), dp;', f'ideal I = {",".join(eqs)};']
    for f in sats:
        s.append(f'I = sat(I, ideal({f}));')
    s += ['ideal G = std(I);', 'print("DIM " + string(dim(G)));', 'quit;']
    fd, path = tempfile.mkstemp(suffix='.sing', dir=workdir)
    with os.fdopen(fd, 'w') as fh:
        fh.write('\n'.join(s) + '\n')
    try:
        out = subprocess.run(['Singular', '-q', path], capture_output=True, text=True, timeout=timeout)
        txt = out.stdout
    except subprocess.TimeoutExpired:
        txt = ''
    os.unlink(path)
    for line in txt.splitlines():
        if line.startswith('DIM '):
            return int(line.split()[1])
    return None




def work(item):
    """One distinct core: (hash, record, workdir, number of bodies) -> (hash, dim over Q(m))."""
    h, d, wd, nb = item
    return h, singular_q(d['vars'], d['ceqs'], d['csats'], wd, nb)


def main():
    global n, masses, outp, files, workdir
    n = int(sys.argv[1])
    masses = sys.argv[2].split(',')
    outp = sys.argv[3]
    files = sys.argv[4:]
    workdir = os.path.dirname(os.path.abspath(outp))
    seen = {}
    n_cores = 0
    for fn in files:
        for line in open(fn):
            if not line.strip():
                continue
            r = json.loads(line)
            n_cores += 1
            eqs = r['core_sym'] if 'core_sym' in r else [symbolic(e) for e in r['core']]
            sats = []
            # positions and E: recover them from the variables used (the sats were not stored; rebuild the generic list)
            # every node coordinate is a nonzero separation or position, as are the differences of coordinates of one node;
            # delta and E are nonzero: all may be saturated
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
            key_vars, ceqs, csats = canon(eqs, sats)
            h = hashlib.sha1(('\n'.join(ceqs) + '\n#sat\n' + '\n'.join(csats)).encode()).hexdigest()[:16]
            seen.setdefault(h, {'ceqs': ceqs, 'csats': csats, 'vars': [f'v{i}' for i in range(len(key_vars))], 'count': 0, 'example': (fn, r['cell'], r['names'])})
            seen[h]['count'] += 1
    print(f'{n_cores} cores, {len(seen)} distinct', flush=True)
    jobs = int(os.environ.get('TCERT_JOBS', str(min(os.cpu_count() or 1, 380))))
    items = [(h, d, workdir, n) for h, d in sorted(seen.items(), key=lambda t: -t[1]['count'])]
    with open(outp, 'w') as f:
        if jobs > 1:
            from multiprocessing import Pool
            with Pool(jobs) as pool:
                for h, dim in pool.imap_unordered(work, items):
                    d = seen[h]
                    f.write(json.dumps({'hash': h, 'count': d['count'], 'dim_Qm': dim, 'eqs': d['ceqs'], 'example': d['example']}) + '\n')
                    f.flush()
        else:
            for item in items:
                h, dim = work(item)
                d = seen[h]
                f.write(json.dumps({'hash': h, 'count': d['count'], 'dim_Qm': dim, 'eqs': d['ceqs'], 'example': d['example']}) + '\n')
                f.flush()
                print(h, d['count'], dim, d['example'][2], flush=True)



if __name__ == '__main__':
    main()
