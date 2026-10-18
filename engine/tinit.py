#!/usr/bin/env python3
"""Initial systems of the exact cells (texact.py) and their consistency at random masses (Singular, char p).

For a cell, the leading coefficients: node coordinates X_v_i of the z-tree (child i of node v; child 0 at 0), Y_v_i of
the w-tree, D_k_l of delta_kl, and E. The leading coefficient of z_pq is X_v[c(p)] - X_v[c(q)] at v = meet(p, q);
of z_k it is that of z_kO. The equations: the initial forms of the identities of texact.py on the cell's argmin sets,
and D^2 z w = 1 on every pair. Saturation by the leading coefficients of the positions (which must be nonzero unless
the body sits at O) and by E. A cell is excluded at the masses if the saturated ideal is the unit ideal.
Usage: tinit.py N CLASSES_JSON IDX CELLS.jsonl OUT.jsonl [--prime P] [--seed S] [--batch B]"""
import json, random, subprocess, sys, os, itertools, tempfile

def child_index(tr, v, leaf):
    """Index of the child of v whose subtree contains the leaf."""
    u = leaf
    par = {}
    for a, ch in tr['children'].items():
        for c in ch:
            par[c] = int(a)
    while u in par and par[u] != v:
        u = par[u]
    assert par.get(u) == v, (v, leaf)
    return tr['children'][str(v)].index(u)


def meet(tr, p, q):
    par = {}
    for a, ch in tr['children'].items():
        for c in ch:
            par[c] = int(a)
    lp, lq = tr['leaf'][str(p)], tr['leaf'][str(q)]
    if lp == lq:
        return None
    anc = [lp]
    while anc[-1] in par:
        anc.append(par[anc[-1]])
    u = lq
    sa = set(anc)
    while u not in sa:
        u = par[u]
    return u


def coord(tag, v, i):
    return '0' if i == 0 else f'{tag}{v}_{i}'


def lead(tr, tag, p, q):
    """Leading coefficient of z_pq (or w_pq) as a Singular expression; None if identically zero."""
    v = meet(tr, p, q)
    if v is None:
        return None
    cp = child_index(tr, v, tr['leaf'][str(p)])
    cq = child_index(tr, v, tr['leaf'][str(q)])
    return f'({coord(tag, v, cp)}-{coord(tag, v, cq)})'


def system(n, cell, masses):
    zt, wt = cell['ztree'], cell['wtree']
    vars_ = []
    for tag, tr in (('X', zt), ('Y', wt)):
        for v, ch in tr['children'].items():
            for i in range(1, len(ch)):
                vars_.append(f'{tag}{v}_{i}')
    pairs = list(itertools.combinations(range(n), 2))
    vars_ += [f'D{k}_{l}' for k, l in pairs] + ['E']
    m = {k: f'({masses[k]})' for k in range(n)}
    M = '(' + '+'.join(f'({x})' for x in masses) + ')'
    eqs = []
    for k, l in pairs:
        eqs.append(f'D{k}_{l}^2*{lead(zt, "X", k, l)}*{lead(wt, "Y", k, l)}-1')
    for name, labels in cell['argmin']:
        terms = []
        if name[0] in ('z', 'w'):
            tr, tag = (zt, 'X') if name[0] == 'z' else (wt, 'Y')
            for lab in labels:
                if lab[0] == 'pos':
                    i = lab[1]
                    terms.append(f'{m[i]}*{lead(tr, tag, i, n)}')
                else:
                    i, j = lab[1], lab[2]
                    a, b = min(i, j), max(i, j)
                    terms.append(f'-{m[i]}*{m[j]}*D{a}_{b}^3*{lead(tr, tag, i, j)}')
        elif name[0] == 'U':
            for lab in labels:
                terms.append('-E' if lab[0] == 'E' else f'{m[lab[1]]}*{m[lab[2]]}*D{lab[1]}_{lab[2]}')
        elif name[0] == 'I':
            for lab in labels:
                terms.append(f'-{M}*E' if lab[0] == 'E' else
                             f'{m[lab[1]]}*{m[lab[2]]}*{lead(zt, "X", lab[1], lab[2])}*{lead(wt, "Y", lab[1], lab[2])}')
        elif name[0] == 'Ip':
            for lab in labels:
                terms.append('-E' if lab[0] == 'E' else
                             f'{m[lab[1]]}*{lead(zt, "X", lab[1], n)}*{lead(wt, "Y", lab[1], n)}')
        eqs.append('+'.join(terms).replace('+-', '-'))
    sats = ['E']
    for k in range(n):
        for tr, tag in ((zt, 'X'), (wt, 'Y')):
            e = lead(tr, tag, k, n)
            if e is not None:
                sats.append(e)
    return vars_, eqs, sats


def singular_block(idx, vars_, eqs, sats, prime):
    s = [f'ring R{idx} = {prime}, ({",".join(vars_)}), dp;', 'option(redSB);', f'ideal I = {",".join(eqs)};']
    for f in sats:
        s.append(f'I = sat(I, ideal({f}));')
    s.append('ideal G = std(I);')
    s.append(f'print("CELL {idx} " + string(dim(G)));')
    s.append(f'kill R{idx};')
    return '\n'.join(s)


def run_batch(blocks, workdir, timeout=None):
    fd, path = tempfile.mkstemp(suffix='.sing', dir=workdir)
    with os.fdopen(fd, 'w') as f:
        f.write('\n'.join(blocks) + '\nquit;\n')
    try:
        out = subprocess.run(['Singular', '-q', path], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        os.unlink(path)
        return {}
    os.unlink(path)
    res = {}
    for line in out.stdout.splitlines():
        if line.startswith('CELL '):
            _, i, d = line.split()
            res[int(i)] = int(d)
    if out.returncode != 0 or not res:
        sys.stderr.write(out.stderr[-2000:])
    return res


if __name__ == '__main__':
    n = int(sys.argv[1])
    cells_path, out_path = sys.argv[4], sys.argv[5]
    prime = int(sys.argv[sys.argv.index('--prime') + 1]) if '--prime' in sys.argv else 32003
    seed = int(sys.argv[sys.argv.index('--seed') + 1]) if '--seed' in sys.argv else 1
    batch = int(sys.argv[sys.argv.index('--batch') + 1]) if '--batch' in sys.argv else 40
    rng = random.Random(seed)
    masses = [rng.randrange(2, prime - 1) for _ in range(n)]
    if '--masses' in sys.argv:
        masses = sys.argv[sys.argv.index('--masses') + 1].split(',')
    cells = [json.loads(l) for l in open(cells_path)]
    workdir = os.path.dirname(os.path.abspath(out_path))
    results = {}
    for b0 in range(0, len(cells), batch):
        blocks = []
        for i in range(b0, min(len(cells), b0 + batch)):
            v, e, s = system(n, cells[i], masses)
            blocks.append(singular_block(i, v, e, s, prime))
        results.update(run_batch(blocks, workdir))
    with open(out_path, 'w') as f:
        for i, c in enumerate(cells):
            f.write(json.dumps({'cell': i, 'dim': results.get(i), 'sumx': c['sumx'], 'x': c['x']}) + '\n')
    dims = [results.get(i) for i in range(len(cells))]
    from collections import Counter
    print(json.dumps({'cells': len(cells), 'masses': masses, 'prime': prime, 'dims': dict(Counter(dims))}))
