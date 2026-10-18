#!/usr/bin/env python3
"""In-situ check of the residual lemmas: for each residual cell and each applicable lemma, the relations the lemma
uses, written in the cell's own leading coefficients (tinit.py conventions: X{v}_{i}, Y{v}_{i}, D{k}_{l}; child 0 of
every node at coordinate 0), are inconsistent at random masses mod p (Singular std after saturation by the
leading coefficients that the lemma assumes nonzero: separations and positions, all nonzero by the place lemma).
Usage: insitu_resid.py [--prime P] [--seeds K]   -> ../data/insitu_resid.log"""
import json, os, random, subprocess, sys, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rkit as R

N, O = 6, 6


def parents(tr):
    par = {}
    for a, ch in tr['children'].items():
        for c in ch:
            par[c] = int(a)
    return par


def meet(tr, p, q):
    par = parents(tr)
    lp, lq = tr['leaf'][str(p)], tr['leaf'][str(q)]
    if lp == lq:
        return None
    anc = [lp]
    while anc[-1] in par:
        anc.append(par[anc[-1]])
    u, sa = lq, set(anc)
    while u not in sa:
        u = par[u]
    return u


def child_index(tr, v, leaf):
    par = parents(tr)
    u = leaf
    while u in par and par[u] != v:
        u = par[u]
    assert par.get(u) == v
    return tr['children'][str(v)].index(u)


def coord(tag, v, i):
    return '0' if i == 0 else f'{tag}{v}_{i}'


def lead(tr, tag, p, q):
    v = meet(tr, p, q)
    if v is None:
        return None
    cp = child_index(tr, v, tr['leaf'][str(p)])
    cq = child_index(tr, v, tr['leaf'][str(q)])
    return f'({coord(tag, v, cp)}-{coord(tag, v, cq)})'


class Sys:
    def __init__(self, rec, masses):
        self.rec = rec
        self.zt, self.wt = rec['ztree'], rec['wtree']
        self.m = {k: f'({masses[k]})' for k in range(N)}
        self.vars = []
        for tag, tr in (('X', self.zt), ('Y', self.wt)):
            for v, ch in tr['children'].items():
                for i in range(1, len(ch)):
                    self.vars.append(f'{tag}{v}_{i}')
        self.vars += [f'D{k}_{l}' for k, l in itertools.combinations(range(N), 2)]
        self.eqs, self.sats = [], set()
        self.argmin = {}
        for nm, labs in rec['argmin']:
            key = (nm[0], nm[1], tuple(nm[2])) if nm[0] in ('z', 'w') else tuple(nm)
            self.argmin[key] = labs

    def tr(self, col):
        return (self.zt, 'X') if col == 'z' else (self.wt, 'Y')

    def L(self, col, p, q):
        tr, tag = self.tr(col)
        return lead(tr, tag, p, q)

    def Dv(self, k, l):
        return f'D{min(k, l)}_{max(k, l)}'

    def add_D(self, k, l):
        self.eqs.append(f'{self.Dv(k, l)}^2*{self.L("z", k, l)}*{self.L("w", k, l)}-1')
        self.sats.add(self.L('z', k, l))
        self.sats.add(self.L('w', k, l))

    def add_body(self, col, k):
        """initial form of body k's col-equation on the cell (from the argmin data), as tinit writes it."""
        labs = self.argmin[(col, 'S', (k,))]
        terms = []
        for lab in labs:
            if lab[0] == 'pos':
                terms.append(f'{self.m[k]}*{self.L(col, k, O)}')
                self.sats.add(self.L(col, k, O))
            else:
                i, j = lab[1], lab[2]
                terms.append(f'-{self.m[i]}*{self.m[j]}*{self.Dv(i, j)}^3*{self.L(col, i, j)}')
                self.sats.add(self.L(col, i, j))
        self.eqs.append('+'.join(terms).replace('+-', '-'))

    def add_pos_relation(self, col, bodies):
        """sum_k m_k * (leading coefficient of the position of k), the initial form of a centre relation."""
        terms = [f'{self.m[k]}*{self.L(col, k, O)}' for k in bodies]
        for k in bodies:
            self.sats.add(self.L(col, k, O))
        self.eqs.append('+'.join(terms))

    def add_torque(self, labels):
        """initial form of a torque: labels ('zw', p, q) = delta_pq^3 z_p w_q, with the sign of T_J (J side first);
        signs are irrelevant for the zero set only up to the J orientation, so we pass (sign, p, q)."""
        terms = []
        for sg, p, q in labels:
            terms.append(f'{"-" if sg < 0 else ""}{self.m[p]}*{self.m[q]}*{self.Dv(p, q)}^3*{self.L("z", p, O)}*{self.L("w", q, O)}')
            self.sats.add(self.L('z', p, O))
            self.sats.add(self.L('w', q, O))
        self.eqs.append('+'.join(terms).replace('+-', '-'))

    def add_sat(self, col, p, q):
        x = self.L(col, p, q)
        if x is not None:
            self.sats.add(x)

    def singular(self, idx, prime):
        s = [f'ring R{idx} = {prime}, ({",".join(self.vars)}), dp;', 'option(redSB);',
             f'ideal I = {",".join(self.eqs)};']
        for f in sorted(x for x in self.sats if x is not None):
            s.append(f"I = sat(I, ideal({f}));")
        s.append('ideal G = std(I);')
        s.append(f'print("CELL {idx} " + string(dim(G)) + " " + string(size(G)) + " " + string(G[1]));')
        s.append(f'kill R{idx};')
        return '\n'.join(s)


def build(rec, lemma, w, masses):
    S = Sys(rec, masses)
    if lemma == 'B0':
        k, l, cp, c = w['k'], w['l'], w['colour_origin'], w['colour_contra']
        S.add_D(k, l)
        S.add_body(cp, l)
        S.add_body(c, l)
        S.add_sat(c, k, O)
    elif lemma == 'K':
        k, l = w['pair']
        S.add_D(k, l)
        for col in 'zw':
            S.add_body(col, k)
            S.add_body(col, l)
        j, q = w['j'], w['extra_on']
        S.add_D(q, j)
    elif lemma == 'L':
        a, b, s, c = w['a'], w['b'], w['s'], w['cc_colour']
        for p, q in ((a, b), (b, s), (a, s)):
            S.add_D(p, q)
        for col in 'zw':
            for k in (a, b, s):
                S.add_body(col, k)
    elif lemma == 'R1*':
        a, b, s, c = w['a'], w['b'], w['s'], w['colour']
        for p, q in ((a, b), (b, s), (a, s)):
            S.add_D(p, q)
        S.add_body(c, a)
        S.add_body(c, b)
        if w['centre'] in ('full', 'full-minus-S'):
            # full centre of mass: the bodies whose c-position has least exponent (non-O children of the root)
            S.add_pos_relation(c, root_bodies(rec, c))
            for K in w.get('S_sets', []):
                for k in K:
                    S.add_body(c, k)
        elif w['centre'] == 'S':
            for K in w['S_sets']:
                for k in K:
                    S.add_body(c, k)
        else:   # subset sum: initial form = positions of MA + MB
            S.add_pos_relation(c, w['MA'] + w['MB'])
    elif lemma == 'W3':
        tri, c = w['tri'], w['colour']
        for p, q in itertools.combinations(tri, 2):
            S.add_D(p, q)
        for k in w['balanced'][:2]:
            S.add_body(c, k)
        for rel in w['relations']:
            if rel[0] == 'full':
                S.add_pos_relation(c, root_bodies(rec, c))
            else:
                for bs in rel[1].values():
                    for k in bs:
                        S.add_body(c, k)
    elif lemma == 'EQ2':
        a, b, s, c = w['a'], w['b'], w['s'], w['colour']
        cb = 'w' if c == 'z' else 'z'
        S.add_D(s, a)
        S.add_D(s, b)
        S.add_D(a, b)
        S.add_body(c, s)
        S.add_body(c, a)
        S.add_body(cb, a)
        S.add_pos_relation(c, root_bodies(rec, c))
    elif lemma == 'TQ':
        l1, l2 = w['l']
        k1, k2 = w['k']
        c = w['colour']
        cb = 'w' if c == 'z' else 'z'
        for l in (l1, l2):
            for k in (k1, k2):
                S.add_D(l, k)
        S.add_pos_relation(c, root_bodies(rec, c))
        S.add_body(cb, k1)
        S.add_body(cb, k2)
        if c == 'z':
            S.add_torque([(1, l, k) for l in (l1, l2) for k in (k1, k2)])
        else:
            S.add_torque([(1, k, l) for l in (l1, l2) for k in (k1, k2)])
    else:
        return None
    return S


def root_bodies(rec, col):
    tr = rec['ztree'] if col == 'z' else rec['wtree']
    root = tr['root']
    out = []
    for k in range(N):
        if meet(tr, k, O) == root:
            out.append(k)
    return out


def run_batch(blocks, workdir):
    path = os.path.join(workdir, 'insitu_tmp.sing')
    with open(path, 'w') as f:
        f.write('LIB "elim.lib";\n' + '\n'.join(blocks) + '\nquit;\n')
    out = subprocess.run(['Singular', '-q', path], capture_output=True, text=True)
    os.unlink(path)
    res = {}
    for line in out.stdout.splitlines():
        if line.startswith('CELL '):
            parts = line.split()
            res[int(parts[1])] = (int(parts[2]), parts[4])
    if out.returncode != 0:
        sys.stderr.write(out.stderr[-3000:])
    return res


def main():
    prime = int(sys.argv[sys.argv.index('--prime') + 1]) if '--prime' in sys.argv else 32003
    seeds = int(sys.argv[sys.argv.index('--seeds') + 1]) if '--seeds' in sys.argv else 2
    work = os.path.join(R.DATA, 'work')
    os.makedirs(work, exist_ok=True)
    cover = [json.loads(l) for l in open(os.path.join(R.DATA, 'resid_cover.jsonl'))]
    jobs = []
    for r in cover:
        rec = R.load_cell(r['class'], r['cell'])
        for lem, w in r['witness'].items():
            if lem == 'TD':
                continue
            for sd in range(seeds):
                rng = random.Random(1000 * r['class'] + r['cell'] + 7919 * sd)
                masses = [rng.randrange(2, prime - 1) for _ in range(N)]
                S = build(rec, lem, w, masses)
                if S is not None:
                    jobs.append(((r['class'], r['cell'], lem, sd), S))
    log = open(os.path.join(R.DATA, 'insitu_resid.log'), 'w')
    bad = 0
    B = 40
    for b0 in range(0, len(jobs), B):
        chunk = jobs[b0:b0 + B]
        blocks = [S.singular(i, prime) for i, (_, S) in enumerate(chunk)]
        res = run_batch(blocks, work)
        for i, (key, S) in enumerate(chunk):
            d = res.get(i)
            ok = d is not None and d[0] == -1
            bad += not ok
            log.write(f'{key} dim={d} {"OK" if ok else "FAIL"}\n')
            if not ok:
                print('FAIL', key, d, flush=True)
    log.write(f'jobs {len(jobs)} failures {bad}\n')
    print('jobs', len(jobs), 'failures', bad)


if __name__ == '__main__':
    main()
