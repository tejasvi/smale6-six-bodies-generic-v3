#!/usr/bin/env python3
"""Certified covering of w-space for Lemma 6.19(a) (iii), (iv): a depth-first partition of R^17 into relatively open
polyhedral cells {w : E w = 0, S w > 0}, refined by the argmin faces of the polynomials of Gbar (G at mu0 mod p), with
a certificate at every leaf. The tree is written in prefix order as tokens (see `emit`); the Lean checker
`Lean6.Special.Comp.D88.Trop.Check` verifies it.

Node kinds:
  E  empty cell: integers u, y with sum_i u_i E_i + sum_j y_j S_j = 0, y >= 0, y != 0;
  S  split along h = e_i - e_j (exponents i, j of polynomial g): children <h,w> > 0, < 0, = 0;
  F  the argmin face of g is the set F on the whole cell: k (e_f - e_a0) = E^T u for f in F (k > 0), and for every
     other exponent b: z (e_b - e_a0) = S^T y + E^T u with z > 0, y >= 0, y != 0; the face is pushed on the list of
     established faces;
  M  the last established face has one monomial (outside trop g);
  L  the initial forms of the established faces have no zero in the torus over F_p: cofactors c_i (polynomials over
     F_p in x_0..x_16 and x_17 = y) with sum_i c_i in_i + c_R (1 - y x_0 ... x_16) = 1;
  N  the cell is {0}: k e_i = E^T u for every i (k > 0).
Usage: dfs.py n4|kc OUTDIR [checkpoints]
"""
import json
import math
import os
import re
import subprocess
import sys
import time
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lpcert as L

P = 65521
NV = 17


# ------------------------------------------------------------------ exact helpers
def solve_rowspan(E, r):
    """u (Fractions) with sum_i u_i E_i = r, or None."""
    m = len(E)
    if m == 0:
        return [] if all(x == 0 for x in r) else None
    # 17 equations in m unknowns: rows = coordinates
    M = [[Fr(E[i][c]) for i in range(m)] + [Fr(r[c])] for c in range(NV)]
    piv = []
    row = 0
    for col in range(m):
        pr = next((i for i in range(row, NV) if M[i][col] != 0), None)
        if pr is None:
            continue
        M[row], M[pr] = M[pr], M[row]
        pv = M[row][col]
        M[row] = [x / pv for x in M[row]]
        for i in range(NV):
            if i != row and M[i][col] != 0:
                f = M[i][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[row])]
        piv.append(col)
        row += 1
    if any(M[i][m] != 0 for i in range(row, NV)):
        return None
    u = [Fr(0)] * m
    for i, col in enumerate(piv):
        u[col] = M[i][m]
    return u


def integerize(*parts):
    """scale the Fraction vectors jointly to coprime integers; returns the integer vectors."""
    den = 1
    for v in parts:
        for x in v:
            den = den * Fr(x).denominator // math.gcd(den, Fr(x).denominator)
    ints = [[int(Fr(x) * den) for x in v] for v in parts]
    g = 0
    for v in ints:
        for x in v:
            g = math.gcd(g, abs(x))
    g = g or 1
    return [[x // g for x in v] for v in ints]


def sparse(v):
    nz = [(i, x) for i, x in enumerate(v) if x != 0]
    return [len(nz)] + [t for ix in nz for t in ix]


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


class Cell:
    __slots__ = ('E', 'S', 'basis', 'w')

    def __init__(self, E, S, basis, w):
        self.E, self.S, self.basis, self.w = E, S, basis, w


def basis_of(E):
    return L.nullspace([list(e) for e in E], NV) if E else [[1 if i == j else 0 for i in range(NV)] for j in range(NV)]


def try_cell(E, S):
    """('cell', Cell) with an exact interior point, or ('empty', tokens of the certificate)."""
    basis = basis_of(E)
    d = len(basis)
    A = [L.proj(s, basis) for s in S]
    kind, val = L.feasible_cert(A, [], d)
    if kind == 'point':
        t = val
        w = [sum(Fr(t[j]) * basis[j][i] for j in range(d)) for i in range(NV)] if d else [Fr(0)] * NV
        den = 1
        for x in w:
            den = den * x.denominator // math.gcd(den, x.denominator)
        w = [int(x * den) for x in w]
        assert all(L.dot(e, w) == 0 for e in E) and all(L.dot(s, w) > 0 for s in S)
        return 'cell', Cell(E, S, basis, w)
    y, _ = val
    r = [sum(Fr(y[j]) * S[j][i] for j in range(len(S))) for i in range(NV)]
    u = solve_rowspan(E, [-x for x in r])
    assert u is not None
    ui, yi = integerize(u, y)
    assert all(x >= 0 for x in yi) and any(x > 0 for x in yi)
    for i in range(NV):
        assert sum(ui[a] * E[a][i] for a in range(len(E))) + sum(yi[b] * S[b][i] for b in range(len(S))) == 0
    return 'empty', ['E'] + sparse(ui) + sparse(yi)


# ------------------------------------------------------------------ the tree
class Tree:
    def __init__(self, G):
        self.G = G                  # list of lists of (coeff mod p, exponent tuple)
        self.nodes = {}             # id -> list of tokens with child references ('@', id)
        self.next = 0
        self.pending = []           # (id, cell, faces)

    def new(self):
        i = self.next
        self.next += 1
        return i

    def refine(self, nid, cell, faces, g):
        """refine the pending node nid by polynomial g; new pending nodes go to out."""
        supp = [t[1] for t in self.G[g]]
        out = []
        stack = [(nid, cell)]
        while stack:
            nid, c = stack.pop()
            d = len(c.basis)
            if d == 0 and not c.S:
                self.nodes[nid] = self.nonneg(c)
                continue
            vals = [L.dot(a, c.w) for a in supp]
            mn = min(vals)
            F = [i for i, v in enumerate(vals) if v == mn]
            a0 = supp[F[0]]
            split = None
            for i in F[1:]:
                h = sub(supp[i], a0)
                if any(v != 0 for v in L.proj(h, c.basis)):
                    split = (i, F[0])
                    break
            strict = []
            if split is None:
                Aproj = [L.proj(s, c.basis) for s in c.S]
                for i in range(len(supp)):
                    if i in F:
                        continue
                    h = sub(supp[i], a0)
                    hp = L.proj(h, c.basis)
                    assert any(v != 0 for v in hp)
                    kind, val = L.feasible_cert(Aproj, [[-v for v in hp]], d)
                    if kind == 'point':
                        split = (i, F[0])
                        break
                    y, z = val
                    zh = z[0]
                    assert zh > 0
                    r = [sum(Fr(y[j]) * c.S[j][k] for j in range(len(c.S))) - zh * h[k] for k in range(NV)]
                    u = solve_rowspan(c.E, [-x for x in r])
                    assert u is not None
                    zi, yi, ui = integerize([zh], y, u)
                    assert zi[0] > 0 and all(x >= 0 for x in yi) and any(x > 0 for x in yi)
                    for k in range(NV):
                        assert zi[0] * h[k] == sum(yi[j] * c.S[j][k] for j in range(len(c.S))) + \
                            sum(ui[a] * c.E[a][k] for a in range(len(c.E)))
                    strict.append([zi[0]] + sparse(yi) + sparse(ui))
            if split is not None:
                i, j = split
                h = sub(supp[i], supp[j])
                kids = []
                for (E2, S2) in ((c.E, c.S + [h]), (c.E, c.S + [neg(h)]), (c.E + [h], c.S)):
                    kind, val = try_cell(E2, S2)
                    if kind == 'empty':
                        kid = self.new()
                        self.nodes[kid] = val
                    else:
                        kid = self.new()
                        stack.append((kid, val))
                    kids.append(kid)
                self.nodes[nid] = ['S', g, i, j] + [('@', k) for k in kids]
                continue
            eqc = []
            for i in F[1:]:
                h = sub(supp[i], a0)
                u = solve_rowspan(c.E, list(h))
                assert u is not None
                kk, u_ = integerize([Fr(1)], u)
                kk = kk[0]
                assert kk > 0
                for k in range(NV):
                    assert kk * h[k] == sum(u_[a] * c.E[a][k] for a in range(len(c.E)))
                eqc.append([kk] + sparse(u_))
            kid = self.new()
            toks = ['F', g, len(F)] + F
            for e in eqc:
                toks += e
            for s in strict:
                toks += s
            toks.append(('@', kid))
            self.nodes[nid] = toks
            nf = faces + [(g, tuple(F))]
            if len(F) == 1:
                self.nodes[kid] = ['M']
            else:
                out.append((kid, c, nf))
        return out

    def nonneg(self, c):
        toks = ['N']
        for i in range(NV):
            e = [1 if k == i else 0 for k in range(NV)]
            u = solve_rowspan(c.E, e)
            assert u is not None
            kk, u_ = integerize([Fr(1)], u)
            kk = kk[0]
            assert kk > 0
            for k in range(NV):
                assert sum(u_[a] * c.E[a][k] for a in range(len(c.E))) == (kk if k == i else 0)
            toks += [kk] + sparse(u_)
        return toks

    def emit(self, root):
        out = []
        stack = [root]
        while stack:
            nid = stack.pop()
            toks = self.nodes[nid]
            kids = []
            for t in toks:
                if isinstance(t, tuple):
                    kids.append(t[1])
                else:
                    out.append(str(t))
            for k in reversed(kids):
                stack.append(k)
        return out


# ------------------------------------------------------------------ torus tests (Singular)
VARS = ','.join('x(%d)' % i for i in range(NV)) + ',yy'


def poly_sing(terms):
    s = []
    for c, e in terms:
        mon = '*'.join(('x(%d)^%d' % (i, k) if k > 1 else 'x(%d)' % i) for i, k in enumerate(e) if k > 0)
        s.append('%d%s' % (c, ('*' + mon) if mon else ''))
    return '+'.join(s) if s else '0'


TERM = re.compile(r'([+-]?)([^+-]+)')


def parse_sing_poly(s):
    """Singular's output in characteristic p: terms c*x(i)^e*...*yy^e; returns list of (c mod p, exps[18])."""
    s = s.replace(' ', '')
    if s == '0':
        return []
    out = []
    for sg, body in TERM.findall(s):
        c = 1
        e = [0] * (NV + 1)
        for f in body.split('*'):
            m = re.fullmatch(r'x\((\d+)\)(\^(\d+))?', f)
            if m:
                e[int(m.group(1))] += int(m.group(3) or 1)
                continue
            m = re.fullmatch(r'yy(\^(\d+))?', f)
            if m:
                e[NV] += int(m.group(2) or 1)
                continue
            assert re.fullmatch(r'\d+', f), (f, s[:80])
            c *= int(f)
        if sg == '-':
            c = -c
        out.append((c % P, tuple(e)))
    return out


SING_HDR = 'ring r = %d,(%s),dp;\noption(redSB);\npoly tt = %s;\n' % (P, VARS, '*'.join('x(%d)' % i for i in range(NV)))
SING_HDR0 = 'ring r = %d,(%s),dp;\noption(redSB);\n' % (P, ','.join('x(%d)' % i for i in range(NV)))


def _sing(script, timeout):
    import tempfile
    fd, path = tempfile.mkstemp(suffix='.sing', prefix='d88trop_')
    os.close(fd)
    open(path, 'w').write(script)
    try:
        r = subprocess.run(['nice', '-n', '10', 'Singular', '-q', path], capture_output=True, text=True, timeout=timeout)
        return r.stdout
    except subprocess.TimeoutExpired:
        return None
    finally:
        os.remove(path)


def _read_cofs(out):
    if out is None or 'YES' not in out:
        return None
    return [parse_sing_poly(line[2:].strip()) for line in out.split('\n') if line.startswith('C ')]


def _lift_rabin(polys, timeout):
    """cofactors (one per polynomial, then the one of 1 - y prod x) or None."""
    s = SING_HDR + 'ideal J = %s, 1 - yy*tt;\nideal GB = std(J);\n' % ','.join(poly_sing(f) for f in polys)
    s += ('if (deg(GB[1]) == 0) { matrix T = lift(J, ideal(1)); int q; print("YES");'
          ' for (q = 1; q <= nrows(T); q++) { print("C " + string(T[q,1])); } } else { print("NO"); }\nquit;\n')
    return _read_cofs(_sing(s, timeout))


def _unit(polys, rabin, timeout):
    """True / False / None (timeout): is the ideal (with 1 - y prod x if rabin) the unit ideal?"""
    if rabin:
        s = SING_HDR + 'ideal J = %s, 1 - yy*tt;\n' % ','.join(poly_sing(f) for f in polys)
    else:
        s = SING_HDR0 + 'ideal J = %s;\n' % ','.join(poly_sing(f) for f in polys)
    s += 'ideal GB = std(J);\nprint("U " + string(deg(GB[1]) == 0));\nquit;\n'
    out = _sing(s, timeout)
    if out is None:
        return None
    return 'U 1' in out


def _lift_plain(polys, timeout):
    s = SING_HDR0 + 'ideal J = %s;\n' % ','.join(poly_sing(f) for f in polys)
    s += ('matrix T = lift(J, ideal(1)); int q; print("YES");'
          ' for (q = 1; q <= nrows(T); q++) { print("C " + string(T[q,1])); }\nquit;\n')
    return _read_cofs(_sing(s, timeout))


def torus_one(system, t1=60, t2=300):
    """cofactors for sum c_i f_i + c_R (1 - y prod x) = 1 (one per polynomial, then c_R); or 'HYP' if neither the lift
    with the Rabinowitsch polynomial (t1 seconds) nor the lift of the system alone (t2 seconds) finishes but the
    system alone generates the unit ideal (Singular std); or None."""
    cof = _lift_rabin(system, t1)
    if cof is not None:
        return cof
    c = _lift_plain(system, t2)
    if c is not None:
        return c + [[]]
    if _unit(system, False, 1800):
        return 'HYP'
    return None


def torus_tests(systems, workdir, tag, nproc=64, batch=None):
    """per system: None (not shown empty) or the cofactors (one per polynomial, then the one of 1 - y prod x)."""
    from multiprocessing import Pool
    with Pool(nproc) as pool:
        return pool.map(torus_one, systems, chunksize=1)


def check_cof(system, cof):
    """sum cof_i f_i + cof_R (1 - y prod x) == 1 over F_p (dict arithmetic)."""
    acc = {}

    def addmul(a, b):
        for c1, e1 in a:
            for c2, e2 in b:
                e = tuple(x + y for x, y in zip(e1, e2))
                acc[e] = (acc.get(e, 0) + c1 * c2) % P
    for f, c in zip(system, cof):
        addmul([(cc, tuple(e) + (0,)) for cc, e in f], c)
    rab = [(1, (0,) * (NV + 1)), (P - 1, (1,) * NV + (1,))]
    addmul(rab, cof[len(system)])
    acc = {e: c for e, c in acc.items() if c}
    return acc == {(0,) * (NV + 1): 1}


def initial_terms(G, g, F):
    return [G[g][i] for i in F]


def _quick(system):
    return _lift_rabin(system, 10)


def run(kind, outdir, checkpoints, early=False):
    import gsys
    G = json.load(open(os.path.join(outdir, '%s_gbar.json' % kind)))
    G = [[(c, tuple(e)) for c, e in g] for g in G]
    order = sorted(range(len(G)), key=lambda i: (len(G[i]), i))
    T = Tree(G)
    root = T.new()
    t0 = time.time()
    kind_, c = try_cell([], [])
    pend = [(root, c, [])]
    log = open(os.path.join(outdir, '%s_dfs.log' % kind), 'w')

    def lg(s):
        log.write('%.1fs %s\n' % (time.time() - t0, s))
        log.flush()
        print('%.1fs %s' % (time.time() - t0, s), flush=True)
    for step, g in enumerate(order):
        new = []
        for (nid, cell, faces) in pend:
            new += T.refine(nid, cell, faces, g)
        pend = new
        lg('step %d poly %d terms %d -> %d pending; nodes %d; %s' % (step, g, len(G[g]), len(pend), T.next, L.STATS))
        if step == len(order) - 1:
            import pickle
            pickle.dump((T, pend, root), open(os.path.join(outdir, '%s_state.pkl' % kind), 'wb'))
        last = step == len(order) - 1
        if early or step in checkpoints or last:
            systems = [[initial_terms(G, gg, F) for (gg, F) in faces] for (_, _, faces) in pend]
            from multiprocessing import Pool
            with Pool(64) as pool:
                res = pool.map(torus_one if last else _quick, systems, chunksize=1)
            keep = []
            for (nid, cell, faces), sysm, cof in zip(pend, systems, res):
                if cof is not None:
                    assert len(cof) == len(faces) + 1 and check_cof(sysm, cof), nid
                    # faces are pushed in order: position 0 in Lean = most recent face
                    toks = ['L']
                    nz = [(len(faces) - 1 - i, cof[i]) for i in range(len(faces)) if cof[i]]
                    toks.append(len(nz))
                    for pos, pl in nz:
                        toks.append(pos)
                        toks += poly_tokens(pl)
                    toks += poly_tokens(cof[len(faces)])
                    T.nodes[nid] = toks
                else:
                    keep.append((nid, cell, faces))
            lg('  torus tests at step %d: %d of %d empty' % (step, len(pend) - len(keep), len(pend)))
            pend = keep
    assert not pend, ('cells without certificate', len(pend))
    toks = T.emit(root)
    lg('done: %d nodes, %d tokens' % (T.next, len(toks)))
    return toks


def poly_tokens(pl):
    out = [len(pl)]
    for c, e in pl:
        nz = [(i, k) for i, k in enumerate(e) if k]
        out += [c, len(nz)] + [t for ik in nz for t in ik]
    return out


def resume(kind, outdir):
    import pickle
    T, pend, root = pickle.load(open(os.path.join(outdir, '%s_state.pkl' % kind), 'rb'))
    t0 = time.time()
    systems = [[initial_terms(T.G, gg, F) for (gg, F) in faces] for (_, _, faces) in pend]
    from multiprocessing import Pool
    with Pool(64) as pool:
        res = pool.map(torus_one, systems, chunksize=1)
    bad = 0
    hyps = []
    for (nid, cell, faces), sysm, cof in zip(pend, systems, res):
        if cof is None:
            bad += 1
            continue
        if cof == 'HYP':
            # the initial forms in the order of the Lean list of faces (most recent first)
            T.nodes[nid] = ['H', len(hyps)]
            hyps.append([sysm[i] for i in reversed(range(len(faces)))])
            continue
        assert len(cof) == len(faces) + 1 and check_cof(sysm, cof), nid
        toks = ['L']
        nz = [(len(faces) - 1 - i, cof[i]) for i in range(len(faces)) if cof[i]]
        toks.append(len(nz))
        for pos, pl in nz:
            toks.append(pos)
            toks += poly_tokens(pl)
        toks += poly_tokens(cof[len(faces)])
        T.nodes[nid] = toks
    print('resume: %d systems, %d assumed, %d without certificate, %.1fs' % (len(pend), len(hyps), bad, time.time() - t0), flush=True)
    assert bad == 0
    json.dump([[[(c, list(e)) for c, e in f] for f in h] for h in hyps], open(os.path.join(outdir, '%s_hyps.json' % kind), 'w'))
    return T.emit(root)


if __name__ == '__main__':
    kind, outdir = sys.argv[1], sys.argv[2]
    if len(sys.argv) > 3 and sys.argv[3] == 'resume':
        toks = resume(kind, outdir)
        with open(os.path.join(outdir, '%s_tree.txt' % kind), 'w') as fo:
            fo.write(' '.join(toks) + '\n')
        sys.exit(0)
    early = len(sys.argv) > 3 and sys.argv[3] == 'early'
    cps = set(int(x) for x in sys.argv[3].split(',')) if len(sys.argv) > 3 and sys.argv[3] and not early else set()
    toks = run(kind, outdir, cps, early)
    with open(os.path.join(outdir, '%s_tree.txt' % kind), 'w') as fo:
        fo.write(' '.join(toks) + '\n')
