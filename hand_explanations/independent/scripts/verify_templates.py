#!/usr/bin/env python3
"""For the 179 cells that rest only on the engine-core templates (LIN, P4): recompute, on the referee's own cell
polyhedra, the argmin set of every secondary identity (subset sums S_J, torques T_J) of the engine's core, check that
it is constant on the cell, and compare its terms with the engine's initial form. Then recompute the LIN condition
from the referee's own initial forms (position leads keyed by (node, child)).
Usage: verify_templates.py"""
import json, os, re, sys, itertools
from collections import Counter
import sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import refkit as K
from refkit import O, BODIES
from ref_lp import CellLP, below_everywhere, equal_everywhere

CLS = K.classes()
part = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'partition.json')))
TARGET = set(tuple(x) for x in part['P4'])
if os.environ.get('ALL_TEMPLATES'):
    TARGET = set()
    for _l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'mechanisms', 'data', 'coverage.jsonl')):
        _r = json.loads(_l)
        if _r['first'].startswith('core'):
            TARGET.add((_r['class'], _r['cell']))
mech = {}
for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'mechanisms', 'data', 'coverage.jsonl')):
    r = json.loads(l)
    if (r['class'], r['cell']) in TARGET:
        mech[(r['class'], r['cell'])] = r
cores = {}
for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'mechanisms', 'data', 'cores_h.jsonl')):
    r = json.loads(l)
    k = (r['class'], r['cell'])
    if k in TARGET and r['certified'] is not False and (k not in cores or r['certified'] is True):
        cores[k] = r
recs = {}
for c, i, rec in K.iter_cells({c for c, _ in TARGET}):
    if (c, i) in TARGET:
        recs[(c, i)] = rec
m = sp.symbols('m0:6')


def tinit_lead(tr, tag, p, q):
    """the engine's name of the leading coefficient of z_pq (tinit.py convention), for matching only"""
    v = tr.meet(p, q)
    if v is None:
        return None
    def co(i):
        return '0' if i == 0 else f'{tag}{v}_{i}'
    cp = tr.ch[v].index(tr.child_to(v, p))
    cq = tr.ch[v].index(tr.child_to(v, q))
    return f'({co(cp)}-{co(cq)})'


def split_top(e):
    """split an expression into top-level signed terms"""
    terms, depth, cur = [], 0, ''
    for ch in e:
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        if depth == 0 and ch in '+-' and cur.strip() not in ('',):
            terms.append(cur)
            cur = ch
        else:
            cur += ch
    if cur.strip():
        terms.append(cur)
    return terms


def engine_terms_S(e, J):
    out = set()
    for t in split_top(e):
        ms = [int(x) for x in re.findall(r'\(m(\d)\)', t)]
        if 'D' in t:
            i, j = ms
            out.add(('cross', i, j) if i in J else ('cross', j, i))
        else:
            assert len(ms) == 1, t
            out.add(('pos', ms[0]))
    return out


def engine_terms_T(e, C):
    out = set()
    for t in split_top(e):
        d = re.search(r'D(\d)_(\d)', t)
        a, b = int(d.group(1)), int(d.group(2))
        leads = re.findall(r'\([XY0][\w]*-[XY0][\w]*\)', t)
        zl = [x for x in leads if 'X' in x]
        wl = [x for x in leads if 'Y' in x]
        assert len(zl) == 1 and len(wl) == 1, t
        found = None
        for p, q in ((a, b), (b, a)):
            if tinit_lead(C.zt, 'X', p, O) == zl[0] and tinit_lead(C.wt, 'Y', q, O) == wl[0]:
                found = (p, q)
        assert found is not None, (t, a, b)
        out.add(found)
    return out


def my_argmin(L, terms, C, hz_point):
    """argmin at the stored interior point, then verify constancy by LP. terms: label -> form."""
    import numpy as np
    def val(f):
        s = 0.0
        for k, v in f.items():
            if k == L.s:
                continue
            col, n = [kk for kk, idx in L.var.items() if idx == k][0]
            s += v * (C.hz if col == 'z' else C.hw)[n]
        return s
    vals = {t: val(f) for t, f in terms.items()}
    mn = min(vals.values())
    S = {t for t, v in vals.items() if v < mn + 1e-4}
    s0 = sorted(S)[0]
    const = True
    for t in S:
        if t != s0 and not equal_everywhere(L, terms[s0], terms[t]):
            const = False
    for t, f in terms.items():
        if t not in S:
            ok, r = below_everywhere(L, terms[s0], f)
            if not ok:
                const = False
    return S, const


def S_terms(L, col, J):
    t = {}
    for k in J:
        p = L.pos(col, k)
        if p is not None:
            t[('pos', k)] = p
        for j in BODIES:
            if j not in J:
                t[('cross', k, j)] = L.force(col, k, j)
    return t


def T_terms(L, J):
    t = {}
    Jc = [j for j in BODIES if j not in J]
    for k in J:
        for l in Jc:
            for p, q in ((k, l), (l, k)):
                if L.pos('z', p) is None or L.pos('w', q) is None:
                    continue
                t[(p, q)] = L.lin((1, L.pos('z', p)), (1, L.pos('w', q)), (-3, L.xkl(p, q)))
    return t


def lin_condition(C, rows):
    """rows: list of (col, {key: mass-sum expr}). Find r rows with <= r columns of full column rank."""
    for r in range(1, len(rows) + 1):
        for sub in itertools.combinations(rows, r):
            cols = sorted({k for _, row in sub for k in row}, key=str)
            if len(cols) > r:
                continue
            Mx = sp.Matrix([[row.get(c, 0) for c in cols] for _, row in sub])
            if Mx.rank() == len(cols):
                minors = [sp.factor(Mx.extract(list(rr), list(range(len(cols)))).det())
                          for rr in itertools.combinations(range(r), len(cols))]
                return [d for d in minors if d != 0]
    return None


stats = Counter()
bad = []
for key in sorted(TARGET):
    c, i = key
    C = K.RCell(recs[key], c, i)
    L = CellLP(C, K.RDiag(CLS[c]))
    core = cores[key]
    linrows = []
    ok_all = True
    for nm, eq in zip(core['names'], core['core_sym']):
        t = eval(nm)
        if t[0] == 'S':
            col, J = t[1], t[2]
            S, const = my_argmin(L, S_terms(L, col, J), C, None)
            eng = engine_terms_S(eq, J)
            stats['S'] += 1
            if not const or S != eng:
                ok_all = False
                bad.append((key, nm, sorted(S), sorted(eng), const))
            elif all(x[0] == 'pos' for x in S):
                tr = C.tree(col)
                row = {}
                for x in S:
                    k = x[1]
                    v = tr.meet(k, O)
                    kk = (v, tr.child_to(v, k))
                    row[kk] = row.get(kk, 0) + m[k]
                linrows.append((col, row))
        elif t[0] == 'T':
            J = t[1]
            S, const = my_argmin(L, T_terms(L, J), C, None)
            eng = engine_terms_T(eq, C)
            stats['T'] += 1
            if not const or S != eng:
                ok_all = False
                bad.append((key, nm, sorted(S), sorted(eng), const))
        elif t[0] in ('z', 'w'):
            stats['body'] += 1        # base identity: argmin is cell data
        elif t[0] == 'D':
            stats['D'] += 1
        else:
            stats['other:' + t[0]] += 1
    first = mech[key]['first']
    if first.startswith('coreLIN'):
        mine = lin_condition(C, linrows)
        theirs = mech[key]['core_fam'][1]
        same = mine is not None and sorted(str(sp.factor(x)) for x in mine) == sorted(
            str(sp.factor(sp.sympify(x))) for x in theirs)
        # equality of the minor sets up to sign
        if mine is not None and not same:
            a = {sp.factor(x) for x in mine} | {sp.factor(-x) for x in mine}
            b = {sp.factor(sp.sympify(x)) for x in theirs}
            same = b <= a
        stats['LIN'] += 1
        stats['LIN_same'] += bool(same)
        if not same:
            bad.append((key, 'LIN', [str(x) for x in mine] if mine else None, theirs))
    else:
        stats['P4'] += 1
    stats['cells_ok' if ok_all else 'cells_bad'] += 1
print(dict(stats))
for b in bad[:30]:
    print(b)
