#!/usr/bin/env python3
"""Exact version of tsec.py: secondary identities whose argmin set is constant on the cell, with every LP verdict
used for that conclusion certified exactly (treplay.Certifier). Per cell, either an exact exclusion by a secondary
identity whose least exponent is attained by a single term on the whole cell, or the system of initial forms (with
symbolic masses m0..m(n-1) and with the random masses used for the mod-p core search).
A cell is excluded only through certified verdicts: 'single' needs, for the term i, certified infeasibility of
{cell, t_k <= t_i} for every k != i; a constant argmin S needs that for k outside S and certified infeasibility of
{cell, +-(t_j - t_i) >= s} for j in S. Identities whose checks are not all certified are dropped (always safe).
Usage: tsec_exact.py N CLASSES_JSON IDX CELLS.jsonl OUT.jsonl [--part K --nparts P] [--prime P] [--seed S]"""
import itertools, json, os, random, sys
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tengine as T
import texact as X
import tinit as I
import tsec as S
import treplay as R


def constant_argmin_exact(L, terms, C, ctx, tol=1e-7):
    """('single', i), ('set', S) or None; every negative LP verdict that the conclusion uses is certified by C."""
    ok, val, sol = L.solve()
    if not ok or val <= T.TOL:
        return None
    vals = [sum(c * sol[j] for j, c in f.items()) for f, _ in terms]
    mn = min(vals)
    Sset = [i for i, v in enumerate(vals) if abs(v - mn) < tol]
    i0 = Sset[0]
    s = L.ns
    for k in range(len(terms)):
        if k == i0:
            continue
        d = S.add(terms[k][0], S.scale(terms[i0][0], -1.0))
        if k in Sset:
            for sg in (1.0, -1.0):
                dd = dict(S.scale(d, sg))
                dd[s] = dd.get(s, 0.0) - 1.0
                if C.feasible(X.sub(L, [(dd, 0.0, None)]), ctx):
                    return None
        else:
            if C.feasible(X.sub(L, [(d, None, 0.0)]), ctx):
                return None
    return ('single', i0) if len(Sset) == 1 else ('set', Sset)


def main():
    n = int(sys.argv[1])
    cls = json.load(open(sys.argv[2]))['classes']
    ci = int(sys.argv[3])
    outp = sys.argv[5]
    pk, pn = 0, 1
    if '--part' in sys.argv:
        pk = int(sys.argv[sys.argv.index('--part') + 1])
        pn = int(sys.argv[sys.argv.index('--nparts') + 1])
    cells = {}                                   # only this part's lines are parsed (memory)
    with open(sys.argv[4]) as fh:
        for i, l in enumerate(fh):
            if i % pn == pk:
                cells[i] = json.loads(l)
    prime = int(sys.argv[sys.argv.index('--prime') + 1]) if '--prime' in sys.argv else 32003
    seed = int(sys.argv[sys.argv.index('--seed') + 1]) if '--seed' in sys.argv else 1
    rng = random.Random(seed)
    masses = [rng.randrange(2, prime - 1) for _ in range(n)]
    msym = [f'm{k}' for k in range(n)]
    only = sorted(cells)
    D = T.Diagram.from_json(n, cls[ci])
    C = R.Certifier()
    with open(outp, 'w') as f:
        for ci_ in only:
            cell = cells[ci_]
            zt, wt = S.tree_from_json(n, cell['ztree']), S.tree_from_json(n, cell['wtree'])
            L = S.cell_lp(D, zt, wt, cell['argmin'])
            vnum, eqnum, sats = I.system(n, cell, masses)
            vsym, eqsym, _ = I.system(n, cell, msym)
            names = [repr(('D', k, l)) for k, l in itertools.combinations(range(n), 2)] + \
                    [repr(tuple(tuple(a) if isinstance(a, list) else a for a in nm)) for nm, _ in cell['argmin']]
            mn = {k: f'({masses[k]})' for k in range(n)}
            ms = {k: f'({msym[k]})' for k in range(n)}
            rec = {'cell': ci_, 'sumx': cell['sumx']}
            for name, terms in S.secondary(D, zt, wt, L):
                r = constant_argmin_exact(L, terms, C, {'cell': ci_, 'identity': repr(name)})
                if r is None:
                    continue
                if r[0] == 'single':
                    rec['excluded_by'] = {'identity': repr(name), 'term': repr(terms[r[1]][1])}
                    break
                Sset = r[1]
                eqnum.append('+'.join(S.term_expr(n, cell['ztree'], cell['wtree'], terms[i][1], mn) for i in Sset).replace('+-', '-'))
                eqsym.append('+'.join(S.term_expr(n, cell['ztree'], cell['wtree'], terms[i][1], ms) for i in Sset).replace('+-', '-'))
                names.append(repr(name))
            if 'excluded_by' not in rec:
                rec['system'] = {'vars': vnum, 'eqs': eqnum, 'eqs_sym': eqsym, 'names': names, 'sats': sats}
                rec['dim'] = -1          # tcore searches for a core; tcert certifies it
            f.write(json.dumps(rec) + '\n')
    cnt = dict(C.c)
    json.dump({'class': ci, 'counts': cnt, 'fails': C.fails[:20], 'border': C.border[:20]}, open(outp + '.cert.json', 'w'))
    print(json.dumps({'class': ci, 'cells': len(list(only)), 'fail': cnt['fail'], 'pruned': cnt['pruned']}))


if __name__ == '__main__':
    main()
