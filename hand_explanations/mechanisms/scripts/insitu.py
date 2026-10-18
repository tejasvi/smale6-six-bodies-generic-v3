#!/usr/bin/env python3
"""In-situ check of the triangle lemmas (E1, R1, R5, R6) on sampled cells: the lemma's leading relations, written in
the cell's own leading coefficients (tinit's variables X{v}_{i}, Y{v}_{i}, D{k}_{l}), are inconsistent at random
masses mod p (Singular), after saturation by the variables involved and by the differences of coordinates of one node.
Relations used: the distance equations of the three pairs of T; the balance equations named by the witness (taken from
tinit.system, i.e. the cell's argmin data); U (lemma E1 'U' case, R5); and for R1/R5/R6 the centre relation
m_a lead(a,O) + m_b lead(b,O) = 0 at the node of T. Usage: insitu.py LEMMA SAMPLE"""
import glob, json, os, random, re, subprocess, sys, tempfile
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
ENG = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'engine')
sys.path.insert(0, ENG)
import tinit as I

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')
DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data')
VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')
PRIME = 32003


def system_for(rec, lem, wit, masses):
    vars_, eqs, sats = I.system(6, rec, masses)
    m = {k: f'({masses[k]})' for k in range(6)}
    names = []
    for nm, labs in rec['argmin']:
        names.append(tuple(tuple(x) if isinstance(x, list) else x for x in nm))
    pairs = [(k, l) for k in range(6) for l in range(k + 1, 6)]
    # eqs = 15 distance equations, then one per argmin entry in order
    byname = {}
    for i, nm in enumerate(names):
        byname[nm] = eqs[15 + i]
    if lem == 'Q':
        col, s0, K = wit
        sel = [byname[(col, 'S', (s0,))]] + [eqs[pairs.index((min(s0, k), max(s0, k)))] for k in K]
        used = sorted(set(v for e in sel for v in VAR.findall(e)))
        sat = list(used)
        return used, sel, sat
    tri = tuple(wit[0])
    sel = [eqs[pairs.index((a, b))] for a, b in [(tri[0], tri[1]), (tri[0], tri[2]), (tri[1], tri[2])]]
    zt, wt = rec['ztree'], rec['wtree']
    if lem == 'E1':
        _, Bz, Bw, how = wit
        if how == 'U':
            Bz, Bw = Bz[:1], Bw[:1]
        for k in Bz:
            sel.append(byname[('z', 'S', (k,))])
        for k in Bw:
            sel.append(byname[('w', 'S', (k,))])
        if how == 'U':
            sel.append(byname[('U',)])
    else:
        if lem == 'R1':
            _, col, s, how = wit
            a, b = [k for k in tri if k != s]
            import lemmas as LM
            A = LM.argmins(rec)
            for k in (a, b):
                if LM.balanced(A, col, k, tri):
                    sel.append(byname[(col, 'S', (k,))])
            if how != 'bal2':
                sel.append(byname[('U',)])
            ccol = col
        elif lem == 'R5':
            _, col, s = wit
            a, b = [k for k in tri if k != s]
            ccol = 'w' if col == 'z' else 'z'
            import lemmas as LM
            A = LM.argmins(rec)
            from_bal = [k for k in (a, b) if LM.balanced(A, col, k, tri)]
            sel.append(byname[(col, 'S', (from_bal[0],))])
            sel.append(byname[('U',)])
        elif lem == 'R6':
            _, col, s, a0 = wit
            a, b = [k for k in tri if k != s]
            oc = 'w' if col == 'z' else 'z'
            sel += [byname[(col, 'S', (s,))], byname[(oc, 'S', (a0,))]]
            ccol = col
        tr, tag = (zt, 'X') if ccol == 'z' else (wt, 'Y')
        sel.append(f'{m[a]}*{I.lead(tr, tag, a, 6)}+{m[b]}*{I.lead(tr, tag, b, 6)}')
    used = sorted(set(v for e in sel for v in VAR.findall(e)))
    sat = list(used)
    bynode = {}
    for v in used:
        if v[0] in 'XY':
            bynode.setdefault(v.split('_')[0], []).append(v)
    for node, lst in bynode.items():
        for i in range(len(lst)):
            for j in range(i + 1, len(lst)):
                sat.append(f'({lst[i]}-{lst[j]})')
    return used, sel, sat


def unit(vars_, eqs, sats, workdir):
    s = [f'ring R = {PRIME}, ({",".join(vars_)}), dp;', f'ideal I = {",".join(eqs)};']
    for f in sats:
        s.append(f'I = sat(I, ideal({f}));')
    s += ['ideal G = std(I);', 'print("DIM " + string(dim(G)));', 'quit;']
    fd, path = tempfile.mkstemp(suffix='.sing', dir=workdir)
    with os.fdopen(fd, 'w') as fh:
        fh.write('\n'.join(s) + '\n')
    out = subprocess.run(['Singular', '-q', path], capture_output=True, text=True, timeout=300).stdout
    os.unlink(path)
    for line in out.splitlines():
        if line.startswith('DIM '):
            return int(line.split()[1]) == -1
    return None


def main():
    lem = sys.argv[1]
    ns = int(sys.argv[2])
    rng = random.Random(11)
    cov = [json.loads(l) for l in open(os.path.join(DATA, 'coverage.jsonl'))]
    cand = [r for r in cov if r['lemmas'].get(lem)]
    rng.shuffle(cand)
    cand = cand[:ns]
    need = {}
    for r in cand:
        need.setdefault(r['class'], {})[r['cell']] = r
    workdir = os.path.join(DATA, 'tmp_insitu')
    os.makedirs(workdir, exist_ok=True)
    res = {'unit': 0, 'not': 0, 'fail': 0}
    bad = []
    for d in sorted(glob.glob(os.path.join(ROOT, '*', 'exact6', 'c*'))):
        c = int(d.rsplit('/c', 1)[1])
        if c not in need:
            continue
        for i, line in enumerate(open(os.path.join(d, 'cells.jsonl'))):
            if i not in need[c]:
                continue
            rec = json.loads(line)
            wit = need[c][i]['witness'][lem]
            if isinstance(wit, str):
                wit = eval(wit)
            masses = [rng.randrange(2, PRIME - 1) for _ in range(6)]
            try:
                v, e, s = system_for(rec, lem, wit, masses)
                u = unit(v, e, s, workdir)
            except Exception as ex:
                res['fail'] += 1
                bad.append((c, i, repr(ex)[:100]))
                continue
            if u:
                res['unit'] += 1
            else:
                res['not'] += 1
                bad.append((c, i, wit))
    print(lem, res, bad[:10])


if __name__ == '__main__':
    main()
