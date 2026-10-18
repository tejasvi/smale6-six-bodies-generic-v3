#!/usr/bin/env python3
"""Counts for MECHANISMS_v2.md (referee items M5-M8), read-only on the engine data and on data/coverage.jsonl.

1. From data/coverage.jsonl: the classes of the 115 residual cells; the single-term table of §2.1 (as tables.py);
   whether B and R5 are ever needed.
2. One pass over all 91,273 cells with the checkers' own helpers (lemmas.py): for Lemma E1, the cells where some
   triangle satisfies the main hypothesis (H2), where only the U_T variant holds, where the first witness triangle is
   balanced at all three vertices in both colours, and where some triangle is; for Lemma R1, the cells where two
   balances hold for some centred triangle, and where only the one-balance + U_T variant holds.
Output data/counts_v2.json."""
import glob, itertools, json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collections import Counter, defaultdict
from cellkit import Cell, O, N
import lemmas as LM

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')
DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data')
ECLS = {3, 148, 149, 40, 150, 183}
BODIES = range(N)


def e1_census(C, A):
    """(main hypothesis for some triangle, U_T variant for some triangle, first witness balanced 3+3,
    some triangle balanced 3+3)"""
    main = var = first33 = any33 = False
    first_seen = False
    for tri in itertools.combinations(BODIES, 3):
        if LM.common_meet(C.zt, tri) is None or LM.common_meet(C.wt, tri) is None:
            continue
        Bz = {k for k in tri if LM.balanced(A, 'z', k, tri)}
        Bw = {k for k in tri if LM.balanced(A, 'w', k, tri)}
        m = (len(Bz) >= 2 and len(Bw) >= 1) or (len(Bw) >= 2 and len(Bz) >= 1)
        u = bool(Bz and Bw and LM.U_tri(A, tri))
        if (m or u) and not first_seen:
            first_seen = True
            first33 = m and len(Bz) == 3 and len(Bw) == 3
        main |= m
        var |= u
        any33 |= (len(Bz) == 3 and len(Bw) == 3)
    return main, var, first33, any33


def r1_census(C, A):
    """(two balances for some centred triangle, one balance + U_T for some centred triangle)"""
    two = one = False
    for tri in itertools.combinations(BODIES, 3):
        if LM.common_meet(C.zt, tri) is None or LM.common_meet(C.wt, tri) is None:
            continue
        for col, T in (('z', C.zt), ('w', C.wt)):
            for s in tri:
                if not LM.centred(T, tri, s):
                    continue
                a, b = [k for k in tri if k != s]
                nb = LM.balanced(A, col, a, tri) + LM.balanced(A, col, b, tri)
                two |= (nb == 2)
                one |= (nb == 1 and LM.U_tri(A, tri))
    return two, one


def main():
    res = {}
    cov = [json.loads(l) for l in open(os.path.join(DATA, 'coverage.jsonl'))]
    assert len(cov) == 91273
    # residue classes
    rc = Counter(r['class'] for r in cov if r['first'] == 'comp')
    res['residue cells'] = sum(rc.values())
    res['residue classes'] = len(rc)
    res['residue by class'] = {str(c): v for c, v in sorted(rc.items())}
    # single-term table (as tables.py, section T1)
    tab = defaultdict(Counter)
    for r in cov:
        if r['kind'] != 'single':
            continue
        idn = eval(r['engine_single'][0])
        tm = eval(r['engine_single'][1])
        it = idn[0]
        if it == 'T':
            it = 'T|J|=%d' % min(len(idn[1]), 6 - len(idn[1]))
        elif it == 'S':
            it = 'S|J|=%d' % len(idn[2])
        key = '%s %s' % (it, tm[0])
        L = r['lemmas']
        tab[key]['cells'] += 1
        for k in ('T', 'P', 'C', 'B'):
            tab[key][k] += L[k]
        tab[key]['T,P,C or B'] += (L['T'] or L['P'] or L['C'] or L['B'])
        tab[key]['E/E1/R1/R5/R6/Q'] += (r['class'] in ECLS or L['E1'] or L['R1'] or L['R5'] or L['R6'] or L['Q'])
        tab[key]['residue'] += (r['first'] == 'comp')
    res['single-term table'] = {k: dict(v) for k, v in sorted(tab.items(), key=lambda t: -t[1]['cells'])}
    # B and R5 never needed
    res['B cells'] = sum(r['lemmas']['B'] for r in cov)
    res['B cells outside T or C'] = sum(1 for r in cov if r['lemmas']['B'] and not (r['lemmas']['T'] or r['lemmas']['C']))
    res['R5 cells'] = sum(r['lemmas']['R5'] for r in cov)
    res['R5 cells outside E or E1'] = sum(1 for r in cov if r['lemmas']['R5']
                                          and not (r['class'] in ECLS or r['lemmas']['E1']))
    gen_wo_R5 = lambda r: (r['class'] in ECLS or any(r['lemmas'][k] for k in ('E1', 'R1', 'R6', 'Q', 'T', 'P', 'C', 'B'))
                           or r['first'].startswith('core') or r['first'] in ('d64', 'd88', 'd98'))
    res['R5 cells covered by nothing else'] = sum(1 for r in cov if r['lemmas']['R5'] and not gen_wo_R5(r))
    res['E1 stored witnesses balanced 3+3'] = sum(1 for r in cov if 'E1' in r['witness']
                                                  and len(r['witness']['E1'][1]) == 3
                                                  and len(r['witness']['E1'][2]) == 3)
    res['E1 stored witnesses by tag'] = dict(Counter(r['witness']['E1'][3] for r in cov if 'E1' in r['witness']))
    res['R1 stored witnesses by tag'] = dict(Counter(r['witness']['R1'][3] for r in cov if 'R1' in r['witness']))
    # one pass over the cells
    cnt = Counter()
    t0 = time.time()
    n = 0
    for d in sorted(glob.glob(os.path.join(ROOT, '*', 'exact6', 'c*'))):
        c = int(d.rsplit('/c', 1)[1])
        p = os.path.join(d, 'cells.jsonl')
        if not os.path.exists(p) or os.path.getsize(p) == 0:
            continue
        for line in open(p):
            rec = json.loads(line)
            C = Cell(rec)
            A = LM.argmins(rec)
            main_, var, f33, a33 = e1_census(C, A)
            cnt['E1 main hypothesis (some triangle)'] += main_
            cnt['E1 U_T variant (some triangle)'] += var
            cnt['E1 main or variant'] += (main_ or var)
            cnt['E1 only via the U_T variant'] += (var and not main_)
            cnt['E1 first witness balanced at all three vertices in both colours'] += f33
            cnt['E1 some triangle balanced at all three vertices in both colours'] += a33
            two, one = r1_census(C, A)
            cnt['R1 two balances (some centred triangle)'] += two
            cnt['R1 one balance + U_T (some centred triangle)'] += one
            cnt['R1 main or variant'] += (two or one)
            cnt['R1 only via the one-balance + U_T variant'] += (one and not two)
            n += 1
            if n % 10000 == 0:
                print(n, round(time.time() - t0), flush=True)
    res['cells scanned'] = n
    res.update(dict(sorted(cnt.items())))
    json.dump(res, open(os.path.join(DATA, 'counts_v2.json'), 'w'), indent=1)
    print(json.dumps(res, indent=1))


if __name__ == '__main__':
    main()
