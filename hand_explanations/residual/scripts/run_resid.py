#!/usr/bin/env python3
"""Apply the residual lemmas to the 115 residual cells of ../mechanisms (first applicable in the order
B0, K, L, R1*, W3, EQ2, TQ, TD) and record all witnesses. Output ../data/resid_cover.jsonl and a summary."""
import json, os, sys, time
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rkit as R
import exactlp as X
import lemmas_resid as LR


def jsonable(x):
    if isinstance(x, dict):
        return {str(k): jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [jsonable(v) for v in x]
    if isinstance(x, (frozenset, set)):
        return sorted(jsonable(v) for v in x)
    if hasattr(x, 'numerator') and not isinstance(x, int):
        return str(x)
    return x


def main():
    out = open(os.path.join(R.DATA, 'resid_cover.jsonl'), 'w')
    first = Counter()
    t0 = time.time()
    for r in R.residual():
        c, i = r['class'], r['cell']
        rec = R.load_cell(c, i)
        D = X.Diag(R.classes()[c])
        C = LR.Ctx(rec, D)
        wit = {}
        wit['B0'] = LR.lemma_B0(C)
        wit['K'] = LR.lemma_K(C)
        wit['L'] = LR.lemma_L(C)
        wit['R1*'] = LR.lemma_R1star(C)
        wit['W3'] = LR.lemma_W3(C)
        wit['EQ2'] = LR.lemma_EQ2(C)
        wit['TQ'] = LR.lemma_TQ(C)
        if r['kind'] == 'single':
            idn, tm = r['engine_single']
            J = eval(idn)[1]
            t = eval(tm)
            lab = ('zw', t[1], t[2]) if t[0] == 'T1' else ('zw', t[2], t[1])
            wit['TD'] = LR.lemma_TD(C, J, lab)
        st = next((k for k in ('B0', 'K', 'L', 'R1*', 'W3', 'EQ2', 'TQ', 'TD') if wit.get(k)), 'none')
        first[(r['kind'], st)] += 1
        for k, v in list(wit.items()):
            if v and 'cert' in v:
                v = dict(v)
                v['cert'] = [(str(lab), [(str(y), str(l)) for y, l in cert[0]], str(cert[1])) for lab, cert in v['cert']]
                wit[k] = v
        out.write(json.dumps({'class': c, 'cell': i, 'kind': r['kind'], 'label': r['label'], 'first': st,
                              'applies': sorted(k for k, v in wit.items() if v),
                              'witness': jsonable({k: v for k, v in wit.items() if v})}) + '\n')
        print(c, i, r['kind'], r['label'], st, sorted(k for k, v in wit.items() if v), round(time.time() - t0, 1),
              flush=True)
    print(dict(first))


if __name__ == '__main__':
    main()
