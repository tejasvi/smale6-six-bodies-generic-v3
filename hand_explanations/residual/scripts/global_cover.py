#!/usr/bin/env python3
"""Apply the residual lemmas B0, K, L, R1* (centre of mass of clusters or Lemma S only; no LP), W3, EQ2 to all
91,273 nonpositive cells, and combine with the coverage of ../mechanisms (data/coverage.jsonl).
TQ and the subset-sum variant of R1* need exact LP certificates and are applied only to the residual cells
(run_resid.py). Output ../data/global_cover.jsonl (one line per cell: lemmas that apply) and a summary."""
import glob, json, os, sys, time
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rkit as R
import exactlp as X
import lemmas_resid as LR

ALLMASS_MECH = {'T', 'P', 'C', 'B'}
ALLMASS_FIRST = {'coreB', 'coreLIN-all', 'coreP4'}


def main():
    mech = {}
    for l in open(os.path.join(R.MECH, 'data', 'coverage.jsonl')):
        r = json.loads(l)
        mech[(r['class'], r['cell'])] = r
    resid = {}
    p = os.path.join(R.DATA, 'resid_cover.jsonl')
    for l in open(p):
        r = json.loads(l)
        resid[(r['class'], r['cell'])] = r
    out = open(os.path.join(R.DATA, 'global_cover.jsonl'), 'w')
    cnt = Counter()
    t0 = time.time()
    n = 0
    cls = R.classes()
    for d in sorted(glob.glob(os.path.join(R.ENG, '*', 'exact6', 'c*'))):
        c = int(d.rsplit('/c', 1)[1])
        pth = os.path.join(d, 'cells.jsonl')
        if not os.path.exists(pth) or os.path.getsize(pth) == 0:
            continue
        D = X.Diag(cls[c])
        for i, line in enumerate(open(pth)):
            rec = json.loads(line)
            rec['class'] = c
            C = LR.Ctx(rec, D)
            app = []
            if LR.lemma_B0(C):
                app.append('B0')
            if LR.lemma_K(C):
                app.append('K')
            if LR.lemma_L(C):
                app.append('L')
            if LR.lemma_R1star(C, try_subset=False):
                app.append('R1*')
            if LR.lemma_W3(C):
                app.append('W3')
            if LR.lemma_EQ2(C):
                app.append('EQ2')
            key = (c, i)
            if key in resid:
                app = sorted(set(app) | set(resid[key]['applies']))
            m = mech[key]
            mlem = {k for k, v in m['lemmas'].items() if v}
            allmass_old = bool(mlem & ALLMASS_MECH) or m['first'] in ALLMASS_FIRST
            allmass_new = allmass_old or bool(set(app) & {'B0', 'K', 'L', 'TD'})
            generic_old = m['first'] != 'comp'
            generic_new = generic_old or bool(app)
            cnt['cells'] += 1
            cnt['allmass_old'] += allmass_old
            cnt['allmass_new'] += allmass_new
            cnt['generic_old'] += generic_old
            cnt['generic_new'] += generic_new
            for a in app:
                cnt['applies_' + a] += 1
            if allmass_new and not allmass_old:
                cnt['allmass_gain'] += 1
                for a in set(app) & {'B0', 'K', 'L', 'TD'}:
                    cnt['allmass_gain_' + a] += 1
                cnt[f'allmass_gain_kind_{m["kind"]}'] += 1
            out.write(json.dumps({'class': c, 'cell': i, 'kind': m['kind'], 'mech_first': m['first'],
                                  'resid_lemmas': app, 'allmass_old': allmass_old, 'allmass_new': allmass_new}) + '\n')
            n += 1
            if n % 10000 == 0:
                print(n, round(time.time() - t0), flush=True)
    summary = dict(sorted(cnt.items()))
    json.dump(summary, open(os.path.join(R.DATA, 'global_cover_summary.json'), 'w'), indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == '__main__':
    main()
