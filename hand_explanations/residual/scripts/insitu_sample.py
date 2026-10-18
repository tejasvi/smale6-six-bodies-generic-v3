#!/usr/bin/env python3
"""In-situ checks (as insitu_resid.py) on random samples of all cells where B0, K, L, W3, EQ2, R1* apply
(global_cover.jsonl). Usage: insitu_sample.py N_PER_LEMMA  -> ../data/insitu_sample.log"""
import json, os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rkit as R
import exactlp as X
import lemmas_resid as LR
import insitu_resid as I

FN = {'B0': LR.lemma_B0, 'K': LR.lemma_K, 'L': LR.lemma_L, 'W3': LR.lemma_W3, 'EQ2': LR.lemma_EQ2,
      'R1*': lambda C: LR.lemma_R1star(C, try_subset=False)}


def main():
    NS = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    rng = random.Random(11)
    rows = [json.loads(l) for l in open(os.path.join(R.DATA, 'global_cover.jsonl'))]
    jobs = []
    prime = 32003
    for lem, fn in FN.items():
        cand = [r for r in rows if lem in r['resid_lemmas']]
        rng.shuffle(cand)
        for r in cand[:NS]:
            rec = R.load_cell(r['class'], r['cell'])
            D = X.Diag(R.classes()[r['class']])
            w = fn(LR.Ctx(rec, D))
            assert w, (lem, r)
            w = json.loads(json.dumps(w, default=str))
            masses = [rng.randrange(2, prime - 1) for _ in range(6)]
            S = I.build(rec, lem, w, masses)
            jobs.append(((lem, r['class'], r['cell']), S))
    work = os.path.join(R.DATA, 'work')
    log = open(os.path.join(R.DATA, 'insitu_sample.log'), 'w')
    bad = 0
    from collections import Counter
    ok_by = Counter()
    for b0 in range(0, len(jobs), 40):
        chunk = jobs[b0:b0 + 40]
        res = I.run_batch([S.singular(i, prime) for i, (_, S) in enumerate(chunk)], work)
        for i, (key, S) in enumerate(chunk):
            d = res.get(i)
            ok = d is not None and d[0] == -1
            bad += not ok
            ok_by[(key[0], ok)] += 1
            log.write(f'{key} {d} {"OK" if ok else "FAIL"}\n')
            if not ok:
                print('FAIL', key, d, flush=True)
    log.write(f'jobs {len(jobs)} failures {bad} {dict(ok_by)}\n')
    print('jobs', len(jobs), 'failures', bad, dict(ok_by))


if __name__ == '__main__':
    main()
