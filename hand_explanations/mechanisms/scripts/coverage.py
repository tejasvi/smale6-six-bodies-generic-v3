#!/usr/bin/env python3
"""Coverage of the lemmas of MECHANISMS.md over all 91,273 nonpositive cells (read-only on the engine data).

For every cell: the cell data (trees, argmin sets) and, for cells excluded by a core, the engine's core. The lemmas
are tried in order; the first that applies is recorded, together with the set of all cell-level lemmas that apply.
  E     class-level: a zw-triangle with no circle and no other stroke at its vertices (Lemma E; generic: E(T))
  T     torque, deepest cross pair (Lemma T; every positive mass)
  P     positive I' (Lemma P; every positive mass)
  C     cluster sum (Lemma C; every positive mass)
  B     binary (Lemma B; every positive mass)
  E1    balanced triangle (Lemma E1; generic: E(T))
  R1    triangle with a vertex at the centre (Lemma R1; generic: R(ab;s))
  R5    centre in one colour, balance at a non-centre vertex in the other, U_T (Lemma R5; generic)
  R6    centre and balance at s in one colour, balance at a in the other (Lemma R6; generic)
  Q     equidistant forces: a balance by forces of equal leading coefficients (Lemma Q; generic: signed mass sum)
  coreB / coreLIN / coreP4: the engine's core is an instance of Lemma B / LIN / P4 (template match)
  d64 / d88 / d98: classes or cells settled by the hand proofs of those folders
  comp  none of the above (the engine's computation remains)
Usage: coverage.py [--sample K]  (K: only every K-th cell, for testing)"""
import glob, json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collections import Counter, defaultdict
from cellkit import Cell, Diag, load_classes
import lemmas as LM
import corefam as CF

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')
DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data')
ECLS = {3, 148, 149, 40, 150, 183}
DCLASS = {124: 'd64', 143: 'd64', 127: 'd88', 147: 'd88', 133: 'd98', 131: 'd98', 31: 'd98', 132: 'd98'}
DCELL = {(31, 22): 'd98', (132, 53): 'd98', (133, 17): 'd98'}


def lin_status(minors):
    """'all' if no minor has a zero with all masses positive (every nonzero coefficient of one sign), else 'generic'."""
    import sympy as sp
    for d in minors:
        p = sp.Poly(sp.expand(d), *CF.M)
        cs = p.coeffs()
        if all(c > 0 for c in cs) or all(c < 0 for c in cs):
            return 'all'
    return 'generic'


def main():
    sample = int(sys.argv[sys.argv.index('--sample') + 1]) if '--sample' in sys.argv else 1
    cls = load_classes()
    single = {}
    for l in open(os.path.join(DATA, 'single.jsonl')):
        r = json.loads(l)
        single[(r['class'], r['cell'])] = (r['identity'], r['term'])
    cores = {}
    for l in open(os.path.join(DATA, 'cores_h.jsonl')):
        r = json.loads(l)
        if r['certified'] is False:
            continue
        key = (r['class'], r['cell'])
        if key not in cores or r['certified'] is True:
            cores[key] = r
    labels = {}
    for l in open(os.path.join(DATA, 'core_pat_ids.jsonl')):
        r = json.loads(l)
        labels[(r['class'], r['cell'])] = r['label']
    out = open(os.path.join(DATA, 'coverage.jsonl' if sample == 1 else 'coverage_sample.jsonl'), 'w')
    first = Counter()
    by_class = defaultdict(Counter)
    applies = Counter()
    n = 0
    t0 = time.time()
    for d in sorted(glob.glob(os.path.join(ROOT, '*', 'exact6', 'c*'))):
        c = int(d.rsplit('/c', 1)[1])
        p = os.path.join(d, 'cells.jsonl')
        if not os.path.exists(p) or os.path.getsize(p) == 0:
            continue
        D = Diag(cls[c])
        for i, line in enumerate(open(p)):
            if i % sample:
                continue
            rec = json.loads(line)
            rec['class'] = c
            key = (c, i)
            C = Cell(rec)
            kind = 'single' if key in single else 'core'
            res = {}
            res['T'] = LM.lemma_T(C)
            res['P'] = LM.lemma_P2(C, D, rec)
            res['C'] = LM.lemma_C(C, rec)
            res['B'] = LM.lemma_B(C, D, rec)
            res['E1'] = LM.lemma_E1(C, D, rec)
            res['R1'] = LM.lemma_R1(C, D, rec)
            res['R5'] = LM.lemma_R5(C, D, rec)
            res['R6'] = LM.lemma_R6(C, D, rec)
            res['Q'] = LM.lemma_Q(C, D, rec)
            for k, v in res.items():
                if v is not None:
                    applies[(kind, k)] += 1
            st = None
            if c in ECLS:
                st = 'E'
            else:
                for k in ('T', 'P', 'C', 'B', 'E1', 'R1', 'R5', 'R6', 'Q'):
                    if res[k] is not None:
                        st = k
                        break
            core_fam = None
            if st is None and key in cores:
                cr = cores[key]
                f, lab = CF.classify(cr['names'], cr['core_sym'])
                if f is not None:
                    core_fam = (f, [str(x) for x in lab])
                    st = 'core' + f
                    if f == 'LIN':
                        st += '-' + lin_status(lab)
            if st is None:
                if c in DCLASS:
                    st = DCLASS[c]
                elif key in DCELL:
                    st = DCELL[key]
                else:
                    st = 'comp'
            first[(kind, st)] += 1
            by_class[c][st] += 1
            out.write(json.dumps({'class': c, 'cell': i, 'kind': kind, 'first': st,
                                  'lemmas': {k: (v is not None) for k, v in res.items()},
                                  'witness': {k: v for k, v in res.items() if v is not None},
                                  'core_fam': core_fam, 'label': labels.get(key),
                                  'engine_single': single.get(key)}, default=str) + '\n')
            n += 1
            if n % 5000 == 0:
                print(n, round(time.time() - t0), flush=True)
    summary = {'cells': n, 'first': {f'{k[0]}|{k[1]}': v for k, v in sorted(first.items())},
               'applies': {f'{k[0]}|{k[1]}': v for k, v in sorted(applies.items())},
               'by_class': {str(c): dict(v) for c, v in sorted(by_class.items())}}
    json.dump(summary, open(os.path.join(DATA, 'coverage_summary.json' if sample == 1 else 'coverage_summary_sample.json'), 'w'),
              indent=1)
    print(json.dumps(summary['first'], indent=1))
    print(json.dumps(summary['applies'], indent=1))


if __name__ == '__main__':
    main()
