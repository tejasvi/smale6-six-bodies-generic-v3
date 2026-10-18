#!/usr/bin/env python3
"""Run the referee's own checkers on all stored cells; one output line per cell.
Usage: run_ref.py OUT.jsonl [NPROC]"""
import json, sys, os
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import refkit as K
import ref_lemmas as L

CLS = K.classes()


def work(c):
    D = K.RDiag(CLS[c])
    eclass = L.lemma_E_class(D)
    out = []
    with open(K.cell_files()[c]) as fh:
        for i, line in enumerate(fh):
            rec = json.loads(line)
            C = K.RCell(rec, c, i)
            e1m, e1u = L.lemma_E1(C)
            r1m, r1v = L.lemma_R1(C)
            r5 = L.lemma_R5(C)
            r6 = L.lemma_R6(C)
            q = L.lemma_Q(C)
            tl = L.lemma_T_literal(C)
            td = L.lemma_T_domination(C)
            p = L.lemma_P(C, D)
            cc = L.lemma_C(C)
            b = L.lemma_B(C, D)
            out.append(json.dumps({'class': c, 'cell': i, 'Eclass': eclass, 'E1': e1m, 'E1u': e1u, 'R1': r1m,
                                   'R1v': r1v, 'R5': r5, 'R6': r6, 'Q': q, 'Tlit': tl, 'Tdom': td, 'P': p,
                                   'C': cc, 'B': b}))
    return c, out


def main():
    outp = sys.argv[1]
    nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    files = K.cell_files()
    order = sorted(files, key=lambda c: -os.path.getsize(files[c]))
    with Pool(nproc) as pool, open(outp, 'w') as f:
        for c, lines in pool.imap_unordered(work, order):
            for l in lines:
                f.write(l + '\n')
            print(c, len(lines), flush=True)


if __name__ == '__main__':
    main()
