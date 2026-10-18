#!/usr/bin/env python3
"""Run the referee's residual-lemma checkers on all cells. Output: one line per cell with the witnesses.
Usage: run_resid.py OUT.jsonl [NPROC]"""
import json, os, sys, random
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import refkit as K
import ref_resid as RR

rng = random.Random(20261017)
MASSES = [[rng.randint(2, 997) for _ in range(6)] for _ in range(3)]


def work(c):
    out = []
    with open(K.cell_files()[c]) as fh:
        for i, line in enumerate(fh):
            C = K.RCell(json.loads(line), c, i)
            r = {'class': c, 'cell': i, 'B0': RR.lemma_B0(C), 'K': RR.lemma_K(C), 'L': RR.lemma_L(C),
                 'R1s': RR.lemma_R1star(C), 'W3': RR.lemma_W3(C, MASSES), 'EQ2': RR.lemma_EQ2(C, MASSES),
                 'TQ': RR.lemma_TQ(C)}
            out.append(json.dumps(r, default=list))
    return c, out


def main():
    nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    files = K.cell_files()
    order = sorted(files, key=lambda c: -os.path.getsize(files[c]))
    with Pool(nproc) as pool, open(sys.argv[1], 'w') as f:
        for c, lines in pool.imap_unordered(work, order):
            for l in lines:
                f.write(l + '\n')
            print(c, len(lines), flush=True)


if __name__ == '__main__':
    main()
