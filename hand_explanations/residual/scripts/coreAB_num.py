#!/usr/bin/env python3
"""Sanity check of the core-level shapes of no-label families A and B on the engine's actual core equations:
unit ideal over Q at random rational masses and, for family A, also at masses with m_a = m_b (the EQ branch is
excluded there by X_s != 0). Saturation by all coordinate differences occurring in the core. -> ../data/coreAB_num.txt"""
import json, os, re, subprocess, sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rkit as R
VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+)\b')
FAMA = {'96674494358ac0b5': (1, 3), '7c60897cf0a47385': (1, 3), '6fd2e5810bbf2a5f': (0, 5),
        '9a753c1a541ced1d': (0, 5), 'ba6b8555b3facbb0': (2, 4), '1e2248294818e876': (2, 3)}   # (a, b)
FAMB = ['d3b647872447c0ef', 'ea7e65c885fdd88f', '30705e67c1c7941d', '647a7fee9b065071', '42bfa6378df9869d',
        '3ad43983ec3bb804']


def unit(eqs, masses, tag):
    vs = sorted({v for e in eqs for v in VAR.findall(e)})
    facs = set()
    for e in eqs:
        for m in re.finditer(r'\(([XY]\d+_\d+|0)-([XY]\d+_\d+|0)\)', e):
            facs.add(m.group(0))
    sub = []
    for e in eqs:
        for k in range(6):
            e = e.replace(f'(m{k})', f'({masses[k]})')
        sub.append(e)
    s = (f'LIB "elim.lib";\nring R = 0, ({",".join(vs)}), dp;\nideal I = {",".join(sub)};\n'
         f'I = sat(I, ideal({"*".join(sorted(facs))}));\nideal G = std(I);\nprint("DIM " + string(dim(G)));\nquit;\n')
    path = os.path.join(R.DATA, 'work', f'coreAB_{tag}.sing')
    open(path, 'w').write(s)
    try:
        out = subprocess.run(['Singular', '-q', path], capture_output=True, text=True, timeout=900).stdout
    except subprocess.TimeoutExpired:
        out = 'TIMEOUT'
    os.unlink(path)
    m = re.search(r'DIM (-?\d+)', out)
    return int(m.group(1)) if m else out[-200:]


def main():
    rows = [json.loads(l) for l in open(os.path.join(R.DATA, 'nolabel_cells.jsonl'))]
    first = {}
    for r in rows:
        first.setdefault(r['hash'], r)
    rng = random.Random(2)
    f = open(os.path.join(R.DATA, 'coreAB_num.txt'), 'w')
    for h in list(FAMA) + FAMB:
        r = first[h]
        cr = R.core_of(r['class'], r['cell'])
        eqs = cr['core_sym']
        res = []
        for t in range(2):
            ms = [rng.randint(2, 30) for _ in range(6)]
            res.append(('random', ms, unit(eqs, ms, f'{h}_{t}')))
        if h in FAMA:
            a, b = FAMA[h]
            ms = [rng.randint(2, 30) for _ in range(6)]
            ms[b] = ms[a]
            res.append(('m_a=m_b', ms, unit(eqs, ms, f'{h}_eq')))
        line = f'{h} (class {r["class"]} cell {r["cell"]}, family {"A" if h in FAMA else "B"}): ' + \
               '; '.join(f'{k} {m}: dim {d}' for k, m, d in res)
        f.write(line + '\n')
        print(line, flush=True)


if __name__ == '__main__':
    main()
