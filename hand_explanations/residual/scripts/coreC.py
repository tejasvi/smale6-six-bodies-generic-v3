#!/usr/bin/env python3
"""No-label family C: the 13 class-29 cores containing the moment of inertia I. For each core (its first cell):
factor the initial form of I (Singular), split the core into the branches I-factor = 0, and eliminate each branch
over Q[m] (masses as ring variables; saturation by every linear factor of the core's D relations, i.e. all
separations used, and by the position coordinates). Usage: coreC.py [OUTFILE [SKIP_HASH ...]]; default output ../data/coreC.txt"""
import json, os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rkit as R

VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+)\b')


def run(script, timeout):
    path = os.path.join(R.DATA, 'work', 'coreC_tmp.sing')
    open(path, 'w').write(script)
    try:
        out = subprocess.run(['Singular', '-q', path], capture_output=True, text=True, timeout=timeout).stdout
    except subprocess.TimeoutExpired:
        out = 'TIMEOUT'
    os.unlink(path)
    return out


def main():
    rows = [json.loads(l) for l in open(os.path.join(R.DATA, 'nolabel_cells.jsonl'))]
    seen = {}
    for r in rows:
        if r['class'] == 29 and r['hash'] not in seen:
            seen[r['hash']] = r
    skip = set(sys.argv[2:]) if len(sys.argv) > 2 else set()
    outname = sys.argv[1] if len(sys.argv) > 1 else 'coreC.txt'
    f = open(os.path.join(R.DATA, outname), 'w')
    for h, r in seen.items():
        if h in skip:
            continue
        cr = R.core_of(29, r['cell'])
        eqs = cr['core_sym']
        names = cr['names']
        vs = sorted({v for e in eqs for v in VAR.findall(e)})
        # saturate by the separation factors of the D relations and by the differences appearing in the core
        facs = set()
        for e in eqs:
            for m in re.finditer(r'\(([XY]\d+_\d+|0)-([XY]\d+_\d+|0)\)', e):
                facs.add(m.group(0))
        idx = names.index("('I',)")
        sat = '*'.join(sorted(facs))
        head = (f'LIB "elim.lib";\nring R = 0, ({",".join(vs)},m0,m1,m2,m3,m4,m5), dp;\n'
                f'ideal I = {",".join(eqs)};\n')
        s1 = head + f'poly Ipol = {eqs[idx]};\nprint(factorize(Ipol));\nquit;\n'
        fac = run(s1, 120)
        f.write(f'=== core {h} (class 29 cell {r["cell"]}, {sum(1 for x in rows if x["hash"] == h)} cells)\n')
        f.write('names: ' + ' | '.join(names) + '\n')
        f.write('I: ' + eqs[idx] + '\nfactorisation of I:\n' + fac + '\n')
        # parse factors (lines like _[k]=...)
        fl = re.findall(r'_\[\d+\]=(.*)', fac)
        fl = [x for x in fl if VAR.search(x)]
        for k, phi in enumerate(fl):
            s2 = head + (f'I = I + ideal({phi});\nI = sat(I, ideal({sat}));\n'
                         f'ideal E = eliminate(I, {"*".join(vs)});\n'
                         'print("branch: " + string(size(E)) + " generators");\n'
                         'int i; for (i = 1; i <= size(E); i++) { print(factorize(E[i])); }\nquit;\n')
            out = run(s2, 900)
            f.write(f'--- branch {k + 1}: {phi} = 0\n{out}\n')
            f.flush()
            print(h, 'branch', k + 1, 'TIMEOUT' if out == 'TIMEOUT' else 'done', flush=True)
    f.close()


if __name__ == '__main__':
    main()
