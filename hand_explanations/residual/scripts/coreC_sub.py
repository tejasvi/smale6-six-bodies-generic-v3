#!/usr/bin/env python3
"""Class-29 I-cores, branch by branch, restricted to the relations of one triangle (the hand proof's K= configuration):
for the branch m2 z2 + m3 z3 [+ rider] = 0 keep the relations among the bodies of T' = {2,3,5} (and the rider), for the
branch m1 w1 + m4 w4 [+ rider] = 0 those among T = {1,4,5} (and the rider): D's of the triangle, the triangle's body
equations, U or V if they belong to the triangle. Eliminate over Q[m] (masses as variables). This checks the claim
'branch => K= polynomial' with a smaller system. Output ../data/coreC_sub.txt"""
import ast, json, os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rkit as R
VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+)\b')
DV = re.compile(r'D(\d)_(\d)')


def run(script, timeout):
    path = os.path.join(R.DATA, 'work', 'coreCsub_tmp.sing')
    open(path, 'w').write(script)
    try:
        out = subprocess.run(['Singular', '-q', path], capture_output=True, text=True, timeout=timeout).stdout
    except subprocess.TimeoutExpired:
        out = 'TIMEOUT'
    os.unlink(path)
    return out


def bodies_of(name, eq):
    t = ast.literal_eval(name)
    if t[0] == 'D' and len(t) == 3:
        return {t[1], t[2]}
    if t[0] in ('z', 'w') and t[1] == 'S':
        return set(t[2]) | {int(a) for p in DV.findall(eq) for a in p}
    if t[0] == 'V':
        return set(t[1])
    if t[0] == 'U':
        return {int(a) for p in DV.findall(eq) for a in p}
    return None


def main():
    rows = [json.loads(l) for l in open(os.path.join(R.DATA, 'nolabel_cells.jsonl'))]
    seen = {}
    for r in rows:
        if r['class'] == 29 and r['hash'] not in seen:
            seen[r['hash']] = r
    f = open(os.path.join(R.DATA, 'coreC_sub.txt'), 'w')
    for h, r in seen.items():
        cr = R.core_of(29, r['cell'])
        eqs, names = cr['core_sym'], cr['names']
        idx = names.index("('I',)")
        vs_all = sorted({v for e in eqs for v in VAR.findall(e)})
        fac = run(f'ring R = 0, ({",".join(vs_all)},m0,m1,m2,m3,m4,m5), dp;\npoly Ipol = {eqs[idx]};\n'
                  'print(factorize(Ipol));\nquit;\n', 120)
        fl = [x for x in re.findall(r'_\[\d+\]=(.*)', fac) if VAR.search(x)]
        f.write(f'=== core {h} (class 29 cell {r["cell"]})\n')
        for phi in fl:
            ms = {int(x) for x in re.findall(r'm(\d)', phi)}
            tri = ({2, 3, 5} if 'X' in phi else {1, 4, 5}) | ms
            keep = []
            for n, e in zip(names, eqs):
                if n == "('I',)":
                    continue
                b = bodies_of(n, e)
                if b is not None and b <= tri:
                    keep.append((n, e))
            sub = [e for _, e in keep] + [phi]
            vs = sorted({v for e in sub for v in VAR.findall(e)})
            facs = set()
            for e in sub:
                for m in re.finditer(r'\(([XY]\d+_\d+|0)-([XY]\d+_\d+|0)\)', e):
                    facs.add(m.group(0))
            for v in vs:
                if v[0] in 'XY':
                    facs.add(v)
            s = (f'LIB "elim.lib";\nring R = 0, ({",".join(vs)},m0,m1,m2,m3,m4,m5), dp;\n'
                 f'ideal I = {",".join(sub)};\nI = sat(I, ideal({"*".join(sorted(facs))}));\n'
                 f'ideal E = eliminate(I, {"*".join(vs)});\nprint("branch: " + string(size(E)) + " generators");\n'
                 'int i; for (i = 1; i <= size(E); i++) { print(factorize(E[i])); }\nquit;\n')
            out = run(s, 900)
            f.write(f'--- branch {phi} = 0; triangle {sorted(tri)}; kept: {" ".join(n for n, _ in keep)}\n{out}\n')
            f.flush()
            print(h, phi, 'TIMEOUT' if out == 'TIMEOUT' else 'done', flush=True)
    f.close()


if __name__ == '__main__':
    main()
