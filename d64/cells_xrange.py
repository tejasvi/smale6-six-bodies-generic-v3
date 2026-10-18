# Range of the K4 exponent x and of sum x over each open cell (engine LP, read-only use of engine code; run with -B).
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'engine'))
import tengine as T, tsec
D6 = json.load(open(os.path.join(HERE, '..', 'diagrams', 'n6.json')))
def run(cls, path, cells, kpair):
    c = D6['classes'][cls]
    D = T.Diagram.from_json(6, c)
    L = [json.loads(l) for l in open(path)]
    for i in cells:
        d = L[i]
        zt = tsec.tree_from_json(6, d['ztree']); wt = tsec.tree_from_json(6, d['wtree'])
        lp = tsec.cell_lp(D, zt, wt, d['argmin'])
        def xform(k, l):
            f = {}
            for tr, V in ((zt, lp.zv), (wt, lp.wv)):
                m = tr.meet(k, l)
                f[V[m]] = f.get(V[m], 0) + 0.5
            return f
        fx = xform(*kpair)
        fs = {}
        for k in range(6):
            for l in range(k+1, 6):
                for j, cf in xform(k, l).items(): fs[j] = fs.get(j, 0) + cf
        out = []
        for f in (fx, fs):
            ok1, lo, _ = lp.solve(obj=f, sense_max=False, smin=1e-7)
            ok2, hi, _ = lp.solve(obj=f, sense_max=True, smin=1e-7)
            out.append((round(lo, 6) if ok1 else None, round(hi, 6) if ok2 else None))
        print(cls, i, 'x range', out[0], 'sumx range', out[1])
run(124, os.path.join(HERE, '..', 'results', 'exact6', 'c124', 'cells.jsonl'), [0,16,17,30,46,83,105,109,110,111,121], (1,2))
run(143, os.path.join(HERE, '..', 'results', 'exact6', 'c143', 'cells.jsonl'), [3,13,14,23,29,35,47,53,59,65,71], (1,2))
