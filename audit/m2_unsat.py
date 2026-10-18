"""Independent Macaulay2 check, WITHOUT saturation, of alternative cores (the statement Singular certified: the core
generates the unit ideal over Q(m') after the first mass symbol occurring in it is set to 1, as in talt.certify).
Input: the (class, cell) pairs whose Macaulay2 runs with the Rabinowitsch saturation timed out
(engine/independent/out/m2_fix1*.jsonl with m2_fix1 == 'timeout'), and the cores from the alternative-core outputs.
Usage: python3 -I m2_unsat.py OUT.jsonl WORKDIR TIMEOUT M2FIX1.jsonl [M2FIX1.jsonl ...] -- ALT.jsonl [ALT.jsonl ...]"""
import json, os, re, subprocess, sys, tempfile, time
import multiprocessing as mp

VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')
outp, work, tmo = sys.argv[1], sys.argv[2], int(sys.argv[3])
rest = sys.argv[4:]
k = rest.index('--')
fixfiles, altfiles = rest[:k], rest[k + 1:]
os.makedirs(work, exist_ok=True)


def one(item):
    eqs = item['core_sym']
    ms = sorted(set(re.findall(r'\bm\d\b', ' '.join(eqs))))
    fix = ms[0]
    eqs1 = [re.sub(r'\b%s\b' % fix, '1', e) for e in eqs]
    par = [m for m in ms if m != fix]
    vs = sorted(set(VAR.findall(' '.join(eqs1))))
    K = f'K = frac(QQ[{",".join(par)}]);' if par else 'K = QQ;'
    s = [K, f'R = K[{",".join(vs)}];', f'I = ideal({",".join(eqs1)});', 'G = gb I;',
         'print(if (1_R % I) == 0 then "UNIT" else "NOTUNIT");', 'exit 0;']
    fd, path = tempfile.mkstemp(suffix='.m2', dir=work)
    with os.fdopen(fd, 'w') as fh:
        fh.write('\n'.join(s) + '\n')
    t = time.time()
    try:
        out = subprocess.run(['nice', '-n', '10', 'M2', '--script', path], capture_output=True, text=True, timeout=tmo)
        out = out.stdout + out.stderr
    except subprocess.TimeoutExpired:
        out = 'TIMEOUT'
    dt = round(time.time() - t, 1)
    res = 'notunit' if 'NOTUNIT' in out else 'unit' if 'UNIT' in out else ('timeout' if out == 'TIMEOUT' else 'error')
    return {'class': item['class'], 'cell': item['cell'], 'fixed': fix, 'neq': len(eqs1), 'nvars': len(vs),
            'm2_unsat_fix1': res, 'seconds': dt, 'input': os.path.basename(path)}


if __name__ == '__main__':
    mp.set_start_method('fork', force=True)
    todo = set()
    for f in fixfiles:
        for l in open(f):
            if l.strip():
                r = json.loads(l)
                if r['m2_fix1'] != 'unit':
                    todo.add((r['class'], r['cell']))
    items = []
    for f in altfiles:
        for l in open(f):
            if l.strip():
                r = json.loads(l)
                if (r['class'], r['cell']) in todo:
                    items.append(r)
    print(len(todo), 'pairs,', len(items), 'cores', flush=True)
    with open(outp, 'w') as f, mp.Pool(max(1, len(items))) as pool:
        for x in pool.imap_unordered(one, items):
            f.write(json.dumps(x) + '\n')
            f.flush()
    print('done', flush=True)
