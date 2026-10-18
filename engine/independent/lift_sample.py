#!/usr/bin/env python3
"""Feasibility of explicit certificates for the cores (toward removing the Groebner engines from the trusted base):
for a random sample of distinct certified cores, Singular's lift gives cofactors C_i in Q(m)[v, t] with
sum C_i g_i = 1 for g = core equations + (t * prod(saturating factors) - 1); Macaulay2 then checks the identity by plain
polynomial arithmetic. Reports times and certificate sizes.
Usage: lift_sample.py RECERT.jsonl OUT.jsonl [--n N] [--seed S] [--timeout T]"""
import json, os, random, re, subprocess, sys, tempfile, time
import multiprocessing as mp

args = sys.argv[1:]
N = int(args[args.index('--n') + 1]) if '--n' in args else 40
seed = int(args[args.index('--seed') + 1]) if '--seed' in args else 1
tmo = int(args[args.index('--timeout') + 1]) if '--timeout' in args else 600
rec, outp = args[0], args[1]
work = os.path.join(os.path.dirname(os.path.abspath(outp)), 'lift_tmp')
os.makedirs(work, exist_ok=True)


def run(cmd, text, suffix):
    fd, path = tempfile.mkstemp(suffix=suffix, dir=work)
    with os.fdopen(fd, 'w') as fh:
        fh.write(text)
    t = time.time()
    try:
        out = subprocess.run(['nice', '-n', '10'] + cmd + [path], capture_output=True, text=True, timeout=tmo)
        out = out.stdout + out.stderr
    except subprocess.TimeoutExpired:
        out = 'TIMEOUT'
    os.unlink(path)
    return out, time.time() - t


def one(it):
    vs = [f'v{i}' for i in range(it['nv'])] + ['tRab']
    prod = '*'.join(it['csats']) if it['csats'] else '1'
    gens = it['ceqs'] + [f'tRab*{prod}-1']
    s = [f'ring R = (0,m0,m1,m2,m3,m4,m5), ({",".join(vs)}), dp;', f'ideal J = {",".join(gens)};',
         'matrix T = lift(J, ideal(1));', 'int i;',
         'for (i = 1; i <= ncols(J); i++) { print("C" + string(i) + " = " + string(T[i,1]) + ";"); }', 'quit;']
    out, ts = run(['Singular', '-q'], '\n'.join(s) + '\n', '.sing')
    res = {'class': it['class'], 'hash': it['hash'], 'neq': len(it['ceqs']), 'lift_s': round(ts, 1)}
    if out == 'TIMEOUT' or 'C1 =' not in out:
        res['lift'] = 'timeout' if out == 'TIMEOUT' else 'error'
        return res
    res['cert_bytes'] = len(out)
    m2 = ['K = frac(QQ[m0,m1,m2,m3,m4,m5]);', f'R = K[{",".join(vs)}];', 'J = {' + ','.join(gens) + '};', out,
          'S = ' + ' + '.join(f'C{i + 1}*J#{i}' for i in range(len(gens))) + ';',
          'print(if S == 1_R then "LIFT_IDENTITY_OK" else "LIFT_IDENTITY_FAIL");', 'exit 0;']
    o2, t2 = run(['M2', '--script'], '\n'.join(m2) + '\n', '.m2')
    res['verify_s'] = round(t2, 1)
    res['lift'] = 'ok' if 'LIFT_IDENTITY_OK' in o2 else ('FAIL' if 'LIFT_IDENTITY_FAIL' in o2 else
                                                         ('verify_timeout' if o2 == 'TIMEOUT' else 'verify_error'))
    return res


if __name__ == '__main__':
    mp.set_start_method('fork', force=True)
    items = [json.loads(l) for l in open(rec)]
    items = [it for it in items if it['stored_dim'] == -1]
    random.Random(seed).shuffle(items)
    items = items[:N]
    with open(outp, 'w') as f, mp.Pool(min(20, N)) as pool:
        for r in pool.imap_unordered(one, items):
            f.write(json.dumps(r) + '\n')
            f.flush()
    print('done', flush=True)
