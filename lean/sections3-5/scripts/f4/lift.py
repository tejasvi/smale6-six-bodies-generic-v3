#!/usr/bin/env python3
"""Cofactor certificates for the distinct cores (data/f4/cores.jsonl, written by collect.py).

For each core, Singular computes lift(I, ideal(1)) over Q(m) -- ring (0,m0,...,m5) for a core of the first pass,
ring (0, the five masses other than F) for a core with fixed mass F -- with no saturation and no extra variable.
The cofactor vector is multiplied by one element of Q(m) that clears all denominators (cleardenom), the result is
mapped to Q[x, m] (masses become variables) and h = sum_i cof_i * gen_i is computed.  Python parses the cofactors
and h, clears any remaining rational numbers by one common integer, writes the certificate (format of scripts/f4/README.md) and
checks the written file exactly (certfmt.verify_cert: python-flint polynomial arithmetic, h free of the variables,
h nonzero at the point (3,5,7,11,13,17) with m_F = 1).  Files above 10 MB are gzipped (.txt.gz).
Existing certificates are skipped, so the run is resumable; one JSON record per attempt is appended to the log.

Usage: lift.py RUN_DIR [--jobs J] [--timeout S] [--memcap GB] [--minfree GB] [--only ID,ID,...|@FILE]
               [--order ORD] [--varorder canon|rev|I,J,...] [--method M] [--log PATH] [--tag TAG]
               [--maxv V] [--force] [--cores PATH]
--cores: read the cores from PATH instead of RUN_DIR/data/f4/cores.jsonl (e.g. the candidates of altcore.py).
--force: also run cores that have a certificate (the smaller of the two files is kept).
--memcap: address-space limit of each Singular process; --minfree: when available memory falls below this, the
Singular process of this run with the largest resident set is killed (status memkill, to be rerun with fewer jobs).
ORD: a Singular monomial ordering for the variables (dp, lp, Dp, or a block order such as "(dp(3),dp(5))");
--varorder rev lists the ring variables in reverse order (the certificate keeps the canonical indices).
M: lift (default; lift(I, ideal(1)) over Q(m)), liftstd or liftstd_slimgb (liftstd over Q(m), the standard basis is
a nonzero constant c, cofactors T[.,1]/c), elim or elim_slimgb (masses as ring variables with the block order
(ORD(V),dp(#masses)); liftstd gives a standard basis with elements in Q[m]; the one with fewest terms is h, and its
column of the transformation matrix gives the cofactors)."""
import json
import math
import os
import re
import resource
import shutil
import subprocess
import sys
import tempfile
import time
from fractions import Fraction
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import certfmt as CF  # noqa: E402

GZ_LIMIT = 10 * 1000 * 1000


def opt(name, default=None, conv=str):
    if name in sys.argv:
        return conv(sys.argv[sys.argv.index(name) + 1])
    return default


RUN = sys.argv[1]
JOBS = opt('--jobs', 200, int)
TMO = opt('--timeout', 1800, int)
MEMCAP = opt('--memcap', 64, int)
ORDER = opt('--order', 'dp')
VARORDER = opt('--varorder', 'canon')
METHOD = opt('--method', 'lift')
TAG = opt('--tag', '')
MAXV = opt('--maxv', 10 ** 9, int)
LOG = opt('--log', os.path.join(RUN, 'logs', 'f4', 'lift.jsonl'))
CERTS = os.path.join(RUN, 'data', 'f4', 'certs')
WORK = os.path.join(RUN, 'work')


def parse_block(block):
    """Generator block text -> (nvar, fixed, list of dicts)."""
    lines = block.strip('\n').split('\n')
    t = lines[1].split()
    nvar, fixed = int(t[3]), int(t[5])
    ng = int(lines[2].split()[1])
    gens = []
    p = 3
    for i in range(ng):
        t = lines[p].split()
        assert t[0] == 'gen' and int(t[1]) == i
        T = int(t[2])
        p += 1
        d = {}
        for _ in range(T):
            a = list(map(int, lines[p].split()))
            p += 1
            k = [0] * (CF.NMASS + nvar)
            k[:CF.NMASS] = a[1:1 + CF.NMASS]
            nx = a[1 + CF.NMASS]
            for q in range(nx):
                k[CF.NMASS + a[2 + CF.NMASS + 2 * q]] = a[3 + CF.NMASS + 2 * q]
            d[tuple(k)] = a[0]
        gens.append(d)
    return nvar, fixed, gens


def sing_poly(d, names):
    if not d:
        return '0'
    out = []
    for k in sorted(d, reverse=True):
        c = d[k]
        mon = [f'{names[j]}^{e}' if e > 1 else names[j] for j, e in enumerate(k) if e]
        a = abs(c)
        if mon:
            body = ('' if a == 1 else f'{a}*') + '*'.join(mon)
        else:
            body = str(a)
        out.append(('-' if c < 0 else '+') + body)
    s = ''.join(out)
    return s[1:] if s[0] == '+' else s


def singular_script(nvar, fixed, gens, outfile, order, varorder, method):
    xs = [f'x{j}' for j in range(nvar)]
    names = list(CF.MASSES) + xs
    ringvars = list(xs)
    if varorder == 'rev':
        ringvars = ringvars[::-1]
    elif varorder != 'canon':
        ringvars = [xs[int(j)] for j in varorder.split(',')]
        assert sorted(ringvars) == sorted(xs)
    pars = [m for k, m in enumerate(CF.MASSES) if k != fixed]
    G = len(gens)
    ideal = 'ideal I = ' + ', '.join(sing_poly(g, names) for g in gens) + ';'
    if method.startswith('elim'):
        # masses as ring variables, block order (variables first): the standard basis contains elements of Q[m]
        alg = ', SZ, "slimgb"' if method == 'elim_slimgb' else ''
        w = ','.join(['1'] * nvar + ['0'] * len(pars))
        s = [f'ring R = 0, ({",".join(ringvars + pars)}), ({order}({nvar}),dp({len(pars)}));', ideal, 'int i; int j;',
             'matrix T; module SZ;', f'ideal GB = liftstd(I, T{alg});', 'int best = 0;',
             'for (i = 1; i <= ncols(GB); i++) { if (GB[i] != 0) { if (deg(GB[i], intvec(' + w + ')) == 0) {'
             ' if (best == 0) { best = i; } else { if (size(GB[i]) < size(GB[best])) { best = i; } } } } }',
             'if (best == 0) { print("NOTUNIT"); quit; }', 'vector v0 = 0;',
             f'for (i = 1; i <= {G}; i++) {{ v0 = v0 + T[i,best]*gen(i); }}']
    else:
        s = [f'ring R = (0,{",".join(pars)}), ({",".join(ringvars)}), {order};', ideal, 'int i;']
        if method == 'lift':
            s += ['matrix T = lift(I, ideal(1));', 'vector v0 = 0;',
                  f'for (i = 1; i <= {G}; i++) {{ v0 = v0 + T[i,1]*gen(i); }}']
        elif method in ('liftstd', 'liftstd_slimgb'):
            alg = ', SZ, "slimgb"' if method == 'liftstd_slimgb' else ''
            s += ['matrix T; module SZ;', f'ideal GB = liftstd(I, T{alg});',
                  'if (size(GB) != 1 || deg(GB[1]) != 0) { print("NOTUNIT"); quit; }',
                  'vector v0 = 0;', f'for (i = 1; i <= {G}; i++) {{ v0 = v0 + T[i,1]*gen(i); }}',
                  'v0 = (1/leadcoef(GB[1])) * v0;']
        else:
            raise ValueError(method)
    s += ['vector v = cleardenom(v0);',
          f'ring S = 0, ({",".join(xs + list(CF.MASSES))}), dp;',
          'vector w = imap(R, v);', 'ideal J = imap(R, I);', 'poly h = 0;',
          f'for (i = 1; i <= {G}; i++) {{ h = h + w[i]*J[i]; }}',
          f'link L = ":w {outfile}";', 'open(L);', 'write(L, "H " + string(h));',
          f'for (i = 1; i <= {G}; i++) {{ write(L, "C " + string(i) + " " + string(w[i])); }}',
          'write(L, "END");', 'close(L);', 'quit;']
    return '\n'.join(s) + '\n'


_TERM = re.compile(r'[+-]?[^+-]+')


def parse_singular_poly(s, varidx, nv):
    s = s.replace(' ', '').replace('\n', '')
    d = {}
    if s == '0':
        return d
    for t in _TERM.findall(s):
        sign = -1 if t[0] == '-' else 1
        if t[0] in '+-':
            t = t[1:]
        coef = 1
        k = [0] * nv
        for f in t.split('*'):
            if f[0].isdigit():
                if '/' in f:
                    a, b = f.split('/')
                    coef = coef * Fraction(int(a), int(b))
                else:
                    coef = coef * int(f)
            else:
                if '^' in f:
                    nm, e = f.split('^')
                    k[varidx[nm]] += int(e)
                else:
                    k[varidx[f]] += 1
        k = tuple(k)
        d[k] = d.get(k, 0) + sign * coef
    return {k: c for k, c in d.items() if c}


def parse_output(path, nvar, G):
    varidx = {m: k for k, m in enumerate(CF.MASSES)}
    for j in range(nvar):
        varidx[f'x{j}'] = CF.NMASS + j
    nv = CF.NMASS + nvar
    recs = []
    with open(path) as fh:
        cur = None
        for ln in fh:
            ln = ln.rstrip('\n')
            if ln.startswith('H ') or ln.startswith('C ') or ln == 'END':
                if cur is not None:
                    recs.append(cur)
                cur = ln
            else:
                cur = (cur or '') + ln
        if cur is not None:
            recs.append(cur)
    if not recs or recs[-1] != 'END':
        raise ValueError('output incomplete')
    h = None
    cofs = [None] * G
    for r in recs[:-1]:
        if r.startswith('H '):
            h = parse_singular_poly(r[2:], varidx, nv)
        else:
            _, i, body = r.split(' ', 2)
            cofs[int(i) - 1] = parse_singular_poly(body, varidx, nv)
    if h is None or any(c is None for c in cofs):
        raise ValueError('missing records')
    den = 1
    for d in cofs + [h]:
        for c in d.values():
            if isinstance(c, Fraction) and c.denominator != 1:
                den = den * c.denominator // math.gcd(den, c.denominator)
    cofs = [{k: int(c * den) for k, c in d.items()} for d in cofs]
    h = {k: int(c * den) for k, c in h.items()}
    return cofs, h, den


def write_cert(path, block, cofs, h):
    with open(path, 'w') as fh:
        fh.write(block)
        for i, c in enumerate(cofs):
            for ln in CF.poly_lines(f'cof {i}', c):
                fh.write(ln + '\n')
        for ln in CF.poly_lines('h', h):
            fh.write(ln + '\n')


def limit_mem():
    cap = MEMCAP * 1024 ** 3
    resource.setrlimit(resource.RLIMIT_AS, (cap, cap))


def run_singular(script_path, out_path, tmo):
    t0 = time.time()
    with open(out_path, 'w') as fo:
        p = subprocess.Popen(['Singular', '-q', '--no-rc', script_path], stdout=fo, stderr=subprocess.STDOUT,
                             preexec_fn=limit_mem)
        with open(os.path.join(os.path.dirname(script_path), 'pid'), 'w') as fh:
            fh.write(str(p.pid))
        ru = None
        status = None
        while True:
            pid, st, r = os.wait4(p.pid, os.WNOHANG)
            if pid:
                status, ru = st, r
                break
            if time.time() - t0 > tmo:
                p.kill()
                pid, st, r = os.wait4(p.pid, 0)
                return 'timeout', time.time() - t0, r.ru_maxrss
            time.sleep(0.02 if time.time() - t0 < 2 else 0.5)
        p.returncode = os.waitstatus_to_exitcode(status)
    return ('exit%d' % p.returncode), time.time() - t0, ru.ru_maxrss


def work(core):
    cid = core['certid']
    rec = {'certid': cid, 'kind': core['kind'], 'fixed': core['fixed'], 'nvar': core['nvar'],
           'ngens': core['ngens'], 'cells': core['cells'], 'order': ORDER, 'varorder': VARORDER, 'method': METHOD,
           'timeout': TMO, 'tag': TAG}
    nvar, fixed, gens = parse_block(core['block'])
    wd = tempfile.mkdtemp(prefix=cid + '_', dir=WORK)
    try:
        out = os.path.join(wd, 'out.txt')
        script = os.path.join(wd, 'in.sing')
        with open(script, 'w') as fh:
            fh.write(singular_script(nvar, fixed, gens, out, ORDER, VARORDER, METHOD))
        st, ts, rss = run_singular(script, os.path.join(wd, 'log.txt'), TMO)
        rec['lift_s'] = round(ts, 2)
        rec['lift_maxrss_mb'] = round(rss / 1024, 1)
        log = open(os.path.join(wd, 'log.txt')).read()
        if st == 'timeout':
            rec['status'] = 'timeout'
            return rec
        if os.path.exists(os.path.join(wd, 'memkill')):
            rec['status'] = 'memkill'
            return rec
        if 'NOTUNIT' in log:
            rec['status'] = 'not_unit'
            return rec
        if '? ' in log or not os.path.exists(out):
            rec['status'] = 'singular_error'
            rec['error'] = log[-400:]
            if 'memory' in log.lower() or 'alloc' in log.lower():
                rec['status'] = 'memout'
            return rec
        t1 = time.time()
        cofs, h, den = parse_output(out, nvar, len(gens))
        rec['int_scale'] = den
        os.makedirs(CERTS, exist_ok=True)
        tmp = os.path.join(wd, cid + '.txt')
        write_cert(tmp, core['block'], cofs, h)
        rec['parse_write_s'] = round(time.time() - t1, 2)
        size = os.path.getsize(tmp)
        rec['cert_bytes'] = size
        final = os.path.join(CERTS, cid + '.txt')
        if size > GZ_LIMIT:
            subprocess.run(['gzip', '-6', tmp], check=True)
            tmp += '.gz'
            final += '.gz'
            rec['gz_bytes'] = os.path.getsize(tmp)
        t2 = time.time()
        ok, msg = CF.verify_cert(tmp, expect_id=cid)
        rec['verify_s'] = round(time.time() - t2, 2)
        rec['verify'] = msg
        rec['h_terms'] = len(h)
        rec['cof_terms'] = sum(len(c) for c in cofs)
        if ok:
            # another run may have certified the same core meanwhile: keep the smaller file
            others = [os.path.join(CERTS, cid + ext) for ext in ('.txt', '.txt.gz')]
            others = [f for f in others if os.path.exists(f)]
            mine = os.path.getsize(tmp)
            if others and min(os.path.getsize(f) for f in others) <= mine:
                rec['status'] = 'ok_not_kept'
            else:
                shutil.move(tmp, final)
                for f in others:
                    if f != final:
                        os.unlink(f)
                rec['status'] = 'ok'
        else:
            rec['status'] = 'verify_failed'
        return rec
    except Exception as e:  # report and continue
        rec['status'] = 'exception'
        rec['error'] = repr(e)[:400]
        return rec
    finally:
        shutil.rmtree(wd, ignore_errors=True)


def mem_available_gb():
    for ln in open('/proc/meminfo'):
        if ln.startswith('MemAvailable:'):
            return int(ln.split()[1]) / 1024 ** 2
    return 1e9


def watchdog(min_gb):
    """If available memory drops below min_gb, kill the Singular process of this run (exact PID, recorded by the
    worker that started it, cmdline checked) with the largest resident set; its core is logged as memkill."""
    import signal
    while True:
        time.sleep(5)
        try:
            if mem_available_gb() >= min_gb:
                continue
            best = None
            for d in os.listdir(WORK):
                wd = os.path.join(WORK, d)
                try:
                    pid = int(open(os.path.join(wd, 'pid')).read())
                    cmd = open(f'/proc/{pid}/cmdline', 'rb').read().decode(errors='replace')
                    if os.path.join(wd, 'in.sing') not in cmd:
                        continue
                    rss = 0
                    for ln in open(f'/proc/{pid}/status'):
                        if ln.startswith('VmRSS:'):
                            rss = int(ln.split()[1])
                    if best is None or rss > best[0]:
                        best = (rss, pid, wd)
                except (OSError, ValueError):
                    continue
            if best:
                open(os.path.join(best[2], 'memkill'), 'w').close()
                os.kill(best[1], signal.SIGKILL)
                print(f'watchdog: killed {best[1]} ({best[0] // 1024} MB) in {os.path.basename(best[2])}', flush=True)
                time.sleep(10)
        except Exception as e:  # keep watching
            print('watchdog error', repr(e), flush=True)


def main():
    import threading
    os.makedirs(WORK, exist_ok=True)
    threading.Thread(target=watchdog, args=(opt('--minfree', 80, int),), daemon=True).start()
    os.makedirs(os.path.dirname(LOG), exist_ok=True)
    cores = [json.loads(ln) for ln in open(opt('--cores', os.path.join(RUN, 'data', 'f4', 'cores.jsonl')))]
    only = opt('--only')
    if only:
        ids = set(open(only[1:]).read().split()) if only.startswith('@') else set(only.split(','))
        cores = [c for c in cores if c['certid'] in ids]
    done = set()
    if os.path.isdir(CERTS):
        for f in os.listdir(CERTS):
            if f.endswith('.txt') or f.endswith('.txt.gz'):
                done.add(f.split('.')[0])
    if '--force' in sys.argv:
        done = set()
    todo = [c for c in cores if c['certid'] not in done and c['nvar'] <= MAXV]
    # largest first (number of terms times number of variables), so that the long jobs start early
    todo.sort(key=lambda c: -(c['nterms'] * c['nvar']))
    print(f'nice {os.nice(0)}; {len(cores)} cores, {len(done)} certificates exist, {len(todo)} to do; '
          f'jobs {JOBS}, timeout {TMO}, order {ORDER}, varorder {VARORDER}, method {METHOD}', flush=True)
    n = 0
    with open(LOG, 'a') as lf, Pool(min(JOBS, max(1, len(todo))), maxtasksperchild=1) as pool:
        for rec in pool.imap_unordered(work, todo):
            lf.write(json.dumps(rec) + '\n')
            lf.flush()
            n += 1
            if rec['status'] != 'ok' or n % 100 == 0:
                print(n, rec['certid'], rec['status'], rec.get('lift_s'), flush=True)
    print('done', flush=True)


if __name__ == '__main__':
    main()
