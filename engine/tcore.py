#!/usr/bin/env python3
"""Minimal inconsistent cores of excluded cells (QuickXplain over the equations; Singular mod p; the saturations are
always kept). Input: tsec.py output with --dump. Output: per cell the core (identity names and equations).
Usage: tcore.py SEC_DUMP.jsonl OUT.jsonl [--prime P] [--max K]"""
import json, sys, os
sys.path.insert(0, '.')
import tinit as I


TLIM = 20


def inconsistent(vars_, eqs, sats, prime, workdir):
    """True if the system is the unit ideal; a timeout counts as consistent."""
    if not eqs:
        return False
    blk = I.singular_block(0, vars_, eqs, sats, prime)
    r = I.run_batch([blk], workdir, timeout=TLIM)
    return r.get(0) == -1


def quickxplain(vars_, background, cand, sats, prime, workdir, stats):
    """A minimal subset C of cand with background + C inconsistent (background + cand is inconsistent)."""
    def qx(B, delta_added, C):
        if delta_added and B:
            stats['calls'] += 1
            if inconsistent(vars_, B, sats, prime, workdir):
                return []
        if len(C) == 1:
            return C
        k = len(C) // 2
        C1, C2 = C[:k], C[k:]
        D2 = qx(B + C1, True, C2)
        D1 = qx(B + D2, bool(D2), C1)
        return D1 + D2
    return qx(background, False, cand)


if __name__ == '__main__':
    inp, outp = sys.argv[1], sys.argv[2]
    prime = int(sys.argv[sys.argv.index('--prime') + 1]) if '--prime' in sys.argv else 32003
    mx = int(sys.argv[sys.argv.index('--max') + 1]) if '--max' in sys.argv else 10**9
    workdir = os.path.dirname(os.path.abspath(outp))
    with open(outp, 'w') as f:
        for li, line in enumerate(open(inp)):
            if li >= mx:
                break
            r = json.loads(line)
            if r.get('dim') != -1 or 'system' not in r:
                continue
            S = r['system']
            idx = list(range(len(S['eqs'])))
            stats = {'calls': 0}
            pre = os.environ.get('TCORE_PRECHECK')
            if pre:
                blk = I.singular_block(0, S['vars'], S['eqs'], S['sats'], prime)
                rr = I.run_batch([blk], workdir, timeout=float(pre))
                if rr.get(0) is not None and rr.get(0) != -1:
                    f.write(json.dumps({'cell': r['cell'], 'consistent': True, 'dim': rr.get(0), 'sumx': r['sumx']}) + '\n')
                    f.flush()
                    continue
            # local equations first: sort by the number of variables they involve
            order = sorted(idx, key=lambda i: len(set(t for t in S['vars'] if t in S['eqs'][i])))
            idx = order
            core = quickxplain(S['vars'], [], [S['eqs'][i] for i in idx], S['sats'], prime, workdir, stats)
            cidx = [S['eqs'].index(e) for e in core]
            names = [S['names'][i] for i in cidx]
            rec = {'cell': r['cell'], 'core_size': len(core), 'names': names, 'core': core, 'idx': cidx,
                   'calls': stats['calls'], 'sumx': r['sumx']}
            if 'eqs_sym' in S:
                rec['core_sym'] = [S['eqs_sym'][i] for i in cidx]
            # the core must be inconsistent at the random masses (QuickXplain's last check may have timed out)
            rec['verified_modp'] = inconsistent(S['vars'], core, S['sats'], prime, workdir)
            f.write(json.dumps(rec) + '\n')
            f.flush()
            print(r['cell'], len(core), names, stats['calls'], flush=True)
