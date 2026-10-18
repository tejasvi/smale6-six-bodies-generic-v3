#!/usr/bin/env python3
"""Replay of a traced Buchberger run of lean6_special's engine (`Comp.GB.Trace.traceText`: `E k I i` or
`E k S i j <mi> <mj>`, then `R c r <m>` for each reduction step `h ← h − c·x^m·g_r`, then `X s`, `g_k = s·h`) modulo P
over the system F, and the sizes of its check as a chain: element k as the cofactor identity
`g_k = s·(origin − Σ c·x^m·g_r)` over the inputs and the earlier elements, for the ancestors of the last element (a
nonzero constant). Usage: trace_chain.py SYSTEM.json INDEX TRACE P   (SYSTEM.json: a list of systems, a system a list
of polynomials [[c, [e0, …]], …]; prints the sizes)"""
import json, sys
from collections import defaultdict

NV = 17


def pack(e):
    return sum(x << (8 * v) for v, x in enumerate(e))


def read_trace(path):
    elems = []
    for line in open(path):
        t = line.split()
        if not t:
            continue
        if t[0] == 'E':
            if t[2] == 'I':
                elems.append({'org': ('I', int(t[3])), 'steps': [], 'scale': None})
            else:
                i, j = int(t[3]), int(t[4])
                mi, mj = [int(x) for x in t[5:5 + NV]], [int(x) for x in t[5 + NV:5 + 2 * NV]]
                assert len(mi) == NV and len(mj) == NV and len(t) == 5 + 2 * NV
                elems.append({'org': ('S', i, j, pack(mi), pack(mj)), 'steps': [], 'scale': None})
        elif t[0] == 'R':
            assert len(t) == 3 + NV
            elems[-1]['steps'].append((int(t[1]), int(t[2]), pack([int(x) for x in t[3:]])))
        elif t[0] == 'X':
            elems[-1]['scale'] = int(t[1])
        else:
            raise ValueError(line)
    return elems


def ancestors(elems):
    need = {len(elems) - 1}
    stack = [len(elems) - 1]
    while stack:
        k = stack.pop()
        d = elems[k]
        deps = [r for _, r, _ in d['steps']]
        if d['org'][0] == 'S':
            deps += [d['org'][1], d['org'][2]]
        for r in deps:
            assert r < k
            if r not in need:
                need.add(r)
                stack.append(r)
    return sorted(need)


def replay(F, elems, need, P):
    g = {}
    stats = {}
    for k in need:
        d = elems[k]
        h = defaultdict(int)
        if d['org'][0] == 'I':
            for c, e in F[d['org'][1]]:
                h[pack(e)] = (h[pack(e)] + c) % P
            prods = len(F[d['org'][1]])
        else:
            _, i, j, mi, mj = d['org']
            for m, c in g[i].items():
                h[m + mi] = (h[m + mi] + c) % P
            for m, c in g[j].items():
                h[m + mj] = (h[m + mj] - c) % P
            prods = len(g[i]) + len(g[j])
        for c, r, m in d['steps']:
            gr = g[r]
            for mm, cc in gr.items():
                key = mm + m
                h[key] = (h[key] - c * cc) % P
            prods += len(gr)
        s = d['scale']
        gk = {m: c * s % P for m, c in h.items() if c * s % P}
        g[k] = gk
        stats[k] = (len(gk), len(d['steps']), prods)
    return g, stats


def main():
    sys_path, idx, trace, P = sys.argv[1], int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
    F = json.load(open(sys_path))[idx]
    elems = read_trace(trace)
    need = ancestors(elems)
    g, stats = replay(F, elems, need, P)
    last = g[len(elems) - 1]
    print(f'elements {len(elems)}, ancestors of the last {len(need)}; last element {sorted(last.items())[:3]}')
    assert len(last) == 1 and list(last)[0] == 0, 'the last element is not a nonzero constant'
    terms = sum(stats[k][0] for k in need)
    steps = sum(stats[k][1] for k in need)
    prods = sum(stats[k][2] for k in need)
    big = sorted(need, key=lambda k: -stats[k][2])[:10]
    print(f'ancestors: element terms {terms:,}, reduction steps {steps:,}, term products {prods:,}')
    print('largest identities (element, terms, steps, products):', [(k,) + stats[k] for k in big])
    sizes = sorted(stats[k][0] for k in need)
    print('element sizes: median', sizes[len(sizes) // 2], 'max', sizes[-1], 'sum', sum(sizes))
    pp = sorted(stats[k][2] for k in need)
    print('products per identity: median', pp[len(pp) // 2], '90%', pp[int(0.9 * len(pp))], 'max', pp[-1])
    maxexp = max(max(((m >> (8 * v)) & 255) for v in range(NV)) for k in need for m in g[k])
    print('max exponent', maxexp)


if __name__ == '__main__':
    main()
