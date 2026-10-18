#!/usr/bin/env python3
"""Markdown tables for RESIDUAL.md from data/resid_cover.jsonl, data/algebra_resid.jsonl, data/global_cover*.
Output ../data/tables_resid.md"""
import json, os, sys
from collections import Counter, defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rkit as R

ORDER = ['B0', 'K', 'L', 'TD', 'R1*', 'W3', 'EQ2', 'TQ']
ALLMASS = {'B0', 'K', 'L', 'TD'}


def main():
    cover = [json.loads(l) for l in open(os.path.join(R.DATA, 'resid_cover.jsonl'))]
    alg = {(r['class'], r['cell']): r for r in (json.loads(l) for l in open(os.path.join(R.DATA, 'algebra_resid.jsonl')))}
    out = []
    # chosen lemma: every-mass lemma first, then generic
    chosen = {}
    for r in cover:
        app = r['applies']
        st = next((k for k in ORDER if k in app), None)
        chosen[(r['class'], r['cell'])] = st
    out.append('## Residual cells: chosen lemma (every-mass lemmas preferred)\n')
    out.append('| class (CC) | diagram | cells | kind | engine label | chosen lemma | masses | other lemmas that apply |')
    out.append('|---|---|---|---|---|---|---|---|')
    grp = defaultdict(list)
    for r in cover:
        key = (r['class'], r['kind'], r['label'], chosen[(r['class'], r['cell'])])
        grp[key].append(r)
    cc = {}
    for l in open(os.path.join(R.MECH, 'data', 'per_class_table.md')):
        parts = [p.strip() for p in l.split('|')]
        if len(parts) > 3 and parts[1].isdigit():
            cc[int(parts[1])] = parts[2]
    tot = Counter()
    for key in sorted(grp, key=lambda k: (ORDER.index(k[3]), k[0])):
        rs = grp[key]
        c, kind, label, st = key
        others = Counter(a for r in rs for a in r['applies'] if a != st)
        masses = 'every positive' if st in ALLMASS else 'generic'
        out.append(f'| {c} ({cc.get(c, "?")}) | {R.diag_str(c)} | {len(rs)} | {kind} | {label or "-"} | {st} | {masses} | '
                   + ', '.join(f'{a} ({n})' for a, n in sorted(others.items())) + ' |')
        tot[st] += len(rs)
        tot['allmass' if st in ALLMASS else 'generic'] += len(rs)
    out.append('')
    out.append('Totals: ' + ', '.join(f'{k} {tot[k]}' for k in ORDER if tot[k]) +
               f'; every positive mass {tot["allmass"]}, generic {tot["generic"]}.')
    out.append('')
    # algebra
    out.append('## Mass conditions of the generic lemmas (per cell)\n')
    out.append('| class | cells | lemma | roles | degree | nonzero | positive sign change | engine label |')
    out.append('|---|---|---|---|---|---|---|---|')
    g2 = defaultdict(list)
    for r in cover:
        a = alg.get((r['class'], r['cell']))
        if not a or a['first'] not in ('R1*', 'W3', 'EQ2', 'TQ', 'L'):
            continue
        roles = json.dumps(a.get('roles'), sort_keys=True)
        g2[(r['class'], a['first'], roles, a.get('degree'), a.get('nonzero'), a.get('positive_sign_change'),
            a.get('engine_label_compare'))].append(r['cell'])
    for k, cells in sorted(g2.items()):
        c, f, roles, deg, nz, ps, cmp_ = k
        out.append(f'| {c} | {len(cells)} | {f} | `{roles}` | {deg} | {nz} | {ps} | {cmp_} |')
    out.append('')
    gs = os.path.join(R.DATA, 'global_cover_summary.json')
    if os.path.exists(gs):
        s = json.load(open(gs))
        out.append('## Global run (all 91,273 cells)\n')
        out.append('```')
        out.append(json.dumps(s, indent=1))
        out.append('```')
    open(os.path.join(R.DATA, 'tables_resid.md'), 'w').write('\n'.join(out) + '\n')
    print('\n'.join(out[:60]))


if __name__ == '__main__':
    main()
