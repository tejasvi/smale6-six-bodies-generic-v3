#!/usr/bin/env python3
"""Writes logs/f4/replaced_table.md: the 35 cells whose Lean check uses a core other than the one stored by the
engine's run, with both cores and the lift attempts on the stored core (from logs/f4/replaced.jsonl and
logs/f4/lift.jsonl), and whether the engine's own lift pipeline (lift_v1, index.jsonl given as
argument, optional) also replaced the core. Run from the package root. Usage: replaced_table.py [LIFT_V1_INDEX]"""
import collections, json, sys
att = collections.defaultdict(list)
for l in open('logs/f4/lift.jsonl'):
    r = json.loads(l)
    att[r['certid']].append(r)
v1 = {}
if len(sys.argv) > 1:
    for l in open(sys.argv[1]):
        r = json.loads(l)
        v1[(r['class'], r['cell'])] = r
rows = [json.loads(l) for l in open('logs/f4/replaced.jsonl')]
out = ['| class | cell | pass | stored core: certid, F, generators | certified core: certid, F, generators | attempts on the stored core | lift_v1 |',
       '|---|---|---|---|---|---|---|']
names = []
for r in sorted(rows, key=lambda r: (r['class'], r['cell'])):
    a = att.get(r['engine_certid'], [])
    parts = []
    for m in sorted(set(x['method'] for x in a)):
        xs = [x for x in a if x['method'] == m]
        to = max([x['timeout'] for x in xs if x['status'] == 'timeout'] or [0])
        mk = [x.get('lift_maxrss_mb') or 0 for x in xs if x['status'] == 'memkill']
        s = []
        if to:
            s.append(f'timeout {to:,} s')
        if mk:
            s.append(f'memory limit ({max(mk) / 1024:.0f} GB)')
        parts.append(f'{m}: ' + ', '.join(s))
    kind = 'first' if r['engine_fixed'] == -1 else 'second'
    x = v1.get((r['class'], r['cell']))
    v1s = '' if x is None else ('also replaced' if x['hash'] != x['orig_hash'] else 'same core')
    out.append(f"| {r['class']} | {r['cell']} | {kind} | `{r['engine_certid']}`, {r['engine_fixed']}, {len(r['engine_names'])} | "
               f"`{r['certid']}`, {r['fixed']}, {len(r['names'])} | {'; '.join(parts)} | {v1s} |")
    names.append(f"* {r['class']}:{r['cell']}: stored {' '.join(r['engine_names'])}; certified {' '.join(r['names'])}")
open('logs/f4/replaced_table.md', 'w').write(
    '# The 35 cells checked through a replacement core\n\n'
    'F: the mass set to 1 (-1: all six masses are parameters). Attempts: Singular `lift`, `liftstd`, `liftstd` with '
    'slimgb, and the elimination method, with the time or memory limit each reached (from `logs/f4/lift.jsonl`); no '
    'attempt on a stored core produced a certificate. lift_v1: what the engine\'s own lift pipeline '
    'did with the same cell.\n\n' + '\n'.join(out) + '\n\n## Names of the generators\n\n' + '\n'.join(names) + '\n')
print(len(rows), 'rows')
