#!/usr/bin/env python3
"""Untrusted converter for the F3/F4 checks (Lean re-checks everything it uses).

Writes, for every class N:
  data/f34/single/c<N>.txt : one line per cell excluded by a single term (Lemma 5.1), sorted by cell:
                             `<cell> <identity> <term>`, the engine's tuples without spaces and quotes,
                             e.g. `12 (T,(0,2,3)) (T1,0,5)`; from the records of exact6/c<N>/sec/p*.sec.jsonl
                             with the key `excluded_by`;
  data/f34/pass/c<N>.txt   : one line per cell whose exclusion rests on a core: `<cell> <pass>`, pass 2 for the
                             cells certified by the second pass (alt_out.jsonl, alt3_out.jsonl, `certified: true`),
                             pass 1 for the other cells of data/f4/links/c<N>.txt;
and logs/f34/single_summary.json with the counts.
Usage: single.py EXACT_COLLECT_DIR ALT_OUT ALT3_OUT LINKS_DIR OUT_DATA_DIR SUMMARY_JSON"""
import glob, json, os, sys

src, alt1, alt3, links, out, summ = sys.argv[1:7]


def compact(s):
    return s.replace(' ', '').replace("'", '')


single = {}
for f in glob.glob(os.path.join(src, '*', 'exact6', 'c*', 'sec', 'p*.sec.jsonl')):
    c = int(f.split('/exact6/c')[1].split('/')[0])
    for line in open(f):
        if '"excluded_by"' not in line:
            continue
        r = json.loads(line)
        e = r['excluded_by']
        single.setdefault(c, []).append((r['cell'], compact(e['identity']), compact(e['term'])))
alt = set()
for fn in (alt1, alt3):
    for line in open(fn):
        r = json.loads(line)
        if r.get('certified'):
            alt.add((r['class'], r['cell']))
counts = {'single': 0, 'pass1': 0, 'pass2': 0, 'classes_single': 0}
os.makedirs(os.path.join(out, 'single'), exist_ok=True)
os.makedirs(os.path.join(out, 'pass'), exist_ok=True)
for c in range(191):
    rows = sorted(single.get(c, []))
    assert len({r[0] for r in rows}) == len(rows), c
    if rows:
        counts['classes_single'] += 1
    counts['single'] += len(rows)
    with open(os.path.join(out, 'single', f'c{c}.txt'), 'w') as fh:
        for cell, ident, term in rows:
            fh.write(f'{cell} {ident} {term}\n')
    lf = os.path.join(links, f'c{c}.txt')
    cells = sorted(int(l.split()[1]) for l in open(lf)) if os.path.exists(lf) else []
    with open(os.path.join(out, 'pass', f'c{c}.txt'), 'w') as fh:
        for cell in cells:
            p = 2 if (c, cell) in alt else 1
            counts['pass%d' % p] += 1
            fh.write(f'{cell} {p}\n')
counts['alt_records'] = len(alt)
json.dump(counts, open(summ, 'w'), indent=1)
print(json.dumps(counts))
