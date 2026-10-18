#!/usr/bin/env python3
"""Converts the machine-readable transcription of the 117 six-body diagrams of Chang and Chen (a JSON file with, per
diagram, its number, z_strokes, w_strokes, z_circled, w_circled; bodies 1..6 as in their figures) into the line format
read by L6F1.ChangChen (data/f1/chang_chen_117.txt):

    <number> <z-strokes> <w-strokes> <z-circled> <w-circled>

strokes as comma-separated pairs `ab` (a < b), circled bodies as a string of digits, `-` for an empty list.
The Lean side re-reads the file and writes it back identically before using it. Usage: cc_convert.py IN.json OUT.txt"""
import hashlib, json, sys

src = sys.argv[1]
raw = open(src, 'rb').read()
d = json.loads(raw)
lines = ['# The 117 diagrams of Chang and Chen (arXiv:2303.02853v1, Figs. 3-6), bodies 1..6 as in the figures.',
         '# Converted by scripts/f1/cc_convert.py from a transcription with SHA-256 '
         + hashlib.sha256(raw).hexdigest() + '.',
         '# number z-strokes w-strokes z-circled w-circled']


def pairs(ps):
    ps = sorted((min(a, b), max(a, b)) for a, b in ps)
    return ','.join(f'{a}{b}' for a, b in ps) if ps else '-'


def bodies(ks):
    return ''.join(str(k) for k in sorted(ks)) if ks else '-'


for x in d['diagrams']:
    lines.append(f"{x['number']} {pairs(x['z_strokes'])} {pairs(x['w_strokes'])} "
                 f"{bodies(x['z_circled'])} {bodies(x['w_circled'])}")
open(sys.argv[2], 'w').write('\n'.join(lines) + '\n')
print(len(d['diagrams']), 'diagrams written')
