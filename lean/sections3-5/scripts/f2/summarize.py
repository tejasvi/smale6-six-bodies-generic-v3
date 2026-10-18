#!/usr/bin/env python3
"""Summarizes a lake build log of the F2 checks: per-module build times (logs/f2/modules.tsv), the axioms printed by
L6Check/F2/Axioms.lean (logs/f2/axioms.log, with a check that every axiom is propext, Quot.sound, Classical.choice or
the auxiliary axiom of a `native_decide` theorem), and a short summary on stdout.
Usage: summarize.py LAKE_LOG OUT_DIR"""
import re, sys

log, out = sys.argv[1], sys.argv[2]
text = open(log, encoding='utf-8', errors='replace').read()
mods = []
for m in re.finditer(r'Built (\S+) \(([\d.]+)(ms|s)\)', text):
    t = float(m.group(2)) / (1000 if m.group(3) == 'ms' else 1)
    mods.append((m.group(1), t))
with open(f'{out}/modules.tsv', 'w') as f:
    f.write('module\tseconds\n')
    for name, t in sorted(mods, key=lambda x: -x[1]):
        f.write(f'{name}\t{t:.3f}\n')
checks = [(n, t) for n, t in mods if n.startswith('L6Check.F2.') and ':' not in n]
# axioms
ax_lines = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S)
std = {'propext', 'Quot.sound', 'Classical.choice'}
bad = []
with open(f'{out}/axioms.log', 'w') as f:
    for name, axs in ax_lines:
        axs = [a.strip() for a in axs.replace('\n', ' ').split(',') if a.strip()]
        nat = [a for a in axs if re.fullmatch(r'[\w.]+\._native\.native_decide\.ax_\d+_\d+', a)]
        other = [a for a in axs if a not in std and a not in nat]
        f.write(f'{name}: standard {sorted(set(axs) & std)}, native_decide auxiliary axioms {len(nat)}, other {other}\n')
        if other:
            bad.append((name, other))
errors = len(re.findall(r'error:', text))
print(f'modules built: {len(mods)}; check modules: {len(checks)}; CPU of check modules: '
      f'{sum(t for _, t in checks):.0f} s; longest: {max(checks, key=lambda x: x[1]) if checks else None}; '
      f'errors: {errors}; theorems with axioms printed: {len(ax_lines)}; non-standard axioms: {bad}')
