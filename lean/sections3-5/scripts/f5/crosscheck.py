#!/usr/bin/env python3
"""Compares the Lean census (the output of L6Check/F5/Print.lean in a build log) with the census program of the paper.
Usage: crosscheck.py BUILD_LOG REF_PERCELL REF_CENSUS AUDIT_CENSUS NOTE_PER_CLASS_JSON
  REF_PERCELL   per-cell output of scripts/f5/percell_ref.py (lines `none c k`, `four c k`, totals)
  REF_CENSUS    output of the census program (tools/clique_census.py) on the embedded data
  AUDIT_CENSUS  the published output of the census program (audit/clique_census.txt)
  NOTE_PER_CLASS_JSON  per-class counts {class: [cells, with a clique, ...]} of the conceptual note's run
Prints the comparisons (file names only)."""
import json, os, re, sys
log, ref_pc, ref_c, audit_c, note = sys.argv[1:6]
lines = [re.sub(r'^info: \S+ ', '', l.rstrip('\n')) for l in open(log)]
lean_pc = [l for l in lines if re.match(r'^(none|four) \d+ \d+$', l)]
ref = [l.rstrip('\n') for l in open(ref_pc) if re.match(r'^(none|four) \d+ \d+$', l)]
print(f'Lean per-cell lines: {len(lean_pc)} (none {sum(l.startswith("none") for l in lean_pc)}, '
      f'four {sum(l.startswith("four") for l in lean_pc)}); program per-cell lines: {len(ref)} '
      f'(none {sum(l.startswith("none") for l in ref)}, four-only {sum(l.startswith("four") for l in ref)})')
print('per-cell lists identical (same order):', lean_pc == ref)
print(f'program output on the embedded data identical to {os.path.basename(audit_c)}:',
      open(ref_c).read() == open(audit_c).read())
rows = {}
for l in lines:
    m = re.match(r'^(\d+) (\d+) (\d+) (\d+) (\d+) (\d+)$', l)
    if m:
        v = list(map(int, m.groups()))
        rows[v[0]] = v[1:]
nt = json.load(open(note))
diff = [c for c in range(191) if rows[c][:2] != nt[str(c)][:2]]
print(f'classes compared with the note\'s per-class counts: {len(rows)}; differing in (cells, with a clique): {diff}')
tot = [sum(r[i] for r in rows.values()) for i in range(5)]
print(f'Lean totals: cells {tot[0]}, clique {tot[1]}, three {tot[2]}, four {tot[3]}, forced {tot[4]}')
