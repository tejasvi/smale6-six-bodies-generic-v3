"""Coverage of the cells by the hand lemmas of Section 9 (Proposition 9.23), from two independent classifications.

Usage: python3 -I -B hand_coverage.py REFEREE_CLASS AUTHORS_TIERS CONCEPT_SCRIPTS ENGINE_RUNS PER_CLASS GENERIC_OPEN
       AUTHORS_COVERAGE

REFEREE_CLASS  final_classification.jsonl of the independent re-implementation (one line per cell: tier, the every-mass
               and generic cell-level lemmas whose hypotheses hold, template, secondary identity, d-class);
AUTHORS_TIERS  tiers_v2.jsonl of the notes (the same per-cell data, computed by the notes' own checkers);
CONCEPT_SCRIPTS, ENGINE_RUNS  as for clique_census.py (the census of Corollary 9.18, recomputed here per cell);
PER_CLASS      audit/per_class.tsv (class -> Chang-Chen number);
GENERIC_OPEN   the 43 cells of Proposition 5.3 (tab-separated class, CC, cell);
AUTHORS_COVERAGE  coverage.jsonl of the notes (for the minors of Lemma LIN in the template cells).

Lemma names in the classifications and in the paper: T, P, C, B0, K, L = Lemmas 9.2-9.7 (every positive mass; B is
dropped, see the check below); E1 = Corollary 9.10 (E its class-level case), R1 and R1s = R1*(alpha/beta) = Lemma
9.11(a), (b); R6, W3, EQ2, Q = Lemmas 9.12-9.15 (generic); R1*gamma = Lemma 9.11(c) and TQ = Lemma 9.22 (one certified
secondary identity each); coreP4 and coreLIN-* = Lemmas 9.20 and 9.21; TD = Lemma 5.1 with a certified torque (class
15 cell 0). The clique census is that of Proposition 9.19 (Corollary 9.18).
"""
import glob, json, re, sys
from collections import Counter

ref_path, aut_path, concept, runs, per_class, open_path, cov_path = sys.argv[1:8]

ref = {}
for line in open(ref_path):
    r = json.loads(line)
    ref[(r['class'], r['cell'])] = r
aut = {}
for line in open(aut_path):
    r = json.loads(line)
    aut[(r['class'], r['cell'])] = r
cc = {}
for line in open(per_class):
    f = line.rstrip('\n').split('\t')
    if not f[0].isdigit():
        continue
    cc[int(f[0])] = f[1]
open43 = set()
for line in open(open_path):
    f = line.rstrip('\n').split('\t')
    if line.startswith('#') or len(f) < 3:
        continue
    open43.add((int(f[0]), int(f[2])))

print('cells: referee %d, notes %d, same keys: %s' % (len(ref), len(aut), set(ref) == set(aut)))
assert set(ref) == set(aut) and len(ref) == 91273

# 1. Tiers, cell by cell.
tier = {k: r['tier'].split()[0] for k, r in ref.items()}
same_tier = sum(tier[k] == aut[k]['tier'] for k in ref)
print('tiers (referee):', dict(sorted(Counter(tier.values()).items())))
print('tiers (notes):  ', dict(sorted(Counter(a['tier'] for a in aut.values()).items())))
print('tier equal cell by cell: %d of %d' % (same_tier, len(ref)))
ren = {'R1s': 'R1*'}
agree_all = sum(sorted(ref[k]['cell_level_allmass']) == sorted(aut[k]['cell_level_allmass']) for k in ref)
print('every-mass lemma sets equal cell by cell: %d of %d' % (agree_all, len(ref)))
gen_diff = Counter()
for k in ref:
    a = set(ren.get(x, x) for x in ref[k]['cell_level_generic'])
    b = set(aut[k]['cell_level_generic'])
    if a != b:
        gen_diff[(tuple(sorted(a - b)), tuple(sorted(b - a)))] += 1
print('generic lemma sets: differences (referee only, notes only):', dict(gen_diff))
w3_only = [k for k in ref if set(ref[k]['cell_level_generic']) == {'W3'} and not ref[k]['cell_level_allmass']]
print('cells whose only cell-level lemma is W3: %d, classes %s; the notes flag W3 there: %s'
      % (len(w3_only), dict(Counter(k[0] for k in w3_only)), all('W3' in aut[k]['cell_level_generic'] for k in w3_only)))
eq2_only = [k for k in ref if set(ref[k]['cell_level_generic']) == {'EQ2'} and not ref[k]['cell_level_allmass']]
print('cells whose only cell-level lemma is EQ2: %d, classes %s' % (len(eq2_only), dict(sorted(Counter(k[0] for k in eq2_only).items()))))

# 2. Every positive mass.
EM = ['T', 'P', 'C', 'B0', 'K', 'L']
allm = {k for k in ref if ref[k]['cell_level_allmass']}
allm_noB = {k for k in ref if set(ref[k]['cell_level_allmass']) - {'B'}}
print('\nEVERY POSITIVE MASS')
print('per lemma:', {x: sum(x in ref[k]['cell_level_allmass'] for k in ref) for x in EM + ['B']})
print('cell-level (T,P,C,B,B0,K,L): %d; without B: %d' % (len(allm), len(allm_noB)))
cum, seen = [], set()
for x in EM:
    seen |= {k for k in ref if x in ref[k]['cell_level_allmass']}
    cum.append((x, len(seen)))
print('cumulative T,P,C,B0,K,L:', cum)
a2 = Counter(ref[k]['template'] for k in ref if tier[k] == 'A2')
a3 = [k for k in ref if tier[k] == 'A3']
print('A2 (templates P4/LIN, certified secondary identities):', sum(a2.values()), dict(a2))
print('A3 (Lemma 5.1 with a certified torque):', a3)
print('every positive mass total: %d' % (len(allm_noB) + sum(a2.values()) + len(a3)))
single = {k for k in ref if ref[k]['kind'] == 'single'}
Aset = allm_noB | {k for k in ref if tier[k] in ('A2', 'A3')}
d89 = {k for k in ref if cc.get(k[0]) == '89'}
d82 = {k for k in ref if cc.get(k[0]) == '82'}
d90 = {k for k in ref if cc.get(k[0]) == '90'}
print('single-term cells (Lemma 5.1, every positive mass): %d; not in (a): %d %s; diagram 89 cells: %d, not in (a) or single: %d'
      % (len(single), len(single - Aset), dict(Counter(tier[k] for k in single - Aset)), len(d89), len(d89 - Aset - single)))
print('diagram 82 cells (Proposition 6.7): %d, not in (a), single or diagram 89: %d %s; diagram 90 cells (Proposition 6.4): %d, not in (a) or single: %d'
      % (len(d82), len(d82 - Aset - single - d89), sorted(d82 - Aset - single - d89), len(d90), len(d90 - Aset - single)))
print('every positive mass with Lemma 5.1 on all single-term cells, Theorem 6.5, Propositions 6.4 and 6.7: %d' % len(Aset | single | d89 | d82 | d90))

# 3. Generic masses.
cell_level = {k for k in ref if ref[k]['cell_level_allmass'] or ref[k]['cell_level_generic']}
extra = sorted(k for k in cell_level if tier[k] not in ('A1', 'G1'))
print('\nGENERIC MASSES')
print('cell-level hand lemmas (any): %d; of them outside tiers A1, G1: %s' % (len(cell_level), [(k, tier[k], ref[k]['cell_level_generic']) for k in extra]))
sec_only = [k for k in ref if k not in cell_level and tier[k] != 'D']
kind = Counter()
for k in sec_only:
    r = ref[k]
    kind[r['secondary'] or r['template'] or 'TD'] += 1
print('only lemmas with certified secondary identities: %d %s' % (len(sec_only), dict(kind)))
D = sorted(k for k in ref if tier[k] == 'D')
print('only Sections 6-7: %d' % len(D), {('class %d' % c, 'CC' + cc[c]): n for c, n in sorted(Counter(k[0] for k in D).items())})
print('  cells:', D)
print('  of Proposition 5.3\'s 43 open cells: %d in this set; open cells with a hand lemma: %s; cells here that are not open: %s'
      % (len(set(D) & open43), sorted((k, ref[k]['cell_level_allmass'] + ref[k]['cell_level_generic'], ref[k]['template']) for k in open43 - set(D)),
         sorted(set(D) - open43)))
print('total: %d + %d + %d = %d' % (len(cell_level), len(sec_only), len(D), len(cell_level) + len(sec_only) + len(D)))
GEN = [('E1', {'E1', 'E'}), ('R', {'R1', 'R1s'}), ('R6', {'R6'}), ('Q', {'Q'}), ('W3', {'W3'}), ('EQ2', {'EQ2'})]
print('per lemma (generic):', {x: sum(bool(set(ref[k]['cell_level_generic']) & s) for k in ref) for x, s in GEN},
      {x: sum(x in ref[k]['cell_level_generic'] for k in ref) for x in ['E', 'R1', 'R1s', 'R5']})
cum, seen = [], set()
for x, s in GEN:
    seen |= {k for k in ref if set(ref[k]['cell_level_generic']) & s}
    cum.append((x, len(seen)))
seen |= allm_noB
cum.append(('+ every-mass lemmas', len(seen)))
print('cumulative E1, R, R6, Q, W3, EQ2, then T..L:', cum)
e_in_e1 = all('E1' in ref[k]['cell_level_generic'] for k in ref if 'E' in ref[k]['cell_level_generic'])
r1_in_r = all('R1s' in ref[k]['cell_level_generic'] for k in ref if 'R1' in ref[k]['cell_level_generic'])
print('E cells all have E1: %s; R1 cells all have R1*(alpha/beta): %s' % (e_in_e1, r1_in_r))
print('E classes:', sorted({k[0] for k in ref if 'E' in ref[k]['cell_level_generic']}),
      'CC', sorted({cc[k[0]] for k in ref if 'E' in ref[k]['cell_level_generic']}, key=int),
      'cells', sum('E' in ref[k]['cell_level_generic'] for k in ref))

# LIN minors in the template cells without a cell-level lemma (tiers A2 and G3).
cov = {}
for line in open(cov_path):
    r = json.loads(line)
    cov[(r['class'], r['cell'])] = r
lin = [k for k in ref if (ref[k]['template'] or '').startswith('coreLIN') and k not in cell_level]
pts = [dict(('m%d' % j, v) for j, v in enumerate(p)) for p in ((1, 2, 3, 4, 5, 6), (3, 1, 4, 1, 5, 9), (2, 7, 1, 8, 2, 8))]
bad = []
for k in lin:
    fam = cov[k]['core_fam']
    assert fam[0] == 'LIN', (k, fam)
    if not any(any(eval(f, {'__builtins__': {}}, pt) != 0 for pt in pts) for f in fam[1]):
        bad.append(k)
print('LIN cells without a cell-level lemma: %d (tiers %s); some minor nonzero at one of three points in all: %s %s'
      % (len(lin), dict(Counter(tier[k] for k in lin)), not bad, bad))
print('  the every-mass LIN cell(s):', [(k, cov[k]['core_fam'][1]) for k in lin if tier[k] == 'A2'])

# 4. Comparison with the census of Corollary 9.18 (Proposition 9.19).
sys.path.insert(0, concept)
import cliques as CQ
import zwexcess as ZX
import cell_killers as CK
clique, clique3 = set(), set()
for fpath in sorted(glob.glob(runs + '/*/exact6/c*/cells.jsonl')):
    ci = int(re.search(r'/c(\d+)/cells', fpath).group(1))
    c = CQ.cls[ci]
    zwk = any((e['r'] == 3 and e['excess'] >= 1) or (e['r'] == 4 and e['dz'] == 0 and e['dw'] == 0)
              for e in ZX.excess(c))
    its = [it for it in CQ.info(c) if it['kind'] in ('z', 'w') and len(it['K']) in (3, 4)]
    zwk3 = any(e['r'] == 3 and e['excess'] >= 1 for e in ZX.excess(c))
    for idx, line in enumerate(open(fpath)):
        cell = json.loads(line)
        if zwk or any(CK.one_colour_killer(it, cell['argmin']) for it in its):
            clique.add((ci, idx))
        if zwk3 or any(len(it['K']) == 3 and CK.one_colour_killer(it, cell['argmin']) for it in its):
            clique3.add((ci, idx))
ee1 = {k for k in ref if set(ref[k]['cell_level_generic']) & {'E', 'E1'}}
print('\nCLIQUES (Corollary 9.18, census of Proposition 9.19)')
print('clique %d; E1 %d; both %d; clique only %d; E1 only %d; union %d'
      % (len(clique), len(ee1), len(clique & ee1), len(clique - ee1), len(ee1 - clique), len(clique | ee1)))
out = clique - cell_level
print('cells with a clique and no cell-level lemma: %d, by tier %s' % (len(out), dict(Counter(tier[k] for k in out))))
print('  with a three-body clique: %d, by tier %s, classes %s' % (len(out & clique3), dict(Counter(tier[k] for k in out & clique3)),
      dict(Counter(k[0] for k in out & clique3))))
print('  with a four-body clique only: %d, by tier %s, classes %s' % (len(out - clique3), dict(Counter(tier[k] for k in out - clique3)),
      dict(Counter(k[0] for k in out - clique3))))
newcl = (out & clique3) - {k for k in ref if tier[k] == 'D'}
print('  three-body clique cells among the secondary-only cells: %d %s' % (len(newcl & set(sec_only)), sorted(newcl & set(sec_only))))
print('  D cells with a clique: %s' % sorted(k for k in out if tier[k] == 'D'))
print('with Corollary 9.18 (three-body cliques): cell-level %d; secondary only %d; Sections 6-7 only %d'
      % (len(cell_level | (clique3 & set(sec_only))), len(set(sec_only) - clique3), len(D)))
kind2 = Counter()
for k in set(sec_only) - clique3:
    r = ref[k]
    kind2[r['secondary'] or r['template'] or 'TD'] += 1
print('  secondary-only cells without a three-body clique, by lemma: %s' % dict(kind2))
print('  D cells with a three-body clique: %s' % sorted(set(D) & clique3))
wq = [k for k in ref if set(ref[k]['cell_level_generic']) & {'W3', 'EQ2'} and set(ref[k]['cell_level_generic']) <= {'W3', 'EQ2'}
      and not ref[k]['cell_level_allmass']]
print('cells whose only cell-level lemmas are among W3, EQ2: %d; of them with a three-body clique: %s'
      % (len(wq), sorted(k for k in wq if k in clique3)))
