#!/usr/bin/env python3
"""Writes the kernel modules of the fused F2-F4 run of one class from the output of f34kexport (L6K/F34K/Export):
the pair runs (`nodes_<i0>_<i1>.txt`) and, if the class was split at depth d > 0, the prefix (`nodes_prefix.txt`).

* ROOT/L6CheckF/C<c>/Class.lean: the representative `D` and the insertion order `ord`;
* NG<g>.lean, groups of consecutive nodes (at most KF34K_GROUP units, default 20; the kernel checks, without
  Mathlib): for a unit `N<id>.ok`: `checkCells` of the claims on the cells below its sibling nodes with the keep table
  of the unit; for a level node `N<id>.lv`: one level of `treeLevelL` equals the list of the nodes of its children;
* VG<g>.lean (the covering lemmas): `N<id>.cov`, from `unit_coversF` (with `certs_ok` from the F4 kernel theorems and
  the list `L6CheckF.csAll` of `L6CheckF.Certs`, and `nd`: the argmin sets of the claims have no repetition, by the
  kernel) or from `level_covers` and the children's `cov`;
* All.lean: `classOK : ∀ Xz Xw, Cond D Xz Xw → ClaimMeaningFinK L6CheckF.csAll Xz Xw` from the root;
* deps.txt: one line per module, `module: dependencies`, for the build scheduler; deps_vg.txt: the lines of the
  covering modules and All.lean only (to build them where the kernel checks were built elsewhere).

The certificates of the cores are those of the F4 kernel modules (`L6CheckK.F4.C<H>.certH` and `.cert`, under
F4ROOT); CERTNAMES lists the certificate ids in the order of the exporter's indices.
Usage: kf34k_gen.py EXPORT_DIR CERTNAMES CLASS E ZC WC ORDER ROOT F4ROOT  (ORDER comma-separated)"""
import os, re, sys

exp, certnames, c, e, zc, wc, order, root, f4root = sys.argv[1:10]
c = int(c)
ordl = [int(x) for x in order.split(',')]
out = os.path.join(root, 'L6CheckF', f'C{c}')
os.makedirs(out, exist_ok=True)
ns = f'L6CheckF.C{c}'
names = [l.strip() for l in open(certnames)]
data_mod, main_mod = {}, {}
base = os.path.join(f4root, 'L6CheckK', 'F4')
for f in os.listdir(base):
    p = os.path.join(base, f)
    if f.endswith('.lean') and re.match(r'[PM]\d+\.lean$', f):
        for line in open(p):
            m = re.match(r'namespace L6CheckK\.F4\.C(\w+)$', line.strip())
            if m:
                (data_mod if f.startswith('P') else main_mod).setdefault(m.group(1), 'L6CheckK.F4.' + f[:-5])
    elif os.path.isdir(p) and f.startswith('C') and os.path.exists(os.path.join(p, 'Data.lean')):
        data_mod[f[1:]] = f'L6CheckK.F4.{f}.Data'

HEAD = ['', 'set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', '']
# the directory of the keep tables as written in the modules (read when they are elaborated, relative to the working
# directory of the build): KF34K_TBL_DIR, e.g. data/f34k/c<k> for a release; default the absolute path of EXPORT_DIR
# (the form of the run of 2026-10-17)
TBL_DIR = os.environ.get('KF34K_TBL_DIR', os.path.abspath(exp))


def tbl(nid):
    return f'{TBL_DIR}/n{nid}.tbl'


OPEN = 'open L6 L6.F2S L6K.F2S L6K.F34K L6.F34S'


def ts(nodes, leaf):
    return '⟨[' + ', '.join(nodes) + '], ' + ('none' if leaf == '-' else f'some {leaf}') + '⟩'


def parse_node(txt):
    t = txt.split()
    parts, cur = [], []
    for x in t[1:]:
        if x == '/':
            parts.append(cur)
            cur = []
        else:
            cur.append(x)
    parts.append(cur)
    return f'({t[0]}, {ts(parts[0], parts[1][0])}, {ts(parts[2], parts[3][0])})'


units, levels, pair_root, prefix_root, weight = {}, {}, {}, None, {}
for nf in sorted(f for f in os.listdir(exp) if f.startswith('nodes_')):
    for line in open(os.path.join(exp, nf)):
        t = line.split()
        if not t:
            continue
        if t[0] == 'R':
            if t[1] == 'prefix':
                prefix_root = t[2]
            else:
                pair_root[int(t[1])] = t[2]
        elif t[0] == 'U':
            k = t.index('nodes')
            units[t[1]] = (int(t[2]), [parse_node(x) for x in ' '.join(t[k + 1:]).split(' ; ')])
            weight[t[1]] = int(t[t.index('weight') + 1]) if 'weight' in t else int(t[t.index('programs') + 1])
        else:
            k = t.index('programs')
            levels[t[1]] = (int(t[2]), parse_node(' '.join(t[3:k])), t[t.index('children') + 1:])
# the children of the prefix levels at depth d are the roots of the pairs
for nid, (depth, node, kids) in levels.items():
    levels[nid] = (depth, node, [pair_root[int(k[1:])] if k.startswith('P') else k for k in kids])
root_id = prefix_root if prefix_root is not None else pair_root[0]
deps = {}

open(os.path.join(out, 'Class.lean'), 'w').write('\n'.join([
    'import L6K.F2S.SearchRL', 'import L6K.F2S.KeepR', '',
    f'/-! The representative of class {c} and its insertion order, for the kernel run of F2-F4. -/', '',
    f'namespace {ns}', '', 'open L6 L6.F2S', '',
    f'def D : L6.F2.Diag := L6.F2.Diag.ofF1 ⟨{e}, {zc}, {wc}⟩', '',
    f'def ord : List Nat := [{", ".join(map(str, ordl))}]', '', f'end {ns}']) + '\n')
deps[f'{ns}.Class'] = []

# per node: the N block (kernel check) and the V block (covering lemma), with their imports
nblk, vblk, nimp, vimp, kids_of = {}, {}, {}, {}, {}
for nid, (depth, nodes) in units.items():
    claims = open(os.path.join(exp, f'n{nid}.claims')).read().strip()
    used = sorted(set(int(m) for m in re.findall(r'\(\.core (\d+) ', claims)))
    loc = {g: i for i, g in enumerate(used)}
    claims = re.sub(r'\(\.core (\d+) ', lambda m: f'(.core {loc[int(m.group(1))]} ', claims)
    hs = [names[g] for g in used]
    certs = ', '.join(f'(L6CheckK.F4.C{h}.certH.nvar, L6CheckK.F4.C{h}.certH.fixed, L6CheckK.F4.C{h}.certH.gens)'
                      for h in hs)
    nimp[nid] = {data_mod[h] for h in hs}
    vimp[nid] = {main_mod[h] for h in hs}
    kids_of[nid] = []
    nblk[nid] = [f'/-! Unit {nid}: the claims of the cells below {len(nodes)} node(s) at depth {depth}. -/', '',
                 f'namespace {ns}.N{nid}', '', OPEN, '',
                 f'load_ctree T "{tbl(nid)}"', '',
                 f'def certs : List CertKey := [{certs}]', '',
                 f'def nodes : List (Nat × TS × TS) := [{", ".join(nodes)}]', '',
                 f'def claims : List ClaimK := {claims}', '',
                 f'theorem ok : checkCells certs (nodes.flatMap (belowRL (keepR T) D ord {depth})) claims = true := by',
                 '  decide +kernel', '', f'end {ns}.N{nid}', '']
    certs_ok = ['theorem certs_ok : ∀ g ∈ certs, ∃ c ∈ L6CheckF.csAll, L6.Poly.CertMeaning c ∧ c.nvar = g.1 ∧',
                '    c.fixed = g.2.1 ∧ c.gens = g.2.2 := by', '  intro g hg']
    if not hs:
        certs_ok += ['  simp [certs] at hg']
    elif len(hs) == 1:
        certs_ok += ['  simp only [certs, List.mem_cons, List.not_mem_nil, or_false] at hg', '  subst hg',
                     f'  exact ⟨_, L6CheckF.Certs.mem_{hs[0]}, L6CheckK.F4.C{hs[0]}.cert, rfl, rfl, rfl⟩']
    else:
        certs_ok += ['  simp only [certs, List.mem_cons, List.not_mem_nil, or_false] at hg',
                     '  rcases hg with ' + ' | '.join('rfl' for _ in hs)]
        certs_ok += [f'  · exact ⟨_, L6CheckF.Certs.mem_{h}, L6CheckK.F4.C{h}.cert, rfl, rfl, rfl⟩' for h in hs]
    vblk[nid] = [f'namespace {ns}.N{nid}', '', OPEN, ''] + certs_ok + ['',
                 'theorem nd : claims.all claimNodupB = true := by', '  decide +kernel', '',
                 'theorem cov : ∀ Xz Xw : ExpTree, Cond D Xz Xw → ∀ x ∈ nodes, NodeOK x.1 (ord.drop ' + str(depth) +
                 ') → OnPath Xz Xw x →', '    ClaimMeaningFinK L6CheckF.csAll Xz Xw :=',
                 '  fun _ _ hX _ hx hn hp => unit_coversF certs_ok ok nd hX hx hn hp', '', f'end {ns}.N{nid}', '']

for nid, (depth, node, kids) in levels.items():
    parts = [(f'{ns}.N{k}.nodes', 'u', k) if k in units else (f'[{ns}.N{k}.node]', 'l', k) for k in kids]
    children = ' ++ ('.join(pt[0] for pt in parts) + ')' * (len(parts) - 1)
    p = ordl[depth]
    nimp[nid], vimp[nid], kids_of[nid] = set(), set(), list(kids)
    nblk[nid] = [f'/-! Level node {nid} at depth {depth}: the insertion of body {p}. -/', '',
                 f'namespace {ns}.N{nid}', '', OPEN, '',
                 f'load_ctree T "{tbl(nid)}"', '',
                 f'def node : Nat × TS × TS := {node}', '',
                 f'def children : List (Nat × TS × TS) := {children}', '',
                 f'theorem lv : treeLevelL (keepR T) D [{p}] node.1 node.2.1 node.2.2 = children := by',
                 '  decide +kernel', '', f'end {ns}.N{nid}', '']
    proof = ['theorem cov : ∀ Xz Xw : ExpTree, Cond D Xz Xw → NodeOK node.1 (ord.drop ' + str(depth) +
             ') → OnPath Xz Xw node →', '    ClaimMeaningFinK L6CheckF.csAll Xz Xw := by',
             '  intro Xz Xw hX hn hp',
             f'  have hn\' : NodeOK node.1 ({p} :: ord.drop {depth + 1}) := hn',
             '  obtain ⟨y, hy, hy1, hyp⟩ := level_covers lv hX hn\' hp',
             f'  have hyn : NodeOK y.1 (ord.drop {depth + 1}) := hy1 ▸ nodeOK_step hn\'',
             '  simp only [children] at hy']
    for i, (_, kind, k) in enumerate(parts):
        if i < len(parts) - 1:
            proof.append('  rcases List.mem_append.mp hy with hy | hy')
            ind = '  · '
        else:
            ind = '  '
        if kind == 'u':
            proof.append(f'{ind}exact {ns}.N{k}.cov Xz Xw hX y hy hyn hyp')
        else:
            proof.append(f'{ind}rw [List.mem_singleton] at hy; subst hy; exact {ns}.N{k}.cov Xz Xw hX hyn hyp')
    vblk[nid] = [f'namespace {ns}.N{nid}', '', OPEN, ''] + proof + ['', f'end {ns}.N{nid}', '']

# groups of consecutive nodes (ids in post-order: children first), at most G units each; with KF34K_LEVELS_APART=1
# the units in groups of at most G units and the level nodes apart, in groups of at most KF34K_LEVEL_GROUP (default
# 200), so that a group of units depends on no other group (consecutive groups of units and level nodes would form a
# chain along each run); a group never spans two export runs (ids of the run of pairs i0.. start at i0 * 10^6; the
# prefix at 2 * 10^9)
G = int(os.environ.get('KF34K_GROUP', '20'))
order_ids = sorted(list(units) + list(levels), key=int)
groups, cur, nu = [], [], 0
if os.environ.get('KF34K_LEVELS_APART', '0') == '1':
    GL = int(os.environ.get('KF34K_LEVEL_GROUP', '200'))
    lpool = [n for n in order_ids if n in levels]
    # with KF34K_LEVELS_BY_DEPTH=1 the level nodes of a run are grouped by depth, deepest first, so that the groups
    # of one depth depend only on deeper ones (the longest chain is the depth of the tree)
    bydepth = os.environ.get('KF34K_LEVELS_BY_DEPTH', '0') == '1'
    if bydepth:
        lpool.sort(key=lambda n: (int(n) // 1000000, -levels[n][0], int(n)))
    for pool, cap in (([n for n in order_ids if n in units], G), (lpool, GL)):
        cur = []
        for nid in pool:
            if cur and (int(cur[-1]) // 1000000 != int(nid) // 1000000 or len(cur) >= cap or
                        bydepth and nid in levels and levels[nid][0] != levels[cur[-1]][0]):
                groups.append(cur)
                cur = []
            cur.append(nid)
        if cur:
            groups.append(cur)
else:
    for nid in order_ids:
        if cur and int(cur[-1]) // 1000000 != int(nid) // 1000000:
            groups.append(cur)
            cur, nu = [], 0
        cur.append(nid)
        if nid in units:
            nu += 1
        if nu >= G:
            groups.append(cur)
            cur, nu = [], 0
    if cur:
        groups.append(cur)
group_of = {nid: gi for gi, g in enumerate(groups) for nid in g}
for gi, g in enumerate(groups):
    other = sorted({group_of[k] for nid in g for k in kids_of[nid]} - {gi})
    imps = ['L6K.F2S.Load', 'L6K.F34K.Check', f'{ns}.Class'] + sorted(set().union(*[nimp[n] for n in g])) + \
        [f'{ns}.NG{h}' for h in other]
    L = [f'import {m}' for m in imps] + HEAD + [f'/-! Class {c}, group {gi}: kernel checks. -/', '']
    for nid in g:
        L += nblk[nid]
    open(os.path.join(out, f'NG{gi}.lean'), 'w').write('\n'.join(L) + '\n')
    deps[f'{ns}.NG{gi}'] = [f'{ns}.Class'] + [f'{ns}.NG{h}' for h in other]
    vimps = [f'{ns}.NG{gi}', 'L6SoundK.F34K.Fin', 'L6CheckF.Certs'] + sorted(set().union(*[vimp[n] for n in g])) + \
        [f'{ns}.VG{h}' for h in other]
    V = [f'import {m}' for m in vimps] + HEAD + [f'/-! Class {c}, group {gi}: covering lemmas. -/', '']
    for nid in g:
        V += vblk[nid]
    open(os.path.join(out, f'VG{gi}.lean'), 'w').write('\n'.join(V) + '\n')
    deps[f'{ns}.VG{gi}'] = [f'{ns}.NG{gi}', 'L6CheckF.Certs'] + [f'{ns}.VG{h}' for h in other]

r = root_id
if r in units:
    # the root is the only node of its unit
    concl = (f'  fun Xz Xw hX => N{r}.cov Xz Xw hX _ List.mem_cons_self (nodeOKB_spec (by decide))\n'
             f'    (onPath_root Xz Xw hX)')
else:
    concl = f'  fun Xz Xw hX => N{r}.cov Xz Xw hX (nodeOKB_spec (by decide)) (onPath_root Xz Xw hX)'
open(os.path.join(out, 'All.lean'), 'w').write('\n'.join([
    f'import {ns}.VG{group_of[r]}', '', f'/-! Class {c}: the claims of all cells, from the root. -/', '',
    f'namespace {ns}', '', OPEN, '',
    '/-- **Every pair satisfying `Cond D` has the claim of its cell**, by the kernel. -/',
    'theorem classOK : ∀ Xz Xw : ExpTree, Cond D Xz Xw → ClaimMeaningFinK L6CheckF.csAll Xz Xw :=', concl, '',
    f'end {ns}']) + '\n')
deps[f'{ns}.All'] = [f'{ns}.VG{group_of[r]}']
with open(os.path.join(out, 'groups.txt'), 'w') as f:
    for gi, g in enumerate(groups):
        f.write(f'NG{gi} run {int(g[0]) // 1000000} nodes {len(g)} units {sum(1 for n in g if n in units)} '
                f'weight {sum(weight.get(n, 0) for n in g)} maxw {max([weight.get(n, 0) for n in g] + [0])}\n')
with open(os.path.join(out, 'deps.txt'), 'w') as f:
    for m, ds in deps.items():
        f.write(m + ': ' + ' '.join(ds) + '\n')
with open(os.path.join(out, 'deps_vg.txt'), 'w') as f:
    for m, ds in deps.items():
        if m.rsplit('.', 1)[1].startswith('VG') or m.endswith('.All'):
            f.write(m + ': ' + ' '.join(ds) + '\n')
print('class', c, 'units', len(units), 'levels', len(levels), 'groups', len(groups), 'root', r)
