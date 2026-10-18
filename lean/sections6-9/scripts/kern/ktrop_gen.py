#!/usr/bin/env python3
"""Generator of the kernel version of Lemma 6.19(a)(iii)-(iv) for one system (L6CheckTrop.<SYS>), from the data of
lean6_special (Comp/D88/Trop/Data<SYS>.lean: the set G and the assumed systems; Tree<SYS>/T*.lean: the covering tree)
and the cofactor certificate of the escape-ray system (lines "k c e0 ... e16", coefficients in [0, 65521)).

The covering tree is lean6_special's, with every leaf `.leaf cofs cofR` replaced by `.hyp k`: the system of hyp k is
the list of the initial forms at the node (`sys<k>`, computed from `Gb<SYS>` and the faces on the path, as the leaf
and the check of `.hyp` compute it); hyp 0 is the escape-ray system (lean6_special's own `.hyp 0`). Then
lean6_special's `chk` and `cover_soundG` apply unchanged, and the torus emptiness of each system comes from its
certificate: the identity of the leaf (`leafOKK`, by the kernel) for the small leaves, and the bucket checks of
`L6KSpec.C4` (as for Lemma 7.9, `scripts/kc4_gen.py`) for the leaves with more than BIG_TERMS cofactor terms and for
the escape-ray system.

Writes, in the module root L6CheckTrop of OUT_ROOT (namespace L6CheckTrop.<SYS>):
  <SYS>/Tree.lean       sys<k>, hyps, root (the tree in pieces n<id>, at most PIECE nodes each);
  <SYS>/Cover.lean      cover_ok : chk 65521 Gb<SYS> hyps [] [] [] root = true (decide +kernel);
  <SYS>/Small.lean      ok<k> : TorusEmptySys 65521 sys<k> for the small leaves;
  <SYS>/<C>/{Data,B<m>,Bks,Ivl<q>,Cover,Main,Bridge}.lean  for each big leaf (C = L<k>) and the escape system
                        (C = Esc): the bucket checks, `ident`, and in Bridge ok : TorusEmptySys 65521 sys<k>;
  <SYS>/Final.lean      hypsOK, gb_ok and the theorem (kc_torus_gamma for KC), in Lean6.Special.D88.TropK;
  data/tropk/<SYS>_<C>.bin, .idx;  L6CheckTrop/deps_<SYS>.txt.
Deterministic. Untrusted: every claim is checked by the kernel.
Usage: ktrop_gen.py OUT_ROOT SPEC_ROOT SYS ESC_CERT BUCKET_BUDGET SPLIT_BUDGET MODULE_BUDGET [BIG_TERMS [PIECE]]
(BIG_TERMS default 2000; PIECE, the weight of a piece of the tree in nodes and certificates, default 400; ESC_CERT
`-`: no certificate of the escape-ray system yet, so neither its checks nor Final are written; a line `h e0 … e16` in
ESC_CERT: the certificate is of the monomial x^e instead of 1, enough on the torus; ESC_CERT `trace:FILE`: a traced
Buchberger run of lean6_special's engine from the escape-ray system to 1, checked as a chain of identities over earlier
polynomials, modules L6CheckTrop.<SYS>.Chain.{Tab,B<m>,Ok}, data data/tropk/<SYS>_chain_*)"""
import glob, lzma, math, os, re, sys
from collections import defaultdict

P = 65521
MU = [1, 2, 3, 30]
COVER_SPLIT = int(os.environ.get('KTROP_COVER', '16000'))
BT = 'Nat × Nat × List Nat × Piece'
HEAD = ['set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', '']
sys.setrecursionlimit(1000000)


def write(root, mod, lines):
    path = os.path.join(root, *mod.split('.')) + '.lean'
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w') as f:
        f.write('\n'.join(lines) + '\n')


# ---------------------------------------------------------------- the data of lean6_special (the readers of Parse.lean)

def lean_string(path, name):
    m = re.search(r'def ' + name + r' : String :=\s*"([^"]*)"', open(path).read())
    assert m, (path, name)
    return m.group(1)


class Toks:
    def __init__(self, s):
        self.t = [x for x in s.split(' ') if x and x != '\n']
        self.i = 0

    def nat(self):
        v = int(self.t[self.i])
        assert v >= 0
        self.i += 1
        return v

    def int(self):
        v = int(self.t[self.i])
        self.i += 1
        return v

    def mono(self):
        n = self.nat()
        ps = [(self.nat(), self.nat()) for _ in range(n)]
        ln = max([v + 1 for v, _ in ps], default=0)
        return [sum(e for v, e in ps if v == i) for i in range(ln)]

    def polyZ(self):
        return [(self.int(), self.mono()) for _ in range(self.nat())]

    def polyN(self):
        return [(self.nat(), self.mono()) for _ in range(self.nat())]

    def gpoly(self):
        return [(self.mono(), self.polyZ()) for _ in range(self.nat())]

    def sparse(self):
        return [(self.nat(), self.int()) for _ in range(self.nat())]

    def eqc(self):
        return (self.int(), self.sparse())

    def strict(self):
        return (self.int(), self.sparse(), self.sparse())


def evalZ(mu, c):
    acc = 0
    for coef, m in c:
        prod = 1
        for a, e in zip(mu, m):
            prod *= a ** e
        acc += coef * prod
    return acc


def read_data(spec, name):
    data = os.path.join(spec, 'Lean6/Special/Comp/D88/Trop', f'Data{name}.lean')
    t = Toks(lean_string(data, 'gStr'))
    G = [t.gpoly() for _ in range(t.nat())]
    assert t.i == len(t.t)
    Gb = [[(evalZ(MU, c) % P, m) for m, c in g] for g in G]
    t = Toks(lean_string(data, 'hypStr'))
    hyps = []
    for _ in range(t.nat()):
        hyps.append([t.polyN() for _ in range(t.nat())])
    assert t.i == len(t.t)
    files = sorted(glob.glob(os.path.join(spec, 'Lean6/Special/Comp/D88/Trop', f'Tree{name}', 'T*.lean')))
    tree = Toks(' '.join(lean_string(f, 's') for f in files))
    return Gb, hyps, tree


def read_node(t, Gb):
    tag = t.t[t.i]
    t.i += 1
    if tag == 'E':
        return ('E', t.sparse(), t.sparse())
    if tag == 'S':
        g, i, j = t.nat(), t.nat(), t.nat()
        return ('S', g, i, j, read_node(t, Gb), read_node(t, Gb), read_node(t, Gb))
    if tag == 'F':
        g, n = t.nat(), t.nat()
        F = [t.nat() for _ in range(n)]
        eqc = [t.eqc() for _ in range(n - 1)]
        sz = len(Gb[g]) if g < len(Gb) else 0
        strict = [t.strict() for _ in range(max(sz - n, 0))]
        return ('F', g, F, eqc, strict, read_node(t, Gb))
    if tag == 'M':
        return ('M',)
    if tag == 'L':
        cofs = [(t.nat(), t.polyN()) for _ in range(t.nat())]
        return ('L', cofs, t.polyN())
    if tag == 'N':
        return ('N', [t.eqc() for _ in range(17)])
    if tag == 'H':
        return ('H', t.nat())
    raise ValueError(tag)


def inF(Gb, g, F):
    gg = Gb[g] if g < len(Gb) else []
    return [gg[i] if i < len(gg) else (0, []) for i in F]


def relabel(node, Gb, faces, leaves, hypfaces):
    """the tree with every leaf replaced by .hyp (1 + its index in prefix order); leaves: (faces, cofs, cofR)"""
    tag = node[0]
    if tag == 'S':
        return node[:4] + tuple(relabel(c, Gb, faces, leaves, hypfaces) for c in node[4:])
    if tag == 'F':
        return node[:5] + (relabel(node[5], Gb, [(node[1], node[2])] + faces, leaves, hypfaces),)
    if tag == 'L':
        leaves.append((faces, node[1], node[2]))
        return ('H', len(leaves))
    if tag == 'H':
        assert node[1] == 0 and not hypfaces
        hypfaces.append(faces)
        return node
    return node


# ---------------------------------------------------------------- Lean literals

def lst(xs):
    return '[' + ', '.join(xs) + ']'


def sp(v):
    return lst(f'({k}, {c})' for k, c in v)


def poly(p):
    return lst(f'({c}, {lst(map(str, m))})' for c, m in p)


def node_size(nd):
    if nd[0] == 'S':
        return 1 + sum(node_size(c) for c in nd[4:])
    if nd[0] == 'F':
        return 1 + node_size(nd[5])
    return 1


def emit_tree(nd, piece, defs):
    """(the Lean term of the node, its weight); a subtree whose weight (nodes and certificates) passes `piece` becomes
    a separate definition n<i>"""
    tag = nd[0]
    w = 1
    if tag == 'E':
        s = f'.empty {sp(nd[1])} {sp(nd[2])}'
    elif tag == 'S':
        parts = [emit_tree(c, piece, defs) for c in nd[4:]]
        w += sum(x for _, x in parts)
        s = f'.split {nd[1]} {nd[2]} {nd[3]} ' + ' '.join(f'({t})' for t, _ in parts)
    elif tag == 'F':
        t, x = emit_tree(nd[5], piece, defs)
        w += x + len(nd[3]) + len(nd[4])
        eqc = lst(f'({k}, {sp(u)})' for k, u in nd[3])
        st = lst(f'({z}, {sp(y)}, {sp(u)})' for z, y, u in nd[4])
        s = f'.face {nd[1]} {lst(map(str, nd[2]))} {eqc} {st} ({t})'
    elif tag == 'M':
        s = '.mono'
    elif tag == 'N':
        s = '.nonneg ' + lst(f'({k}, {sp(u)})' for k, u in nd[1])
    else:
        s = f'.hyp {nd[1]}'
    if w > piece:
        defs.append(s)
        return f'n{len(defs) - 1}', 1
    return s, w


def wrap(text, width, indent):
    """the text broken at spaces into lines of at most `width` characters, each line indented"""
    lines, cur = [], indent
    for w in text.split(' '):
        if len(cur) + len(w) + 1 > width and cur.strip():
            lines.append(cur.rstrip())
            cur = indent
        cur += w + ' '
    if cur.strip():
        lines.append(cur.rstrip())
    return lines


# ---------------------------------------------------------------- the bucket checks (as scripts/kc4_gen.py)

def key(e):
    return sum(x << (8 * v) for v, x in enumerate(e))


def choose_split(NV, gens, cofs, h, budget):
    def counts(Vp):
        pat = lambda e: tuple(e[j] for j in Vp)
        cnt = defaultdict(int)
        for g, c in zip(gens, cofs):
            gp, cp = defaultdict(int), defaultdict(int)
            for _, e in g:
                gp[pat(e)] += 1
            for _, e in c:
                cp[pat(e)] += 1
            for d, nd in gp.items():
                for a2, na in cp.items():
                    cnt[tuple(x + y for x, y in zip(d, a2))] += nd * na
        return cnt
    deg = [max((e[j] for p in gens + cofs + [h] for _, e in p), default=0) for j in range(NV)]
    Vp = []
    cnt = counts(Vp)
    while cnt and max(cnt.values()) > budget:
        best = None
        for j in range(NV):
            if j in Vp or deg[j] == 0:
                continue
            c2 = counts(Vp + [j])
            m = max(c2.values())
            if best is None or m < best[0]:
                best = (m, j, c2)
        if best is None or best[0] >= max(cnt.values()):
            break
        Vp.append(best[1])
        cnt = best[2]
    return Vp, cnt


def pack(records, RB):
    if len(records) <= 64:
        n = 0
        for i, r in enumerate(records):
            assert 0 <= r < (1 << RB)
            n |= r << (i * RB)
        return n
    m = len(records) // 2
    return pack(records[:m], RB) | (pack(records[m:], RB) << (m * RB))


def gen_cert(root, ns, label, NV, gens, cofs, budget, split_budget, mbudget, datafile, hmono=None):
    """the bucket checks of the identity Σ cofs[i] · gens[i] = h modulo P (exponent vectors of length NV), h = 1 or the
    monomial x^hmono; returns the modules"""
    h = [(1, (0,) * NV)] if hmono is None else [(1, tuple(hmono))]
    assert len(gens) == len(cofs) and len(gens) < 64 and all(len(g) <= 64 for g in gens)
    assert all(len(e) == NV for p in gens + cofs for _, e in p)
    assert all(max(e, default=0) < 128 for p in gens + cofs for _, e in p)
    assert all(0 <= c < P for p in gens + cofs for c, _ in p)
    KB = 8 * NV
    Vp, cnt = choose_split(NV, gens, cofs, h, split_budget)
    pat = lambda e: tuple(e[j] for j in Vp)
    CB = max([abs(c).bit_length() for p in cofs for c, _ in p] + [1])
    HB = 1
    chunks = []

    def chunk(n):
        chunks.append(n)
        return len(chunks) - 1

    def nterms(terms, cb):
        out = []
        for sgn in (1, -1):
            ts = sorted((key(e), abs(c)) for c, e in terms if c * sgn > 0)
            n = pack([k | (c << KB) for k, c in ts], KB + cb)
            out.append(f'{len(ts)} {chunk(n)}')
        return ' '.join(out)

    pieces = []
    for c in cofs:
        groups = defaultdict(list)
        for t in c:
            groups[pat(t[1])].append(t)
        pieces.append([(a2, groups[a2]) for a2 in sorted(groups)])
    assert all(len(pl) < 2 ** 20 for pl in pieces)
    idx = [f'K {KB}', f'G {len(gens)}']
    for i, pl in enumerate(pieces):
        for _, ts in pl:
            idx.append(f'P {i} {CB} {nterms(ts, CB)}')
    hgroups = defaultdict(list)
    for t in h:
        hgroups[pat(t[1])].append(t)
    bcodes = defaultdict(list)
    bprods = defaultdict(int)
    for i, g in enumerate(gens):
        for j, (_, e) in enumerate(g):
            d = pat(e)
            for q, (a2, ts) in enumerate(pieces[i]):
                pa = tuple(x + y for x, y in zip(d, a2))
                bcodes[pa].append(i * 2 ** 26 + j * 2 ** 20 + q)
                bprods[pa] += len(ts)
    allpat = sorted(set(bcodes) | set(hgroups))
    groups, cur, load = [], [], 0
    for pa in allpat:
        w = bprods.get(pa, 0) + len(hgroups.get(pa, []))
        if cur and load + w > budget:
            groups.append(cur)
            cur, load = [], 0
        cur.append(pa)
        load += w
    if cur:
        groups.append(cur)
    bprod_list = []
    for g in groups:
        codes = sorted(c for pa in g for c in bcodes.get(pa, []))
        hts = [t for pa in g for t in hgroups.get(pa, [])]
        prods = sum(bprods.get(pa, 0) for pa in g)
        ci = chunk(pack(codes, 32))
        hp = nterms(hts, HB)
        F = prods + len(hts) + 16
        R = math.ceil(math.log2(max(2, 2 * len(codes) + 3))) + 1
        idx.append(f'B {len(bprod_list)} {F} {R} {len(codes)} {ci} {HB} {hp}')
        bprod_list.append(prods)
    datadir = os.path.join(root, 'data', 'tropk')
    os.makedirs(datadir, exist_ok=True)
    binp = os.path.join(datadir, f'{datafile}.bin')
    with open(binp, 'wb') as f:
        for n in chunks:
            bb = n.to_bytes((n.bit_length() + 7) // 8, 'little')
            f.write(len(bb).to_bytes(8, 'little'))
            f.write(bb)
    size = os.path.getsize(binp)
    with open(os.path.join(datadir, f'{datafile}.idx'), 'w') as f:
        f.write('\n'.join(idx) + '\n')
    allc = sorted(c for pa in bcodes for c in bcodes[pa])
    bnd = [0]
    for q in range(COVER_SPLIT, len(allc), COVER_SPLIT):
        if allc[q] > bnd[-1]:
            bnd.append(allc[q])
    ivls = [(bnd[q], bnd[q + 1] if q + 1 < len(bnd) else 0) for q in range(len(bnd))]
    write(root, f'{ns}.Data', ['import L6KSpec.C4Check', 'import L6KSpec.C4Load', '', *HEAD,
        f'/-! {label}, p = {P}: the generators packed, `h = 1`, the cofactor pieces and the buckets (split variables '
        f'{Vp}). -/', '', f'namespace {ns}', '', 'open L6KSpec.C4', '',
        '/-- The generators, packed. -/',
        'def gens : List KPoly := [' + ', '.join('[' + ', '.join(f'({key(e)}, {c})' for c, e in g) + ']' for g in gens)
        + ']', '', *(['/-- `h = 1`. -/', 'def h : KPoly := [(0, 1)]'] if hmono is None else
                     [f'/-- `h = x^{list(hmono)}`. -/', f'def h : KPoly := [({key(hmono)}, 1)]']), '',
        '/-! The cofactor pieces `pcs` and the buckets `b0`, `b1`, … (data for the kernel). -/',
        f'load_c4_cert "data/tropk/{datafile}.bin" {size} "data/tropk/{datafile}.idx"', '', f'end {ns}'])
    mods = []
    groups_b, cur, load = [], [], 0
    for k, bp in enumerate(bprod_list):
        if cur and load + bp > mbudget:
            groups_b.append(cur)
            cur, load = [], 0
        cur.append(k)
        load += bp
    if cur:
        groups_b.append(cur)
    G = f'guardMask {NV}'
    for m, ks in enumerate(groups_b):
        mns = f'{ns}.B{m}'
        L = [f'import {ns}.Data', '', *HEAD, f'/-! {label}, buckets {ks[0]}–{ks[-1]}. -/', '',
             f'namespace {mns}', '', f'open L6KSpec.C4 {ns}', '']
        for k in ks:
            L.append(f'theorem ok{k} : bucketOKp {P} ({G}) b{k}.1 b{k}.2.1 gens pcs b{k}.2.2.1 b{k}.2.2.2 = true := by '
                     'decide +kernel')
        L += ['', '/-- The buckets of this block. -/',
              f'noncomputable def bks : List ({BT}) := [' + ', '.join(f'b{k}' for k in ks) + ']', '',
              f'theorem all_ok : bks.all (fun b => bucketOKp {P} ({G}) b.1 b.2.1 gens pcs b.2.2.1 b.2.2.2) = true := by',
              '  simp only [bks, List.all_cons, List.all_nil, Bool.and_true, ' + ', '.join(f'ok{k}' for k in ks) + ']',
              '', f'end {mns}']
        write(root, mns, L)
        mods.append(mns)
    write(root, f'{ns}.Bks', [f'import {m}' for m in mods] + ['', *HEAD, f'namespace {ns}', '', 'open L6KSpec.C4', '',
         '/-- All buckets. -/', f'noncomputable def allBks : List ({BT}) := ' + ' ++ '.join(f'{b}.bks' for b in mods),
         '', '/-- The intervals of the comparison of codes. -/',
         'def ivls : List (Nat × Nat) := [' + ', '.join(f'({x}, {y})' for x, y in ivls) + ']', '', f'end {ns}'])
    for q, (x, y) in enumerate(ivls):
        write(root, f'{ns}.Ivl{q}', [f'import {ns}.Bks', '', *HEAD, f'namespace {ns}', '', 'open L6KSpec.C4', '',
              f'theorem cov{q} : ivlCheck (allBks.flatMap fun b => b.2.2.1) (allCodes gens pcs) {x} {y} = true := '
              'by decide +kernel', '', f'end {ns}'])
    write(root, f'{ns}.Cover', [f'import {ns}.Ivl{q}' for q in range(len(ivls))] + ['', *HEAD, f'namespace {ns}', '',
          'open L6KSpec.C4', '',
          'theorem cover_all : ivls.all (fun lh => ivlCheck (allBks.flatMap fun b => b.2.2.1) (allCodes gens pcs) '
          'lh.1 lh.2) = true := by',
          '  simp only [ivls, List.all_cons, List.all_nil, Bool.and_true, ' + ', '.join(f'cov{q}' for q in range(len(ivls)))
          + ']', '', f'end {ns}'])
    write(root, f'{ns}.Main', [f'import {ns}.Cover', 'import L6SoundKSpec.C4Cert', '', *HEAD, f'namespace {ns}', '',
        'open L6KSpec.C4', '',
        f'theorem all_ok : allBks.all (fun b => bucketOKp {P} ({G}) b.1 b.2.1 gens pcs b.2.2.1 b.2.2.2) = true := by',
        '  simp only [allBks, List.all_append, Bool.and_self, ' + ', '.join(f'{b}.all_ok' for b in mods) + ']', '',
        'theorem cover : coverHead gens pcs ivls = true := by decide +kernel', '',
        f'theorem hparts : hOK {HB + 1} 20 h (allBks.map fun b => b.2.2.2) = true := by decide +kernel', '',
        *([f'/-- **The cofactor identity**: where `{P} = 0`, the generators have no common zero. -/',
           f'theorem ident {{R : Type*}} [CommRing R] (hp : (({P} : ℕ) : R) = 0) (x : ℕ → R)',
           f'    (hg : ∀ g ∈ gens, eval {NV} x g = 0) : (1 : R) = 0 := by',
           f'  have e := cofmod_sound_ivl (p := {P}) (by norm_num) all_ok cover cover_all hparts hp x hg',
           '  simpa [h, eval_cons, monoEval_zero] using e'] if hmono is None else
          [f'/-- **The cofactor identity**: where `{P} = 0` and the generators vanish, so does the monomial `h`. -/',
           f'theorem ident {{R : Type*}} [CommRing R] (hp : (({P} : ℕ) : R) = 0) (x : ℕ → R)',
           f'    (hg : ∀ g ∈ gens, eval {NV} x g = 0) : eval {NV} x h = 0 :=',
           f'  cofmod_sound_ivl (p := {P}) (by norm_num) all_ok cover cover_all hparts hp x hg']),
        '', f'end {ns}'])
    prods = sum(bprod_list)
    print(f'{label}: split {Vp} buckets {len(bprod_list)} max_bucket {max(bprod_list)} products {prods} codes '
          f'{len(allc)} intervals {len(ivls)} bucket_modules {len(mods)} data_bytes {size}', flush=True)
    return [f'{ns}.Data'] + mods + [f'{ns}.Bks'] + [f'{ns}.Ivl{q}' for q in range(len(ivls))] + \
        [f'{ns}.Cover', f'{ns}.Main']


def combine(terms, nv):
    """the terms (c, monomial) as a polynomial modulo P with exponent vectors of length nv, equal monomials merged"""
    d = defaultdict(int)
    for c, m in terms:
        assert len(m) <= nv
        e = tuple(m) + (0,) * (nv - len(m))
        d[e] = (d[e] + c) % P
    return [(c, e) for e, c in sorted(d.items(), reverse=True) if c]


def gen_chain(root, ns, name, sysz, trace_path, mbudget):
    """the check of a traced Buchberger run (lean6_special's `Comp.GB.Trace.traceText`) from the system `sysz` to the
    constant 1 as a chain of identities: the table holds the inputs, then the ancestors of the last element (each
    sorted by key); each ancestor is an identity over the inputs and the earlier ancestors. Returns the modules with
    their dependencies and the name of the theorem `TorusEmptySys P sys0`."""
    from trace_chain import read_trace, ancestors
    elems = read_trace(trace_path)
    need = ancestors(elems)
    nin = len(sysz)
    pk = lambda m: sum(x << (8 * v) for v, x in enumerate(m))
    tab = [sorted((pk(m), c % P) for c, m in f if c % P) for f in sysz]
    assert all(len({k for k, _ in f}) == len(f) for f in tab)
    tidx, g, steps = {}, {}, []
    for k in need:
        d = elems[k]
        h = defaultdict(int)
        cofs = []
        s = d['scale'] % P
        assert s
        if d['org'][0] == 'I':
            i = d['org'][1]
            for key, c in tab[i]:
                h[key] = (h[key] + c) % P
            cofs.append((i, 0, s))
        else:
            _, i, j, mi, mj = d['org']
            for key, c in g[i].items():
                h[key + mi] = (h[key + mi] + c) % P
            for key, c in g[j].items():
                h[key + mj] = (h[key + mj] - c) % P
            cofs += [(tidx[i], mi, s), (tidx[j], mj, (P - s) % P)]
        for c, r, m in d['steps']:
            for key, cc in g[r].items():
                h[key + m] = (h[key + m] - c * cc) % P
            cofs.append((tidx[r], m, (P - s * c % P) % P))
        assert all(c for _, _, c in cofs)
        g[k] = {key: c * s % P for key, c in h.items() if c * s % P}
        tidx[k] = nin + len(steps)
        tab.append(sorted(g[k].items()))
        steps.append((tidx[k], cofs))
    assert tab[-1] == [(0, 1)], 'the last element is not the constant 1'
    assert len(tab) < 2 ** 12 and all(max(((key >> (8 * v)) & 255) for v in range(17)) < 128
                                       for e in tab for key, _ in e)
    KB, CB, RB = 136, 17, 12
    datadir = os.path.join(root, 'data', 'tropk')
    os.makedirs(datadir, exist_ok=True)

    def write_data(stem, chunks, idx):
        binp = os.path.join(datadir, f'{stem}.bin')
        with open(binp, 'wb') as f:
            for n in chunks:
                bb = n.to_bytes((n.bit_length() + 7) // 8, 'little')
                f.write(len(bb).to_bytes(8, 'little'))
                f.write(bb)
        with open(os.path.join(datadir, f'{stem}.idx'), 'w') as f:
            f.write('\n'.join(idx) + '\n')
        return os.path.getsize(binp)
    tsize = write_data(f'{name}_chain_tab', [pack([key | (c << KB) for key, c in e], KB + CB) for e in tab],
                       [f'K {KB} {CB}'] + [f'T {len(e)} {j}' for j, e in enumerate(tab)])
    cns = f'{ns}.Chain'
    write(root, f'{cns}.Tab', ['import L6KSpec.TropChainLoad', '', *HEAD,
          f'/-! The table of the chain of `{name}`: the {nin} inputs (the escape-ray system `sys0`), then the {len(need)}',
          'ancestors of the constant `1` in the traced Buchberger run, each sorted by key (data for the kernel). -/', '',
          f'namespace {cns}', '', f'load_chain_table "data/tropk/{name}_chain_tab.bin" {tsize} '
          f'"data/tropk/{name}_chain_tab.idx"', '', f'end {cns}'])
    prods = [len(tab[k]) + sum(len(tab[r]) for r, _, _ in cofs) for k, cofs in steps]
    batches, cur, load = [], [], 0
    for j, pr in enumerate(prods):
        if cur and load + pr > mbudget:
            batches.append(cur)
            cur, load = [], 0
        cur.append(j)
        load += pr
    if cur:
        batches.append(cur)
    mods = [(f'{cns}.Tab', [])]
    for b, js in enumerate(batches):
        chunks, idx = [], [f'K {RB} {KB} {CB}']
        for j in js:
            k, cofs = steps[j]
            F = prods[j] + 16
            R = math.ceil(math.log2(len(cofs) + 2)) + 1
            idx.append(f'S {j} {k} {F} {R} {len(cofs)} {len(chunks)}')
            chunks.append(pack([r | (m << RB) | (c << (RB + KB)) for r, m, c in cofs], RB + KB + CB))
        size = write_data(f'{name}_chain_B{b}', chunks, idx)
        bns = f'{cns}.B{b}'
        L = [f'import {cns}.Tab', '', *HEAD, f'/-! The chain of `{name}`, elements {js[0]}–{js[-1]}. -/', '',
             f'namespace {bns}', '', f'open L6KSpec.C4 L6KSpec.Trop {cns}', '',
             f'load_chain_steps "data/tropk/{name}_chain_B{b}.bin" {size} "data/tropk/{name}_chain_B{b}.idx"', '']
        for j in js:
            L.append(f'theorem ok{j} : chainStepOK {P} (guardMask 17) T s{j} = true := by decide +kernel')
        L += ['', '/-- The steps of this block. -/',
              'noncomputable def bsteps : List ChainStep := [' + ', '.join(f's{j}' for j in js) + ']', '',
              f'theorem all_ok : bsteps.all (chainStepOK {P} (guardMask 17) T) = true := by',
              '  simp only [bsteps, List.all_cons, List.all_nil, Bool.and_true, ' + ', '.join(f'ok{j}' for j in js) + ']',
              '', f'end {bns}']
        write(root, bns, L)
        mods.append((bns, [f'{cns}.Tab']))
    blocks = [m for m, _ in mods[1:]]
    write(root, f'{cns}.Ok', [f'import {m}' for m in blocks] + [f'import {ns}.Tree', 'import L6SoundKSpec.TropChain',
          'import Lean6.Special.D88.Trop.Final', '', *HEAD,
          f'/-! The escape-ray system `sys0` of `{name}` has no common zero: the chain of the traced Buchberger run from it',
          'to the constant `1`, checked by the kernel (`sysEmpty_of_chain`). -/', '', f'namespace {cns}', '',
          'open L6KSpec.C4 L6KSpec.Trop Lean6.Special.Comp Lean6.Special.Comp.D88.Trop Lean6.Special.D88.Trop',
          f'open {ns} (sys0)', '',
          '/-- All steps. -/',
          'noncomputable def allSteps : List ChainStep := ' + ' ++ '.join(f'{m}.bsteps' for m in blocks), '',
          'theorem tab_guards : T.all (guards (guardMask 17)) = true := by decide +kernel', '',
          f'theorem all_ok : allSteps.all (chainStepOK {P} (guardMask 17) T) = true := by',
          '  simp only [allSteps, List.all_append, ' + ', '.join(f'{m}.all_ok' for m in blocks) + ', Bool.and_self]', '',
          'theorem order_ok : chainOrder allSteps sys0.length = true := by decide +kernel', '',
          'theorem inputs_ok : (List.range sys0.length).all (fun i => nth [] T i == sortN 40 (toN (sys0.getD i []))) = '
          'true := by decide +kernel', '',
          'theorem len_pos : 0 < allSteps.length := by decide +kernel', '',
          'theorem last_ok : nth [] T (sys0.length + allSteps.length - 1) = [(0, 1)] := by decide +kernel', '',
          f'/-- **The torus emptiness of `sys0`**, from the chain. -/',
          f'theorem ok : TorusEmptySys {P} sys0 :=',
          '  sysEmpty_of_chain (by decide +kernel) (by norm_num) tab_guards inputs_ok all_ok order_ok len_pos last_ok',
          '', f'end {cns}'])
    mods.append((f'{cns}.Ok', blocks + [f'{ns}.Tree']))
    print(f'{name} chain: elements {len(elems)}, ancestors {len(need)}, table terms {sum(len(e) for e in tab)}, '
          f'cofactor terms {sum(len(c) for _, c in steps)}, products {sum(prods)}, max per identity {max(prods)}, '
          f'modules {len(batches)} (budget {mbudget})', flush=True)
    return mods, (0, f'{cns}.Ok', f'{cns}.ok')


# ---------------------------------------------------------------- main

def main():
    root, spec, name, esc = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
    budget, split_budget, mbudget = int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7])
    big_terms = int(sys.argv[8]) if len(sys.argv) > 8 else 2000
    piece = int(sys.argv[9]) if len(sys.argv) > 9 else 400
    Gb, hyps0, toks = read_data(spec, name)
    tree = read_node(toks, Gb)
    assert toks.i == len(toks.t)
    leaves, hypfaces = [], []
    rtree = relabel(tree, Gb, [], leaves, hypfaces)
    assert len(hypfaces) == 1 and len(hyps0) == 1
    systems = [[inF(Gb, g, F) for g, F in fs] for fs in hypfaces + [l[0] for l in leaves]]
    assert systems[0] == hyps0[0], 'the escape-ray system is not the system of the initial forms at the node'
    ns = f'L6CheckTrop.{name}'
    gb = f'Gb{name}'
    # Tree
    defs = []
    root_term, _ = emit_tree(rtree, piece, defs)
    L = ['import Lean6.Special.Comp.D88.Trop.Run' + name, '', *HEAD,
         f'/-! The covering tree of lean6_special for `{name}` with each leaf `.leaf` replaced by `.hyp k`, and the',
         f'systems `sys<k>` of the initial forms at the nodes `.hyp k` (`sys0`: the escape-ray system; `sys<k>`, k ≥ 1:',
         'the leaf `k - 1` in prefix order). -/', '', f'namespace {ns}', '',
         'open Lean6.Special.Comp Lean6.Special.Comp.D88.Trop', '']
    for k, fs in enumerate(hypfaces + [l[0] for l in leaves]):
        L.append(f'/-- The system of `.hyp {k}`. -/')
        L.append(f'def sys{k} : List (Poly Nat) := ({lst(f"({g}, {lst(map(str, F))})" for g, F in fs)} : '
                 f'List (Nat × List Nat)).map fun f => inF ({gb}.getD f.1 []) f.2')
    L += ['', '/-- The systems of the nodes `.hyp`. -/',
          'def hyps : List (List (Poly Nat)) := ' + lst(f'sys{k}' for k in range(len(systems))), '']
    for i, d in enumerate(defs):
        L += [f'/-- A subtree. -/', f'def n{i} : Node := {d}', '']
    L += ['/-- The covering tree. -/', f'def root : Node := {root_term}', '', f'end {ns}']
    write(root, f'{ns}.Tree', L)
    write(root, f'{ns}.Cover', [f'import {ns}.Tree', '', *HEAD, f'namespace {ns}', '',
          'open Lean6.Special.Comp Lean6.Special.Comp.D88.Trop', '',
          f'/-- The covering checks, with the systems `hyps` at the nodes `.hyp`. -/',
          f'theorem cover_ok : chk {P} {gb} hyps [] [] [] root = true := by decide +kernel', '', f'end {ns}'])
    # small leaves and certificate systems
    small = [k for k, l in enumerate(leaves, 1) if sum(len(q) for _, q in l[1]) + len(l[2]) <= big_terms]
    big = [k for k, l in enumerate(leaves, 1) if sum(len(q) for _, q in l[1]) + len(l[2]) > big_terms]
    L = [f'import {ns}.Tree', 'import L6SoundKSpec.TropLeaf', 'import Lean6.Special.D88.Trop.Final', '', *HEAD,
         f'/-! The leaves of the covering of `{name}` with at most {big_terms} cofactor terms: the identity of the leaf',
         'by the kernel (`leafOKK`), hence the torus emptiness of its system. -/', '', f'namespace {ns}', '',
         'open Lean6.Special.Comp Lean6.Special.Comp.D88.Trop Lean6.Special.D88.Trop L6KSpec.Trop', '']
    for k in small:
        _, cofs, cofR = leaves[k - 1]
        L += [f'theorem ok{k} : TorusEmptySys {P} sys{k} :=',
              f'  sysEmpty_of_leafOKK (cofs := {lst(f"({pos}, {poly(q)})" for pos, q in cofs)})',
              f'    (cofR := {poly(cofR)}) (by decide +kernel)', '']
    L += [f'end {ns}']
    write(root, f'{ns}.Small', L)
    deps = [f'{ns}.Tree: ', f'{ns}.Cover: {ns}.Tree', f'{ns}.Small: {ns}.Tree']
    bridges = []
    certs = []
    for k in big:
        _, cofs, cofR = leaves[k - 1]
        bypos = defaultdict(list)
        for pos, q in cofs:
            assert pos < len(systems[k])
            bypos[pos] += q
        idx = sorted(pos for pos in bypos if combine(bypos[pos], 18))
        # the generators term by term as `packN` writes them (rabin p last)
        gens = [[(c, tuple(m) + (0,) * (18 - len(m))) for c, m in systems[k][i]] for i in idx] + \
            [[(1, (0,) * 18), (P - 1, (1,) * 18)]]
        cf = [combine(bypos[i], 18) for i in idx] + [combine(cofR, 18)]
        certs.append((k, f'L{k}', 18, idx, gens, cf))
    hmono = None
    if esc != '-' and not esc.startswith('trace:'):
        cofsE = defaultdict(list)
        f = lzma.open(esc, 'rt') if esc.endswith('.xz') else open(esc)
        for line in f:
            t = line.split()
            if t and t[0] == 'h':
                # the certificate is of the monomial x^e, not of 1
                hmono = [int(x) for x in t[1:]]
                assert len(hmono) == 17 and max(hmono) < 128
            elif t:
                cofsE[int(t[0])].append((int(t[1]), [int(x) for x in t[2:]]))
        idx = sorted(cofsE)
        gens = [[(c, tuple(m) + (0,) * (17 - len(m))) for c, m in systems[0][i]] for i in idx]
        certs.append((0, 'Esc', 17, idx, gens, [combine(cofsE[i], 17) for i in idx]))
    for k, C, NV, idx, gens, cf in certs:
        cns = f'{ns}.{C}'
        label = (f'The escape-ray system of `{name}` (`sys0`)' if k == 0 else
                 f'The leaf of `.hyp {k}` of `{name}` (`sys{k}`) with the Rabinowitsch polynomial')
        mods = gen_cert(root, cns, label, NV, gens, cf, budget, split_budget, mbudget, f'{name}_{C}',
                        hmono if k == 0 else None)
        blocks = [m for m in mods if re.fullmatch(r'B\d+', m.rsplit('.', 1)[1])]
        ivs = [m for m in mods if m.rsplit('.', 1)[1].startswith('Ivl')]
        deps += [f'{cns}.Data: '] + [f'{b}: {cns}.Data' for b in blocks] + [f'{cns}.Bks: ' + ' '.join(blocks)]
        deps += [f'{m}: {cns}.Bks' for m in ivs] + [f'{cns}.Cover: ' + ' '.join(ivs), f'{cns}.Main: {cns}.Cover']
        pre = []
        if k == 0 and hmono is not None:
            g_rhs = f'({lst(map(str, idx))}.map fun i => sys0.getD i []).map packN'
            a = lst(map(str, hmono))
            pre = ['/-- `h` is the packed monomial. -/', f'theorem h_eq : h = packN [(1, {a})] := by decide +kernel', '']
            ok = [f'theorem ok : TorusEmptySys {P} sys0 :=',
                  f'  sysEmpty_of_monoIdent {lst(map(str, idx))} {a} (by decide +kernel) (by decide +kernel)',
                  f'    fun K _ _ x hg => h_eq ▸ ident (CharP.cast_eq_zero K {P}) x (by rw [gens_eq]; exact hg)']
        elif k == 0:
            g_rhs = f'({lst(map(str, idx))}.map fun i => sys0.getD i []).map packN'
            ok = [f'theorem ok : TorusEmptySys {P} sys0 :=',
                  f'  sysEmpty_of_ident (nv := 17) {lst(map(str, idx))} (by decide +kernel) fun K _ _ x hg =>',
                  f'    ident (CharP.cast_eq_zero K {P}) x (by rw [gens_eq]; exact hg)']
        else:
            g_rhs = f'(({lst(map(str, idx))}.map fun i => sys{k}.getD i []) ++ [rabin {P}]).map packN'
            ok = [f'theorem ok : TorusEmptySys {P} sys{k} :=',
                  f'  sysEmpty_of_leafIdent {lst(map(str, idx))} (by decide +kernel) fun K _ _ x hg =>',
                  f'    ident (CharP.cast_eq_zero K {P}) x (by rw [gens_eq]; exact hg)']
        write(root, f'{cns}.Bridge', [f'import {cns}.Main', f'import {ns}.Tree', 'import L6SoundKSpec.TropLeaf',
              'import Lean6.Special.D88.Trop.Final', '', *HEAD, f'namespace {cns}', '',
              'open L6KSpec.C4 L6KSpec.Trop Lean6.Special.Comp Lean6.Special.Comp.D88.Trop Lean6.Special.D88.Trop',
              f'open {ns} (sys{k})', '',
              '/-- The generators are the packed polynomials of the system with a cofactor. -/',
              f'theorem gens_eq : gens = {g_rhs} := by decide +kernel', '', *pre,
              f'/-- **The torus emptiness of `sys{k}`**, from the cofactor identity. -/', *ok, '', f'end {cns}'])
        deps.append(f'{cns}.Bridge: {cns}.Main {ns}.Tree')
        bridges.append((k, f'{cns}.Bridge', f'{cns}.ok'))
    if esc.startswith('trace:'):
        # the escape-ray system from a traced Buchberger run, as a chain of identities
        mods, bridge = gen_chain(root, ns, name, systems[0], esc[len('trace:'):], mbudget)
        deps += [f'{m}: ' + ' '.join(ds) for m, ds in mods]
        bridges.append(bridge)
    # Final
    okname = {k: f'{ns}.ok{k}' for k in small}
    okname.update({k: o for k, _, o in bridges})
    if esc == '-':
        # no certificate of the escape-ray system yet: everything but its checks and Final
        with open(os.path.join(root, 'L6CheckTrop', f'deps_{name}.txt'), 'w') as fh:
            fh.write('\n'.join(deps) + '\n')
        print(f'{name}: nodes {node_size(rtree)} pieces {len(defs)} systems {len(systems)} small_leaves {len(small)} '
              f'certificate_systems {len(certs)} (big leaves {big}); no escape-ray certificate, no Final', flush=True)
        return
    assert sorted(okname) == list(range(len(systems)))
    thm = {'KC': 'kc_torus_gamma', 'N4': 'n4_torus_gamma'}[name]
    L = [f'import {ns}.Cover', f'import {ns}.Small'] + [f'import {b}' for _, b, _ in bridges] + \
        ['import Lean6.Special.D88.Trop.CoverG', 'import Lean6.Special.D88.Trop.Final', '', *HEAD,
         f'/-! # Lemma 6.19(a), (iii)–(iv) for `{name}`, by the kernel',
         '',
         f'`{thm}` has the statement of lean6_special\'s `Lean6.Special.D88.Trop.{thm}`. The proof is',
         '`cover_soundG` (lean6_special) applied to the covering checked by the kernel (`cover_ok`: the tree of',
         'lean6_special with its leaves as nodes `.hyp`) and to the torus emptiness of the systems at the nodes `.hyp`',
         '(`hypsOK`: the identities of the leaves and the escape-ray certificate, by the kernel). -/', '',
         'namespace Lean6.Special.D88.TropK', '',
         'open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.D88.Trop Lean6.Special.D88.Trop', '',
         f'theorem {name.lower()}_hypsOK : HypsOK {P} {ns}.hyps :=',
         *wrap(''.join(f'L6KSpec.Trop.hypsOK_cons {okname[k]} (' for k in range(len(systems))) +
               f'L6KSpec.Trop.hypsOK_nil {P}' +
               ')' * len(systems), 116, '  '), '',
         f'theorem {name.lower()}_gb_ok : gbOK {P} {gb} = true := by decide +kernel', '',
         f'/-- **(iii)–(iv) for `{name}`, over any linearly ordered abelian group**, by the kernel. -/',
         f'theorem {thm} {{Γ : Type*}} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] (w : ℕ → Γ)',
         f'    (hw : ∃ i < 17, w i < 0) : TorusEmptyG {P} {gb} w :=',
         f'  cover_soundG {name.lower()}_gb_ok {name.lower()}_hypsOK {ns}.cover_ok w hw', '',
         'end Lean6.Special.D88.TropK']
    write(root, f'{ns}.Final', L)
    deps.append(f'{ns}.Final: {ns}.Cover {ns}.Small ' + ' '.join(b for _, b, _ in bridges))
    with open(os.path.join(root, 'L6CheckTrop', f'deps_{name}.txt'), 'w') as fh:
        fh.write('\n'.join(deps) + '\n')
    print(f'{name}: nodes {node_size(rtree)} pieces {len(defs)} systems {len(systems)} small_leaves {len(small)} '
          f'certificate_systems {len(certs)} (big leaves {big})', flush=True)


if __name__ == '__main__':
    main()
