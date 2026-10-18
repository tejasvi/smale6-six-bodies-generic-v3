#!/usr/bin/env python3
"""Generator of the kernel checks of the cofactor certificates of Lemma 7.9 (L6CheckC4), from the equations of the
charts as lean6_special prints them (gen/c4/dump_eqs.lean: lines "[mu]|chart|c:e0,…,e8;…") and the certificates
(lines "k c e0 … e8": cofactor of equation k, coefficient in [0, P), exponents; files CHART.cert or .cert.xz).

Per chart C, in the namespace L6CheckC4.C (module root L6CheckC4):
  data/c4k/C.bin, C.idx   the cofactor pieces and the buckets, read by `load_c4_cert` (as data/f4k of the F4 kernel
                          modules of lean6, scripts/kern/kf4_gen.py);
  C/Data.lean             the eleven equations packed (`gens`, the statement), `h = 1`, `load_c4_cert`;
  C/B<m>.lean             theorems `bucketOKp P (guardMask 9) … = true` (decide +kernel), at most MODULE_BUDGET term
                          products per module;
  C/Bks.lean, C/Ivl<q>.lean, C/Cover.lean
                          all buckets, the comparison of the codes by intervals of COVER_SPLIT codes (one module
                          each, checked in parallel), and the cover;
  C/Main.lean             the cover and h checks and `ident : (P : R) = 0 → (∀ g ∈ gens, eval 9 x g = 0) → 1 = 0`;
  C/Bridge.lean           `eqs_eq`: the equations of the paper at a point of the chart (`eqsAt (muOf MU) x`) are the
                          values of `gens`, and `no_zero` (no common zero in a nontrivial `ZMod P`-algebra).
The statements come from lean6_special's `K4.C4.Defs` (and `charts_eq` from `Comp.K4.C4.Check`), which have no
`native_decide` and no primality instances (with the native ones of `K4.C4.Final` in scope, instance search would
derive `Algebra (ZMod P) R` through the field structure).
The buckets split the identity by the exponents of a few variables chosen greedily (the ring is graded by them), so
that no pattern has more than SPLIT_BUDGET products; consecutive patterns are packed into buckets of at most
BUCKET_BUDGET products. Untrusted: every claim is checked by the kernel.
Usage: kc4_gen.py OUT_ROOT EQS MU P BUCKET_BUDGET SPLIT_BUDGET MODULE_BUDGET CHART=CERT ...
(MU as printed in EQS, e.g. "[3, 5, 7, 11]"; CHART one of s_c, s_p12, …, t_p34)"""
import lzma, math, os, sys
from collections import defaultdict

NV = 9
CHARTS = {'s_p12': (0, 2), 's_p13': (0, 3), 's_p14': (0, 4), 's_p23': (0, 5), 's_p24': (0, 6), 's_p34': (0, 7),
          's_c': (0, 8), 't_p12': (1, 2), 't_p13': (1, 3), 't_p14': (1, 4), 't_p23': (1, 5), 't_p24': (1, 6),
          't_p34': (1, 7), 't_c': (1, 8)}
COVER_SPLIT = int(os.environ.get('KC4_COVER', '16000'))
BT = 'Nat × Nat × List Nat × Piece'
HEAD = ['set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', '']


def read_eqs(path, mu, chart):
    eqs = []
    for line in open(path):
        m, ch, body = line.rstrip('\n').split('|')
        if m != mu or ch != chart:
            continue
        f = []
        for t in body.split(';'):
            c, e = t.split(':')
            f.append((int(c), tuple(int(x) for x in e.split(','))))
        eqs.append(f)
    assert len(eqs) == 11, (chart, len(eqs))
    return eqs


def read_cert(path, ng):
    f = lzma.open(path, 'rt') if path.endswith('.xz') else open(path)
    cofs = [[] for _ in range(ng)]
    for line in f:
        t = line.split()
        if not t:
            continue
        k, c, e = int(t[0]), int(t[1]), tuple(int(x) for x in t[2:])
        assert len(e) == NV
        cofs[k].append((c, e))
    return cofs


def key(e):
    return sum(x << (8 * v) for v, x in enumerate(e))


def choose_split(gens, cofs, h, budget):
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
    # binary splitting keeps the shifts of big numbers small
    if len(records) <= 64:
        n = 0
        for i, r in enumerate(records):
            assert 0 <= r < (1 << RB)
            n |= r << (i * RB)
        return n
    m = len(records) // 2
    return pack(records[:m], RB) | (pack(records[m:], RB) << (m * RB))


def gen_chart(root, eqs_path, mu, P, chart, cert, budget, split_budget, mbudget):
    gens = read_eqs(eqs_path, mu, chart)
    cofs = read_cert(cert, len(gens))
    h = [(1, (0,) * NV)]
    assert all(len(g) <= 64 for g in gens) and len(gens) <= 11
    assert all(max(e) < 128 for p in gens + cofs + [h] for _, e in p)
    a, b = CHARTS[chart]
    assert all(e[a] == 0 and e[b] == 0 for p in gens + cofs for _, e in p)
    assert all(0 <= c < P for p in cofs for c, _ in p)
    KB = 8 * NV
    Vp, cnt = choose_split(gens, cofs, h, split_budget)
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
    datadir = os.path.join(root, 'data', 'c4k')
    os.makedirs(datadir, exist_ok=True)
    binp = os.path.join(datadir, f'{chart}.bin')
    with open(binp, 'wb') as f:
        for n in chunks:
            bb = n.to_bytes((n.bit_length() + 7) // 8, 'little')
            f.write(len(bb).to_bytes(8, 'little'))
            f.write(bb)
    size = os.path.getsize(binp)
    with open(os.path.join(datadir, f'{chart}.idx'), 'w') as f:
        f.write('\n'.join(idx) + '\n')
    allc = sorted(c for pa in bcodes for c in bcodes[pa])
    bnd = [0]
    for q in range(COVER_SPLIT, len(allc), COVER_SPLIT):
        if allc[q] > bnd[-1]:
            bnd.append(allc[q])
    ivls = [(bnd[q], bnd[q + 1] if q + 1 < len(bnd) else 0) for q in range(len(bnd))]
    ns = f'L6CheckC4.{chart}'
    write(root, f'{ns}.Data', ['import L6KSpec.C4Check', 'import L6KSpec.C4Load', '', *HEAD,
        f'/-! Chart `{chart}` = {CHARTS[chart]} of Lemma 7.9 at μ = {mu}, p = {P}: the equations, `h = 1`, the cofactor',
        f'pieces and the buckets (split variables {Vp}). -/', '', f'namespace {ns}', '', 'open L6KSpec.C4', '',
        f'/-- The eleven equations of the chart (lean6_special\'s `Comp.C4.chartEqs {mu} {CHARTS[chart]}`, normalized), '
        'packed. -/',
        'def gens : List KPoly := [' + ', '.join('[' + ', '.join(f'({key(e)}, {c})' for c, e in g) + ']' for g in gens)
        + ']', '', '/-- `h = 1`. -/', 'def h : KPoly := [(0, 1)]', '',
        '/-! The cofactor pieces `pcs` and the buckets `b0`, `b1`, … (data for the kernel). -/',
        f'load_c4_cert "data/c4k/{chart}.bin" {size} "data/c4k/{chart}.idx"', '', f'end {ns}'])
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
    G = 'guardMask 9'
    for m, ks in enumerate(groups_b):
        mns = f'{ns}.B{m}'
        L = [f'import {ns}.Data', '', *HEAD, f'/-! Chart `{chart}`, buckets {ks[0]}–{ks[-1]}. -/', '',
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
        mods.append((mns, sum(bprod_list[k] for k in ks)))
    blocks = [m for m, _ in mods]
    write(root, f'{ns}.Bks', [f'import {m}' for m in blocks] + ['', *HEAD, f'namespace {ns}', '', 'open L6KSpec.C4', '',
         '/-- All buckets. -/', f'noncomputable def allBks : List ({BT}) := ' + ' ++ '.join(f'{b}.bks' for b in blocks),
         '', '/-- The intervals of the comparison of codes. -/',
         'def ivls : List (Nat × Nat) := [' + ', '.join(f'({x}, {y})' for x, y in ivls) + ']', '', f'end {ns}'])
    # one module per interval of the comparison of codes, so that the intervals are checked in parallel
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
        '  simp only [allBks, List.all_append, Bool.and_self, ' + ', '.join(f'{b}.all_ok' for b in blocks) + ']', '',
        'theorem cover : coverHead gens pcs ivls = true := by decide +kernel', '',
        f'theorem hparts : hOK {HB + 1} 20 h (allBks.map fun b => b.2.2.2) = true := by decide +kernel', '',
        f'/-- **The cofactor identity of chart `{chart}`**: where `{P} = 0`, the equations have no common zero. -/',
        f'theorem ident {{R : Type*}} [CommRing R] (hp : (({P} : ℕ) : R) = 0) (x : ℕ → R)',
        '    (hg : ∀ g ∈ gens, eval 9 x g = 0) : (1 : R) = 0 := by',
        f'  have e := cofmod_sound_ivl (p := {P}) (by norm_num) all_ok cover cover_all hparts hp x hg',
        '  simpa [h, eval_cons, monoEval_zero] using e', '', f'end {ns}'])
    ch = CHARTS[chart]
    write(root, f'{ns}.Bridge', [f'import {ns}.Main', 'import Lean6.Special.K4.C4.Defs', '', *HEAD,
        f'namespace {ns}', '', 'open L6KSpec.C4 Lean6.Special.K4.C4', '',
        f'/-- At a point of chart `{chart}` (`x {ch[0]} = x {ch[1]} = 1`), the equations of the paper are the values of '
        '`gens`. -/',
        f'theorem eqs_eq {{R : Type*}} [CommRing R] (x : ℕ → R) (h1 : x {ch[0]} = 1) (h2 : x {ch[1]} = 1) :',
        f'    eqsAt (muOf {mu}) x = gens.map (eval 9 x) := by',
        '  simp only [eqsAt, eqsZ, gens, List.map_cons, List.map_nil, List.cons.injEq, and_true]',
        '  refine ⟨' + ', '.join('?_' for _ in range(11)) + '⟩ <;>',
        '  simp [eqIZ, eqIIZ, eqIIIZ, aZ, xiZ, Pm, muOf, Finset.sum_filter, Finset.prod_filter, Fin.sum_univ_four,',
        '    Fin.prod_univ_four, pairIdx, eval, monoEval, keyExp, Finset.prod_range_succ, h1, h2] <;> ring', '',
        f'/-- **Chart `{chart}`**: no common zero in any nontrivial commutative `ZMod {P}`-algebra. -/',
        f'theorem no_zero {{R : Type*}} [CommRing R] [Nontrivial R] [Algebra (ZMod {P}) R] (x : ℕ → R)',
        f'    (h1 : x {ch[0]} = 1) (h2 : x {ch[1]} = 1) : ¬ ∀ e ∈ eqsAt (muOf {mu}) x, e = 0 := by',
        '  intro hz',
        f'  have hp : (({P} : ℕ) : R) = 0 := by',
        f'    rw [← map_natCast (algebraMap (ZMod {P}) R), ZMod.natCast_self, map_zero]',
        '  refine one_ne_zero (ident hp x fun g hg => ?_)',
        '  rw [eqs_eq x h1 h2] at hz',
        '  exact hz _ (List.mem_map_of_mem hg)', '', f'end {ns}'])
    prods = sum(bprod_list)
    print(f'{chart} split {Vp} buckets {len(bprod_list)} max_bucket {max(bprod_list)} products {prods} codes {len(allc)} '
          f'intervals {len(ivls)} bucket_modules {len(mods)} data_bytes {size}', flush=True)
    return chart, [(f'{ns}.Data', 0)] + mods + [(f'{ns}.Bks', 0)] + [(f'{ns}.Ivl{q}', 1) for q in range(len(ivls))] + \
        [(f'{ns}.Cover', len(ivls)), (f'{ns}.Main', 0), (f'{ns}.Bridge', 0)]


ORDER = ['s_p12', 's_p13', 's_p14', 's_p23', 's_p24', 's_p34', 's_c', 't_p12', 't_p13', 't_p14', 't_p23', 't_p24',
         't_p34', 't_c']


def write_final(root, mu, P):
    """L6CheckC4/Final.lean: NoZero MU P ∧ UnitIdeal MU P (lean6_special's statements) from the fourteen charts"""
    L = [f'import L6CheckC4.{c}.Bridge' for c in ORDER] + ['import Lean6.Special.K4.C4.Defs',
         'import Lean6.Special.Comp.K4.C4.Check', '',
         'set_option maxRecDepth 100000', '',
         f'/-! # Lemma 7.9 over `F_{P}` at `μ₀ = {mu}`, by the kernel',
         '',
         f'`NoZero {mu} {P} ∧ UnitIdeal {mu} {P}` (the statements of `Lean6.Special.K4.C4`, the first half of',
         '`lemma_7_9`) from the cofactor identities of the fourteen charts (`L6CheckC4.<chart>.no_zero`); the unit ideal',
         'from the absence of common zeros in the quotient ring, as in `Lean6.Special.K4.C4.chart_span`. -/', '',
         'namespace L6CheckC4', '', 'open Lean6.Special.K4.C4 Lean6.Special.Comp', '',
         '/-- One chart as a unit ideal, from the absence of common zeros (the proof of `chart_span`). -/',
         'theorem span_of_noZero (μL : List ℤ) (p : ℕ) (ch : ℕ × ℕ)',
         '    (hnz : ∀ (R : Type) [CommRing R] [Nontrivial R] [Algebra (ZMod p) R] (x : ℕ → R), x ch.1 = 1 → x ch.2 = 1 →',
         '      ¬ ∀ e ∈ eqsAt (muOf μL) x, e = 0) :',
         '    (1 : MvPolynomial ℕ (ZMod p)) ∈ Ideal.span {e | e ∈ eqsAt (muOf μL) (chartPt p ch)} := by',
         '  by_contra hI',
         '  set I := Ideal.span {e | e ∈ eqsAt (muOf μL) (chartPt p ch)}',
         '  have hne : I ≠ ⊤ := fun h => hI (h ▸ Submodule.mem_top)',
         '  have : Nontrivial (MvPolynomial ℕ (ZMod p) ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne',
         '  apply hnz (MvPolynomial ℕ (ZMod p) ⧸ I) (fun j => Ideal.Quotient.mk I (chartPt p ch j))',
         '  · simp [chartPt]',
         '  · simp [chartPt]',
         '  · rw [eqsAt_map]',
         '    intro e he',
         '    obtain ⟨e\', he\', rfl⟩ := List.mem_map.mp he',
         '    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span he\')', '',
         f'/-- No common zero on any chart, in any nontrivial commutative `ZMod {P}`-algebra. -/',
         f'theorem charts_no_zero : ∀ ch ∈ C4.charts, ∀ (R : Type) [CommRing R] [Nontrivial R] [Algebra (ZMod {P}) R]',
         f'    (x : ℕ → R), x ch.1 = 1 → x ch.2 = 1 → ¬ ∀ e ∈ eqsAt (muOf {mu}) x, e = 0 := by',
         '  intro ch hch R _ _ _ x h1 h2',
         '  rw [C4.charts_eq] at hch',
         '  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch',
         '  rcases hch with ' + ' | '.join('rfl' for _ in ORDER)]
    L += [f'  · exact {c}.no_zero x h1 h2' for c in ORDER]
    L += ['', f'/-- **Lemma 7.9 over `F_{P}`**, by the kernel: the first half of `Lean6.Special.K4.C4.lemma_7_9`. -/',
          f'theorem lemma_7_9_{P} : NoZero {mu} {P} ∧ UnitIdeal {mu} {P} :=',
          '  ⟨fun R _ _ _ ch hch x h1 h2 => charts_no_zero ch hch R x h1 h2,',
          '   fun ch hch => span_of_noZero _ _ ch (charts_no_zero ch hch)⟩', '', 'end L6CheckC4']
    write(root, 'L6CheckC4.Final', L)
    with open(os.path.join(root, 'L6CheckC4', 'deps_final.txt'), 'w') as f:
        f.write('L6CheckC4.Final: ' + ' '.join(f'L6CheckC4.{c}.Bridge' for c in ORDER) + '\n')


def write(root, mod, lines):
    path = os.path.join(root, *mod.split('.')) + '.lean'
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w') as f:
        f.write('\n'.join(lines) + '\n')


def _gen(args):
    return gen_chart(*args)


def main():
    root, eqs, mu, P = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    budget, split_budget, mbudget = int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7])
    tasks = []
    for a in sys.argv[8:]:
        chart, cert = a.split('=', 1)
        tasks.append((root, eqs, mu, P, chart, cert, budget, split_budget, mbudget))
    jobs = int(os.environ.get('KC4_JOBS', '1'))
    if jobs > 1:
        from multiprocessing import Pool
        with Pool(jobs) as pool:
            res = pool.map(_gen, tasks, chunksize=1)
    else:
        res = [_gen(t) for t in tasks]
    with open(os.path.join(root, 'L6CheckC4', 'deps.txt'), 'a') as f:
        for chart, mods in res:
            ns = f'L6CheckC4.{chart}'
            blocks = [m for m, _ in mods if m.rsplit('.', 1)[1][0] == 'B' and m.rsplit('.', 1)[1][1:].isdigit()]
            f.write(f'{ns}.Data: \n')
            for b in blocks:
                f.write(f'{b}: {ns}.Data\n')
            ivs = [m for m, _ in mods if m.rsplit('.', 1)[1].startswith('Ivl')]
            f.write(f'{ns}.Bks: ' + ' '.join(blocks) + '\n')
            for m in ivs:
                f.write(f'{m}: {ns}.Bks\n')
            f.write(f'{ns}.Cover: ' + ' '.join(ivs) + '\n')
            f.write(f'{ns}.Main: {ns}.Cover\n')
            f.write(f'{ns}.Bridge: {ns}.Main\n')
    if sorted(c for c, _ in res) == sorted(ORDER):
        write_final(root, mu, P)


if __name__ == '__main__':
    main()
