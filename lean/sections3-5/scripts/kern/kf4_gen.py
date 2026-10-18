#!/usr/bin/env python3
"""Generator of the kernel checks of the cofactor certificates (L6CheckK/F4) from certificate texts (L6CERT 1).

Per certificate H (file name H.txt or H.txt.gz), in the namespace L6CheckK.F4.C<H>:
  data/f4k/H.bin   chunks (8-byte little-endian length, then the bytes of a little-endian number): for each cofactor
                   its pieces (positive part, negative part), then for each bucket its codes and its part of h
                   (positive, negative);
  data/f4k/H.idx   the index read by `load_f4_cert` (pieces and buckets: counts, widths, chunk numbers);
  the data block   the generators and h (source literals: the statement), `certH`, and `load_f4_cert` (pieces, buckets);
  bucket blocks    theorems `bucketOK ... = true` (decide +kernel) with the list `bks` of their buckets;
  the main block   the cover, h and point checks and `cert : CertMeaning certH`.
The buckets split the identity by the exponents of a few variables chosen greedily (the ring is graded by them) so
that no pattern has more than BUCKET_BUDGET term products; consecutive patterns are then packed into buckets of at most
BUCKET_BUDGET products. Certificates with at most MODULE_BUDGET products are packed
(data and buckets) into modules L6CheckK/F4/P<n>, up to MODULE_BUDGET products and 64 certificates each; larger ones
get L6CheckK/F4/C<H>/Data and C<H>/B<m> (bucket blocks up to MODULE_BUDGET products). The main blocks go into
L6CheckK/F4/M<n>, 64 certificates each. L6CheckK/F4/modules.txt lists the modules by build stage with their cost.
Untrusted: every claim is checked by the kernel.
Usage: [KF4_JOBS=n] [KF4_SPLIT=SPLIT_BUDGET] kf4_gen.py OUT_ROOT BUCKET_BUDGET MODULE_BUDGET CERT ...
(the split variables are chosen for SPLIT_BUDGET products per pattern, default BUCKET_BUDGET; prints one line per
certificate)"""
import gzip, math, os, sys
from collections import defaultdict

NMASS = 6


def read_cert(path):
    f = gzip.open(path, 'rt') if path.endswith('.gz') else open(path)
    lines = [ln.split() for ln in f if ln.strip() and not ln.lstrip().startswith('#')]
    assert lines[0] == ['L6CERT', '1'], lines[0]
    a = lines[1]
    assert a[0] == 'nmass' and int(a[1]) == NMASS
    nvar, fixed = int(a[3]), int(a[5])
    ng = int(lines[2][1])
    pos = 3

    def poly(T):
        nonlocal pos
        out = []
        for _ in range(T):
            t = [int(x) for x in lines[pos]]
            pos += 1
            e = t[1:1 + NMASS] + [0] * nvar
            for q in range(t[1 + NMASS]):
                e[NMASS + t[2 + NMASS + 2 * q]] += t[3 + NMASS + 2 * q]
            out.append((t[0], tuple(e)))
        return out

    gens, cofs = [], []
    for i in range(ng):
        assert lines[pos][0] == 'gen' and int(lines[pos][1]) == i
        T = int(lines[pos][2]); pos += 1
        gens.append(poly(T))
    for i in range(ng):
        assert lines[pos][0] == 'cof' and int(lines[pos][1]) == i
        T = int(lines[pos][2]); pos += 1
        cofs.append(poly(T))
    assert lines[pos][0] == 'h'
    T = int(lines[pos][1]); pos += 1
    h = poly(T)
    assert pos == len(lines)
    return nvar, fixed, gens, cofs, h


def key(e):
    return sum(x << (8 * v) for v, x in enumerate(e))


def choose_split(gens, cofs, h, nv, budget):
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
    deg = [max((e[j] for p in gens + cofs + [h] for _, e in p), default=0) for j in range(nv)]
    Vp = []
    cnt = counts(Vp)
    while cnt and max(cnt.values()) > budget:
        best = None
        for j in range(nv):
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
    n = 0
    for i, r in enumerate(records):
        assert 0 <= r < (1 << RB)
        n |= r << (i * RB)
    return n


def gen_cert(path, root, budget, split_budget):
    H = os.path.basename(path).split('.')[0]
    nvar, fixed, gens, cofs, h = read_cert(path)
    nv = NMASS + nvar
    assert all(len(g) <= 16 for g in gens) and len(gens) < 16
    assert all(max(e) < 128 for p in gens + cofs + [h] for _, e in p)
    KB = 8 * nv
    Vp, cnt = choose_split(gens, cofs, h, nv, split_budget)
    pat = lambda e: tuple(e[j] for j in Vp)
    CB = max([abs(c).bit_length() for p in cofs for c, _ in p] + [1])
    HB = max([abs(c).bit_length() for c, _ in h] + [1])
    chunks = []

    def chunk(n):
        chunks.append(n)
        return len(chunks) - 1

    def nterms(terms, cb):
        """two chunks (positive, negative part), terms sorted by key; returns 'cp kp cn kn'"""
        out = []
        for sgn in (1, -1):
            ts = sorted((key(e), abs(c)) for c, e in terms if c * sgn > 0)
            n = pack([k | (c << KB) for k, c in ts], KB + cb)
            out.append(f'{len(ts)} {chunk(n)}')
        return ' '.join(out)

    # pieces of the cofactors, by pattern
    pieces, pidx = [], []
    for c in cofs:
        groups = defaultdict(list)
        for t in c:
            groups[pat(t[1])].append(t)
        pats = sorted(groups)
        pidx.append({a2: p for p, a2 in enumerate(pats)})
        pieces.append([(a2, groups[a2]) for a2 in pats])
    idx = [f'K {KB}', f'G {len(gens)}']
    for i, pl in enumerate(pieces):
        for _, ts in pl:
            idx.append(f'P {i} {CB} {nterms(ts, CB)}')
    # buckets
    hgroups = defaultdict(list)
    for t in h:
        hgroups[pat(t[1])].append(t)
    bcodes = defaultdict(list)
    bprods = defaultdict(int)
    for i, g in enumerate(gens):
        for j, (_, e) in enumerate(g):
            d = pat(e)
            for p, (a2, ts) in enumerate(pieces[i]):
                a = tuple(x + y for x, y in zip(d, a2))
                bcodes[a].append(i * 2 ** 24 + j * 2 ** 20 + p)
                bprods[a] += len(ts)
    # buckets: consecutive patterns packed up to the budget (a bucket of several patterns is the sum of their
    # identities, so it holds as well)
    allpat = sorted(set(bcodes) | set(hgroups))
    groups, cur, load = [], [], 0
    for a in allpat:
        w = bprods.get(a, 0) + len(hgroups.get(a, []))
        if cur and load + w > budget:
            groups.append(cur)
            cur, load = [], 0
        cur.append(a)
        load += w
    if cur:
        groups.append(cur)
    buckets = []
    for g in groups:
        codes = sorted(c for a in g for c in bcodes.get(a, []))
        hts = [t for a in g for t in hgroups.get(a, [])]
        prods = sum(bprods.get(a, 0) for a in g)
        ci = chunk(pack(codes, 28))
        hp = nterms(hts, HB)
        nlists = len(codes) + 1
        F = prods + len(hts) + 16
        R = math.ceil(math.log2(max(2, nlists + 1))) + 1
        idx.append(f'B {len(buckets)} {F} {R} {len(codes)} {ci} {HB} {hp}')
        buckets.append((F, R, None, None, prods))
    # data file
    datadir = os.path.join(root, 'data', 'f4k')
    os.makedirs(datadir, exist_ok=True)
    binp = os.path.join(datadir, f'{H}.bin')
    with open(binp, 'wb') as f:
        for n in chunks:
            b = n.to_bytes((n.bit_length() + 7) // 8, 'little')
            f.write(len(b).to_bytes(8, 'little'))
            f.write(b)
    size = os.path.getsize(binp)
    with open(os.path.join(datadir, f'{H}.idx'), 'w') as f:
        f.write('\n'.join(idx) + '\n')
    ns = f'L6CheckK.F4.C{H}'
    L = [f'/-! Certificate `{H}`: generators and `h` (the statement), cofactor pieces and buckets (split variables '
         f'{Vp}). -/', '', f'namespace {ns}', '', 'open L6.Poly L6K.F4', '',
         '/-- The generators. -/',
         'def gens : List Poly := [' + ', '.join(
             '[' + ', '.join(f'({key(e)}, {c})' for c, e in g) + ']' for g in gens) + ']', '']
    hch = [h[q:q + 1000] for q in range(0, len(h), 1000)] or [[]]
    for q, part in enumerate(hch):
        L.append(f'def h{q} : Poly := [' + ', '.join(f'({key(e)}, {c})' for c, e in part) + ']')
    L += [f'/-- The polynomial `h` ({len(h)} terms). -/', 'def h : Poly := ' + ' ++ '.join(f'h{q}' for q in range(len(hch))),
          '', '/-- The certificate: the generators and `h` (the cofactors are the sums of the pieces). -/',
          f'def certH : Cert := ⟨{nvar}, {fixed}, gens, [], h⟩', '',
          '/-! The cofactor pieces `pcs` and the buckets `b0`, `b1`, … (data for the kernel). -/',
          f'load_f4_cert "data/f4k/{H}.bin" {size} "data/f4k/{H}.idx"', '', f'end {ns}', '']
    prods = sum(b[4] for b in buckets)
    allc = sorted(c for a in bcodes for c in bcodes[a])
    ivls = None
    if len(allc) > COVER_SPLIT:
        bnd = [0]
        for q in range(COVER_SPLIT, len(allc), COVER_SPLIT):
            if allc[q] > bnd[-1]:
                bnd.append(allc[q])
        ivls = [(bnd[q], bnd[q + 1] if q + 1 < len(bnd) else 0) for q in range(len(bnd))]
    print(f'{H} nvar {nvar} split {Vp} buckets {len(buckets)} max_bucket {max(b[4] for b in buckets)} products {prods} '
          f'codes {len(allc)} data_bytes {size}')
    return {'H': H, 'ns': ns, 'G': f'(guardMask (6 + {nvar}))', 'HB': HB, 'fixed': fixed, 'data': L,
            'bprods': [b[4] for b in buckets], 'prods': prods, 'ivls': ivls}


BT = 'Nat × Nat × List Nat × Piece'
COVER_SPLIT = int(os.environ.get('KF4_COVER', '16000'))   # codes per interval of the cover of a large certificate
HEAD = ['set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', 'set_option linter.unusedSimpArgs false', '']


def bucket_block(c, ks, m):
    ns, G = c['ns'], c['G']
    mns = f'{ns}.B{m}'
    L = [f'/-! Certificate `{c["H"]}`, buckets {ks[0]}–{ks[-1]}. -/', '', f'namespace {mns}', '',
         f'open L6.Poly L6K.F4 {ns}', '']
    for k in ks:
        L.append(f'theorem ok{k} : bucketOK {G} b{k}.1 b{k}.2.1 gens pcs b{k}.2.2.1 b{k}.2.2.2 = true := by decide +kernel')
    L += ['', '/-- The buckets of this block. -/',
          f'noncomputable def bks : List ({BT}) := [' + ', '.join(f'b{k}' for k in ks) + ']', '',
          f'theorem all_ok : bks.all (fun b => bucketOK {G} b.1 b.2.1 gens pcs b.2.2.1 b.2.2.2) = true := by',
          '  simp only [bks, List.all_cons, List.all_nil, Bool.and_true, ' + ', '.join(f'ok{k}' for k in ks) + ']',
          '', f'end {mns}', '']
    return L, mns


def allbks_lines(blocks):
    return ['/-- All buckets. -/',
            f'noncomputable def allBks : List ({BT}) := ' + ' ++ '.join(f'{b}.bks' for b in blocks), '']


def cover_module(c, blocks):
    """the buckets of a large certificate and its cover, one theorem per interval of codes"""
    ns = c['ns']
    L = [f'namespace {ns}', '', 'open L6.Poly L6K.F4', ''] + allbks_lines(blocks)
    L.append('/-- The intervals of the comparison of codes. -/')
    L.append('def ivls : List (Nat × Nat) := [' + ', '.join(f'({a}, {b})' for a, b in c['ivls']) + ']')
    L.append('')
    for q, (a, b) in enumerate(c['ivls']):
        L.append(f'theorem cov{q} : L6K.F1.ivlCheck (allBks.flatMap fun b => b.2.2.1) (allCodes gens pcs) {a} {b} = true := '
                 'by decide +kernel')
    L += ['', 'theorem cover_all : ivls.all (fun lh => L6K.F1.ivlCheck (allBks.flatMap fun b => b.2.2.1) '
          '(allCodes gens pcs) lh.1 lh.2) = true := by',
          '  simp only [ivls, List.all_cons, List.all_nil, Bool.and_true, '
          + ', '.join(f'cov{q}' for q in range(len(c['ivls']))) + ']', '', f'end {ns}', '']
    return L


def main_block(c, blocks):
    ns, G, H = c['ns'], c['G'], c['H']
    L = [f'namespace {ns}', '', 'open L6.Poly L6K.F4', '']
    if c['ivls'] is None:
        L += allbks_lines(blocks)
    L += [f'theorem all_ok : allBks.all (fun b => bucketOK {G} b.1 b.2.1 gens pcs b.2.2.1 b.2.2.2) = true := by',
          '  simp only [allBks, List.all_append, Bool.and_self, ' + ', '.join(f'{b}.all_ok' for b in blocks) + ']', '']
    if c['ivls'] is None:
        L.append('theorem cover : coverOK 20 gens pcs (allBks.flatMap fun b => b.2.2.1) = true := by decide +kernel')
    else:
        L.append('theorem cover : coverHead gens pcs ivls = true := by decide +kernel')
    L += [f'theorem hparts : hOK {c["HB"]} 20 h (allBks.map fun b => b.2.2.2) = true := by decide +kernel',
          'theorem masses : h.all (fun t => decide (t.1 < 256 ^ 6)) = true := by decide +kernel',
          f'theorem nonzero : (evalAt 6 (hPoint ({c["fixed"]})) h != 0) = true := by decide +kernel', '',
          f'/-- **Certificate `{H}`**: in every commutative ring, `h` vanishes wherever the generators vanish, and `h` '
          'is nonzero at `hPoint F`. -/']
    if c['ivls'] is None:
        L.append('theorem cert : CertMeaning certH := cert_sound all_ok cover hparts masses nonzero')
    else:
        L.append('theorem cert : CertMeaning certH := cert_sound_ivl all_ok cover cover_all hparts masses nonzero')
    L += ['', f'end {ns}', '']
    return L


def write(root, mod, lines):
    path = os.path.join(root, *mod.split('.')) + '.lean'
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w') as f:
        f.write('\n'.join(lines) + '\n')


def _gen(args):
    return gen_cert(*args)


def main():
    root, budget, mbudget = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    jobs = int(os.environ.get('KF4_JOBS', '1'))
    split_budget = int(os.environ.get('KF4_SPLIT', str(budget)))
    tasks = [(p, root, budget, split_budget) for p in sys.argv[4:]]
    if jobs > 1:
        from multiprocessing import Pool
        with Pool(jobs) as pool:
            certs = pool.map(_gen, tasks, chunksize=1)
    else:
        certs = [_gen(t) for t in tasks]
    manifest = []           # (stage, module, cost in products)
    where = {}              # H -> (modules holding its buckets, bucket block names)
    # small certificates: data and buckets packed together, up to the module budget and 64 certificates
    small = [c for c in certs if c['prods'] <= mbudget]
    packs, cur, load = [], [], 0
    for c in small:
        if cur and (load + c['prods'] > mbudget or len(cur) >= 64):
            packs.append(cur)
            cur, load = [], 0
        cur.append(c)
        load += c['prods']
    if cur:
        packs.append(cur)
    for n, pk in enumerate(packs):
        mod = f'L6CheckK.F4.P{n}'
        L = ['import L6K.F4.Check', 'import L6K.F4.Load', '', *HEAD]
        for c in pk:
            L += c['data']
            bl, bname = bucket_block(c, list(range(len(c['bprods']))), 0)
            L += bl
            where[c['H']] = ([mod], [bname])
        write(root, mod, L)
        manifest.append((1, mod, sum(c['prods'] for c in pk)))
    # large certificates: a data module and bucket modules
    for c in certs:
        if c['prods'] <= mbudget:
            continue
        dmod = f'{c["ns"]}.Data'
        write(root, dmod, ['import L6K.F4.Check', 'import L6K.F4.Load', '', *HEAD] + c['data'])
        manifest.append((1, dmod, 0))
        groups, cur, load = [], [], 0
        for k, bp in enumerate(c['bprods']):
            if cur and load + bp > mbudget:
                groups.append(cur)
                cur, load = [], 0
            cur.append(k)
            load += bp
        if cur:
            groups.append(cur)
        mods, names = [], []
        for m, g in enumerate(groups):
            bl, bname = bucket_block(c, g, m)
            write(root, bname, [f'import {dmod}', '', *HEAD] + bl)
            manifest.append((2, bname, sum(c['bprods'][k] for k in g)))
            mods.append(bname)
            names.append(bname)
        where[c['H']] = (mods, names)
    # the covers of the large certificates, one module each
    for c in certs:
        if c['ivls'] is None:
            continue
        mod = f'{c["ns"]}.Cover'
        write(root, mod, ['import L6K.F4.Check'] + [f'import {m}' for m in where[c['H']][0]] + ['', *HEAD]
              + cover_module(c, where[c['H']][1]))
        manifest.append((3, mod, len(c['ivls'])))
        where[c['H']] = ([mod], where[c['H']][1])
    # the certificate theorems, 64 certificates per module
    for n in range(0, len(certs), 64):
        grp = certs[n:n + 64]
        mod = f'L6CheckK.F4.M{n // 64}'
        imports = []
        for c in grp:
            for m in where[c['H']][0]:
                if m not in imports:
                    imports.append(m)
        L = ['import L6SoundK.F4.Cert'] + [f'import {m}' for m in imports] + ['', *HEAD]
        for c in grp:
            L += main_block(c, where[c['H']][1])
        write(root, mod, L)
        manifest.append((4, mod, len(grp)))
    with open(os.path.join(root, 'L6CheckK', 'F4', 'modules.txt'), 'w') as f:
        for st, mod, cost in manifest:
            f.write(f'{st} {mod} {cost}\n')
    print('certificates', len(certs), 'packs', len(packs), 'modules', len(manifest))


if __name__ == '__main__':
    main()
