#!/usr/bin/env python3
"""Generator of the kernel checks of the boxes of Lemma 6.19(c) (N4, 11 centres) and (d) (KC, 12 centres).

Reads the box strings of version 1 from the chunk modules of lean6_special (Lean6/Special/Comp/D88/Boxes/<FAM>/D*.lean,
in the order of the imports of <FAM>/All.lean), parses them exactly as `parseBox` does (radius `⌈r·2^P⌉`, centres
nearest to `x·2^P`, ties away from zero; untrusted, the kernel checks the boxes it is given), sorts them by the real
part of the first centre, and writes:
  data/ksp/<FAM>_M<k>.bin           chunks (8-byte length, little-endian number), one per theorem of 8 boxes;
  data/ksp/<FAM>_sorted.txt         the box strings in the sorted order (for the classification of the KC boxes);
  L6CheckKSpec/<FAM>/M<k>.lean      theorems `(boxesOf W n 8 x_j).all <test> = true` (decide +kernel), the list
                                    `boxes` of the module and `all_ok`;
  L6CheckKSpec/<FAM>/All.lean       all boxes, `all_ok`, their number, and the sweep `sweepOK R allBoxes = true`.
Usage: ksp_gen.py SPEC_ROOT OUT_ROOT FAM BOXES_PER_MODULE   (FAM = N4 or KC)"""
import os, re, sys

P = 256


def parse_dec(s):
    neg = s.startswith('-')
    if neg:
        s = s[1:]
    ps = [p for p in (s.find('e'), s.find('E')) if p >= 0]
    m, e = (s[:min(ps)], s[min(ps) + 1:]) if ps else (s, '')
    ip, _, fp = m.partition('.')
    n = int(ip + fp)
    ex = int(e) if e else 0
    return neg, n, ex - len(fp)


def to_fix(d):
    neg, n, e = d
    if e >= 0:
        v = n * 10 ** e * 2 ** P
    else:
        v = (2 * n * 2 ** P + 10 ** (-e)) // (2 * 10 ** (-e))
    return -v if neg else v


def to_fix_ceil(d):
    _, n, e = d
    if e >= 0:
        return n * 10 ** e * 2 ** P
    return (n * 2 ** P + 10 ** (-e) - 1) // 10 ** (-e)


def parse_box(s):
    rs, *coords = s.split('|')
    rho = to_fix_ceil(parse_dec(rs))
    cs = []
    for c in coords:
        a, b = c.split(',')
        cs.append((to_fix(parse_dec(a)), to_fix(parse_dec(b))))
    return rho, cs


def zz(x):
    return 2 * x if x >= 0 else -2 * x - 1


def main():
    spec, root, fam, per_mod = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    n, test = {'N4': (11, 'n4BoxOKB'), 'KC': (12, 'kcBoxOKB')}[fam]
    d = os.path.join(spec, 'Lean6', 'Special', 'Comp', 'D88', 'Boxes', fam)
    mods = re.findall(r'^import Lean6\.Special\.Comp\.D88\.Boxes\.' + fam + r'\.(D\d+)$', open(os.path.join(d, 'All.lean')).read(), re.M)
    strings = []
    for m in mods:
        for line in open(os.path.join(d, m + '.lean')):
            mm = re.match(r'^\s*"([^"]*)"\s*[,\]]?\s*$', line)
            if mm:
                strings.append(mm.group(1))
    pairs = sorted(((parse_box(s), s) for s in strings), key=lambda bs: bs[0][1][0][0])
    boxes = [b for b, _ in pairs]
    assert all(len(cs) == n for _, cs in boxes)
    W = max(max(r.bit_length(), max(max(zz(x).bit_length(), zz(y).bit_length()) for x, y in cs)) for r, cs in boxes)
    R = max(r for r, _ in boxes)
    datadir = os.path.join(root, 'data', 'ksp')
    os.makedirs(datadir, exist_ok=True)
    with open(os.path.join(datadir, f'{fam}_sorted.txt'), 'w') as f:
        f.write('\n'.join(s for _, s in pairs) + '\n')
    outdir = os.path.join(root, 'L6CheckKSpec', fam)
    os.makedirs(outdir, exist_ok=True)
    head = ['set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', '']
    modnames = []
    for k in range(0, len(boxes), per_mod):
        chunk = boxes[k:k + per_mod]
        name = f'M{k // per_mod}'
        binp = os.path.join(datadir, f'{fam}_{name}.bin')
        thms = []
        with open(binp, 'wb') as f:
            for j in range(0, len(chunk), 8):
                grp = chunk[j:j + 8]
                recs = []
                for r, cs in grp:
                    recs.append(r)
                    for x, y in cs:
                        recs += [zz(x), zz(y)]
                v = 0
                for i, r in enumerate(recs):
                    v |= r << (i * W)
                b = v.to_bytes((v.bit_length() + 7) // 8, 'little')
                f.write(len(b).to_bytes(8, 'little'))
                f.write(b)
                thms.append(len(grp))
        size = os.path.getsize(binp)
        ns = f'L6CheckKSpec.{fam}.{name}'
        L = ['import L6KSpec.Boxes', 'import L6KSpec.Load', '', *head,
             f'/-! Boxes {k}–{k + len(chunk) - 1} of Lemma 6.19({"c" if fam == "N4" else "d"}), sorted by the real part '
             'of the first centre. -/', '', f'namespace {ns}', '', 'open Lean6.Special.D88.Boxes L6KSpec', '',
             f'load_box_chunks x "data/ksp/{fam}_{name}.bin" {size}', '']
        for j, c in enumerate(thms):
            L.append(f'theorem ok{j} : (boxesOf {W} {n} {c} x{j}).all {test} = true := by decide +kernel')
        L += ['', '/-- The boxes of this module. -/',
              'noncomputable def boxes : List Box := ' + ' ++ '.join(f'boxesOf {W} {n} {c} x{j}' for j, c in enumerate(thms)), '',
              f'theorem all_ok : boxes.all {test} = true := by',
              '  simp only [boxes, List.all_append, ' + ', '.join(f'ok{j}' for j in range(len(thms))) + ', Bool.and_self]',
              '', f'end {ns}']
        with open(os.path.join(outdir, f'{name}.lean'), 'w') as f:
            f.write('\n'.join(L) + '\n')
        modnames.append(ns)
    ns = f'L6CheckKSpec.{fam}'
    L = ['import L6KSpec.Boxes'] + [f'import {m}' for m in modnames] + ['', *head,
         f'/-! All boxes of Lemma 6.19({"c" if fam == "N4" else "d"}): the tests and the sweep. -/', '',
         f'namespace {ns}', '', 'open Lean6.Special.D88.Boxes L6KSpec', '',
         '/-- All boxes, sorted by the real part of the first centre. -/',
         'noncomputable def allBoxes : List Box := ' + ' ++ ('.join(f'{m}.boxes' for m in modnames)
         + ')' * (len(modnames) - 1), '',
         f'theorem all_ok : allBoxes.all {test} = true := by',
         '  simp only [allBoxes, List.all_append, ' + ', '.join(f'{m}.all_ok' for m in modnames) + ', Bool.and_self]', '',
         f'theorem length_eq : allBoxes.length = {len(boxes)} := by decide +kernel',
         f'theorem sweep : sweepOK {R} allBoxes = true := by decide +kernel', '', f'end {ns}']
    with open(os.path.join(outdir, 'All.lean'), 'w') as f:
        f.write('\n'.join(L) + '\n')
    print(f'{fam}: boxes {len(boxes)}, W {W}, R bits {R.bit_length()}, modules {len(modnames)}')
    with open(os.path.join(outdir, 'modules.txt'), 'w') as f:
        for m in modnames:
            f.write(f'1 {m}\n')
        f.write(f'2 {ns}.All\n')


if __name__ == '__main__':
    main()
