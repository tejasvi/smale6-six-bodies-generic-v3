#!/usr/bin/env python3
"""Per-core table of the class-29 I-cores from ../data/coreC_part1.txt and coreC_part2.txt: the two factors of I,
and for each branch the factors of the eliminated polynomial, classified as R(ab;s)*mu15 (type 1), EQ (type 6),
type 16 (m_b^3 = +-m_a (m_a+m_p)^2) or other. Prints a markdown table (and writes ../data/coreC_table.md)."""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, '..', 'data')


def short(n):
    import ast
    t = ast.literal_eval(n)
    if t[0] == 'D' and len(t) == 3:
        return f'D{t[1]}{t[2]}'
    if t[0] in ('z', 'w') and t[1] == 'S':
        return f'{t[0]}[{"".join(map(str, t[2]))}]'
    if t[0] == 'V':
        return 'V' + ''.join(map(str, t[1]))
    return t[0]


def classify(facs):
    nontriv = [f for f in facs if f not in ('1', '-1') and not re.fullmatch(r'm\d', f)]
    ms = sorted(set(re.findall(r'm\d', ' '.join(nontriv))))
    if any('^12' in f or '^8*m' in f for f in nontriv) and len(nontriv) == 2:
        return f'type 1: R(ab;s)·μ15 in {",".join(ms)}'
    if len(nontriv) == 3 and len(ms) == 2:
        return f'type 6: EQ in {",".join(ms)}'
    if len(nontriv) == 2 and len(ms) == 3 and all('^3' in f for f in nontriv):
        return f'type 16 (rider) in {",".join(ms)}'
    return 'other: ' + '; '.join(x[:50] for x in nontriv)


def main():
    rows = []
    for fn in ('coreC_part1.txt', 'coreC_part2.txt'):
        p = os.path.join(DATA, fn)
        if not os.path.exists(p):
            continue
        txt = open(p).read()
        for block in txt.split('=== core ')[1:]:
            head = block.split('\n')[0]
            h = head.split()[0]
            cells = re.search(r'(\d+) cells', head).group(1)
            names = block.split('\n')[1].replace('names: ', '')
            brs = []
            for br in block.split('--- branch ')[1:]:
                first = br.split('\n')[0]
                if 'TIMEOUT' in br:
                    brs.append((first, 'TIMEOUT'))
                    continue
                facs = re.findall(r'_\[\d+\]=(.*)', br)
                brs.append((first, classify(facs)))
            rows.append((h, cells, names, brs))
    out = ['| core | cells | relations | branch 1 | branch 2 |', '|---|---|---|---|---|']
    for h, cells, names, brs in rows:
        rel = ' '.join(short(n) for n in names.split(' | '))
        b = [f'{x[0].split(" = ")[0]} = 0: {x[1]}' for x in brs] + ['', '']
        out.append(f'| {h} | {cells} | {rel} | {b[0]} | {b[1]} |')
    txt = '\n'.join(out)
    open(os.path.join(DATA, 'coreC_table.md'), 'w').write(txt + '\n')
    print(txt)
    print(len(rows), 'cores')


if __name__ == '__main__':
    main()
