#!/usr/bin/env python3
"""Convert a reduced Groebner basis printed by msolve (`-g 2`, graded reverse lexicographic order) into the input of
the native test gen/d88count/br_testdim.lean: one polynomial per line, terms 'c:e0,...,e(n-1)' separated by spaces,
coefficients in [1, p), exponents in the variable order printed by msolve, terms sorted decreasingly in the graded
reverse lexicographic order with the first variable largest (Comp.Count.grevGtStd).
Usage: br_msolve2lst.py BASIS.txt OUT.lst P"""
import re
import sys


def key(e):
    # higher total degree first; for equal degree the smaller exponent at the last differing position is larger
    return (sum(e), tuple(-x for x in reversed(e)))


def main():
    src, dst, p = sys.argv[1], sys.argv[2], int(sys.argv[3])
    txt = open(src).read()
    head = txt[:txt.index('[')]
    m = re.search(r'#field characteristic:\s*(\d+)', head)
    assert m and int(m.group(1)) == p, 'characteristic'
    assert 'graded reverse lexicographical' in head, 'monomial order'
    names = [v.strip() for v in re.search(r'#variable order:\s*(.*)', head).group(1).split(',')]
    body = txt[txt.index('[') + 1:txt.rindex(']')]
    out = []
    for q in body.split(','):
        q = q.replace('\n', '').replace(' ', '')
        if not q:
            continue
        terms = {}
        for t in re.findall(r'[+-]?[^+-]+', q):
            sg = -1 if t[0] == '-' else 1
            t = t.lstrip('+-')
            c = 1
            e = [0] * len(names)
            for f in t.split('*'):
                if re.fullmatch(r'\d+', f):
                    c *= int(f)
                else:
                    m = re.fullmatch(r'([A-Za-z]\w*)(\^(\d+))?', f)
                    assert m, (f, q[:60])
                    e[names.index(m.group(1))] += int(m.group(3) or 1)
            k = tuple(e)
            terms[k] = (terms.get(k, 0) + sg * c) % p
        ts = sorted(((k, c) for k, c in terms.items() if c % p), key=lambda kc: key(kc[0]), reverse=True)
        out.append(' '.join('%d:%s' % (c, ','.join(map(str, k))) for k, c in ts))
    open(dst, 'w').write('\n'.join(out) + '\n')
    print(len(out), 'polys', sum(len(l.split()) for l in out), 'terms')


if __name__ == '__main__':
    main()
