#!/usr/bin/env python3
"""Leading-order exclusion of the 41 labelled four-body zw-diagrams (AK 2012 Fig. 8; engine enum/n4.json) at a mass
point, over F_p and over Q.  Used for the integrality lemma (DERIVATION.md, Lemma 5): every singular place of the
four-body system N_4 over a valuation with residue masses mu has one of these diagrams, and in each case the listed
leading-order equations hold; if each system generates the unit ideal, no singular place exists.

Classes (bodies a, b, c, d = a permutation of 1..4; colours z/w; the colour-swapped systems are the same polynomial
systems with z and w exchanged, hence give the same verdict):
 A  two isolated binaries (z-binary ab circled, w-binary cd circled): CM of each binary at order -2, cross distances,
    leading torque of {a, b} at exponent 2  (AK (12));
 B  isolated zw-triangle abc, no circles: three-body equilibrium (forces of a, b in both colours), distances (AK 5.3);
 C  zw-triangle abc plus a maximal z-stroke cd, all z-circled (AK's kite, colours exchanged): (K1) z-equations of a, b
    at -2, (K2) w-equations of a, b at -2, (K3) triangle distances, (K4) w-centre of mass at order 1 (w_c, w_d >= 2);
 D  quadrilateral: z-strokes ac, bd, w-strokes bc, ad, all circled: Rule 1c on the z-components + z-closeness (AK (14));
 E  fully zw-edged, no circles: four-body equilibrium.
Usage: n4_diagrams.py m1 m2 m3 m4 OUT.sing     (then: Singular -q OUT.sing)
"""
import itertools
import sys


def sing_class_A(m, a, b, c, d):
    ma, mb, mc, md = m[a], m[b], m[c], m[d]
    return ('ring r = CHAR,(za,zb,wc,wd,Pac,Pad,Pbc,Pbd,t),dp;',
            'ideal I = %d*za+%d*zb, %d*wc+%d*wd, Pac^2*za*wc+1, Pad^2*za*wd+1, Pbc^2*zb*wc+1, Pbd^2*zb*wd+1, '
            '%d*Pac+%d*Pad+%d*Pbc+%d*Pbd, za-1, t*wc-1;' % (ma, mb, mc, md, ma * mc, ma * md, mb * mc, mb * md))


def sing_class_B(m, a, b, c):
    ma, mb, mc = m[a], m[b], m[c]
    # zab = za - zb etc.; zac = zab + zbc ; normalization zab = 1, wab = 1
    return ('ring r = CHAR,(zbc,wbc,Pab,Pbc,Pac),dp;',
            'poly zab = 1; poly wab = 1; poly zac = zab + zbc; poly wac = wab + wbc;\n'
            'ideal I = %d*Pab^3*zab + %d*Pac^3*zac, -%d*Pab^3*zab + %d*Pbc^3*zbc, '
            '%d*Pab^3*wab + %d*Pac^3*wac, -%d*Pab^3*wab + %d*Pbc^3*wbc, '
            'Pab^2*zab*wab-1, Pbc^2*zbc*wbc-1, Pac^2*zac*wac-1;' % (mb, mc, ma, mc, mb, mc, ma, mc))


def sing_class_C(m, a, b, c, d):
    ma, mb, mc = m[a], m[b], m[c]
    return ('ring r = CHAR,(zbc,wab,wbc,Pab,Pbc,Pac),dp;',
            'poly A = 1; poly zab = 1; poly zac = zab + zbc; poly wac = wab + wbc;\n'
            'ideal I = A - (%d*Pab^3*zab + %d*Pac^3*zac), A - (-%d*Pab^3*zab + %d*Pbc^3*zbc), '
            '%d*Pab^3*wab + %d*Pac^3*wac, -%d*Pab^3*wab + %d*Pbc^3*wbc, '
            'Pab^2*zab*wab-1, Pbc^2*zbc*wbc-1, Pac^2*zac*wac-1, %d*wac + %d*wbc;'
            % (mb, mc, ma, mc, mb, mc, ma, mc, ma, mb))


def sing_class_C_noK1(m, a, b, c, d):
    """Kite without (K1): only (K2), (K3), (K4) -- the equations AK use for (20)."""
    ma, mb, mc = m[a], m[b], m[c]
    return ('ring r = CHAR,(zbc,wab,wbc,Pab,Pbc,Pac),dp;',
            'poly zab = 1; poly zac = zab + zbc; poly wac = wab + wbc;\n'
            'ideal I = %d*Pab^3*wab + %d*Pac^3*wac, -%d*Pab^3*wab + %d*Pbc^3*wbc, '
            'Pab^2*zab*wab-1, Pbc^2*zbc*wbc-1, Pac^2*zac*wac-1, %d*wac + %d*wbc;'
            % (mb, mc, ma, mc, ma, mb))


def sing_class_D(m, a, b, c, d):
    # z: [z_a] = [z_d] = Q, [z_b] = [z_c] = P ; m_a Q + m_c P = 0 ; m_b P + m_d Q = 0 ; (P, Q) != 0
    return ('ring r = CHAR,(P,Q,t),dp;',
            'ideal I = %d*Q + %d*P, %d*P + %d*Q, t*Q - 1;' % (m[a], m[c], m[b], m[d]))


def sing_class_E(m):
    lines = ['ring r = CHAR,(z3,z4,w3,w4,P12,P13,P14,P23,P24,P34),dp;',
             'poly z1 = 0; poly z2 = 1; poly w1 = 0; poly w2 = 1;']
    P = {(1, 2): 'P12', (1, 3): 'P13', (1, 4): 'P14', (2, 3): 'P23', (2, 4): 'P24', (3, 4): 'P34'}
    eqs = []
    for col in 'zw':
        for k in range(1, 5):
            terms = []
            for l in range(1, 5):
                if l != k:
                    terms.append('%d*%s^3*(%s%d-%s%d)' % (m[l - 1], P[(min(k, l), max(k, l))], col, k, col, l))
            eqs.append('+'.join(terms))
    for (k, l), nm in P.items():
        eqs.append('%s^2*(z%d-z%d)*(w%d-w%d)-1' % (nm, k, l, k, l))
    lines.append('ideal I = ' + ', '.join(eqs) + ';')
    return (lines[0], '\n'.join(lines[1:]))


def main():
    m = [int(x) for x in sys.argv[1:5]]
    out = sys.argv[5]
    blocks = []
    B = range(4)
    # A: choose the z-binary {a,b}
    for (a, b) in itertools.combinations(B, 2):
        c, d = [x for x in B if x not in (a, b)]
        blocks.append(('A z{%d%d} w{%d%d}' % (a + 1, b + 1, c + 1, d + 1), sing_class_A(m, a, b, c, d)))
    for tri in itertools.combinations(B, 3):
        a, b, c = tri
        blocks.append(('B tri{%d%d%d}' % (a + 1, b + 1, c + 1), sing_class_B(m, a, b, c)))
    for tri in itertools.combinations(B, 3):
        d = [x for x in B if x not in tri][0]
        for c in tri:
            a, b = [x for x in tri if x != c]
            blocks.append(('C tri{%d%d%d} stroke %d-%d' % (tri[0] + 1, tri[1] + 1, tri[2] + 1, c + 1, d + 1),
                           sing_class_C(m, a, b, c, d)))
            blocks.append(('C\' (no K1) tri{%d%d%d} stroke %d-%d' % (tri[0] + 1, tri[1] + 1, tri[2] + 1, c + 1, d + 1),
                           sing_class_C_noK1(m, a, b, c, d)))
    seen = set()
    for perm in itertools.permutations(B):
        a, b, c, d = perm
        key = (frozenset([frozenset((a, c)), frozenset((b, d))]), frozenset([frozenset((b, c)), frozenset((a, d))]))
        if key in seen:
            continue
        seen.add(key)
        blocks.append(('D z{%d%d,%d%d} w{%d%d,%d%d}' % (a + 1, c + 1, b + 1, d + 1, b + 1, c + 1, a + 1, d + 1),
                       sing_class_D(m, a, b, c, d)))
    blocks.append(('E full', sing_class_E(m)))
    txt = []
    for char in ('65521', '0'):
        for name, (ring, body) in blocks:
            txt.append(ring.replace('CHAR', char))
            txt.append(body)
            txt.append('ideal G = std(I);')
            txt.append('print("char %s | %s | unit ideal: " + string(G[1] == 1) + " | dim " + string(dim(G)));'
                       % (char, name))
            txt.append('kill r;')
    txt.append('quit;')
    open(out, 'w').write('\n'.join(txt) + '\n')
    print(len(blocks), 'systems per characteristic')


if __name__ == '__main__':
    main()
