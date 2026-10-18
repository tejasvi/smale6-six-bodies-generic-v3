#!/usr/bin/env python3
"""Exact check of Lemma B (DERIVATION.md) at a rational mass triple, independent of its proof.

Runs Singular on the full normalized three-body system (slice z_12 = 1, all three z- and w-equations, the three
distance equations, centre of mass), eliminates every variable except t = z_13, and compares the eliminant g(t)
with the shape polynomials of shape_polys.py: the squarefree part of g must equal the squarefree part of the product
of the shape polynomials (up to a constant). Since the eliminant's roots are exactly the z-shapes of the solutions,
this shows that the shapes at these masses are exactly the roots of the Lemma B polynomials. It also reports
dim, vdim and vdim of the radical of the system (number of solutions with and without multiplicity).
Usage: lemB_check.py mu1 mu2 mu3 WORKDIR      (integers)
"""
import sys, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction
import sympy as sp
import shape_polys as SP

TEMPLATE = r'''
LIB "elim.lib";
LIB "primdec.lib";
ring r = 0, (z2,z3,w1,w2,w3,p12,p13,p23,t), dp;
int m1 = %(m1)d; int m2 = %(m2)d; int m3 = %(m3)d;
poly z1 = 1 + z2;
ideal I =
  m1*z1 + m2*z2 + m3*z3,
  m1*w1 + m2*w2 + m3*w3,
  z1 - m2*p12^3*(z1-z2) - m3*p13^3*(z1-z3),
  z2 - m1*p12^3*(z2-z1) - m3*p23^3*(z2-z3),
  z3 - m1*p13^3*(z3-z1) - m2*p23^3*(z3-z2),
  w1 - m2*p12^3*(w1-w2) - m3*p13^3*(w1-w3),
  w2 - m1*p12^3*(w2-w1) - m3*p23^3*(w2-w3),
  w3 - m1*p13^3*(w3-w1) - m2*p23^3*(w3-w2),
  p12^2*(z1-z2)*(w1-w2) - 1,
  p13^2*(z1-z3)*(w1-w3) - 1,
  p23^2*(z2-z3)*(w2-w3) - 1,
  t - (z1 - z3);
ideal J = std(I);
int d = dim(J); int v = vdim(J);
int vr = vdim(std(radical(J)));
ideal E = eliminate(I, z2*z3*w1*w2*w3*p12*p13*p23);
link l = ":w %(out)s";
write(l, "dim=" + string(d));
write(l, "vdim=" + string(v));
write(l, "vdim_radical=" + string(vr));
write(l, "ngens=" + string(size(E)));
write(l, "g=" + string(E[1]));
close(l);
quit;
'''


def main():
    m = [int(v) for v in sys.argv[1:4]]
    wd = sys.argv[4]
    os.makedirs(wd, exist_ok=True)
    out = os.path.join(wd, 'elim_%d_%d_%d.txt' % tuple(m))
    sing = os.path.join(wd, 'elim_%d_%d_%d.sing' % tuple(m))
    with open(sing, 'w') as f:
        f.write(TEMPLATE % {'m1': m[0], 'm2': m[1], 'm3': m[2], 'out': out})
    subprocess.run(['Singular', '-q', sing], check=True, stdout=subprocess.DEVNULL)
    info = dict(line.strip().split('=', 1) for line in open(out) if '=' in line)
    t = sp.symbols('t')
    g = sp.Poly(sp.sympify(info['g']), t)
    prod = sp.Poly(1, t)
    for name, co in SP.all_shape_polys([Fraction(v) for v in m]):
        prod *= sp.Poly(list(reversed(co)), t)
    def sqfree(p):
        return sp.Poly(sp.quo(p.as_expr(), sp.gcd(p.as_expr(), sp.diff(p.as_expr(), t))), t)
    sg, sq = sqfree(g), sqfree(prod)
    ratio = sp.cancel(sg.as_expr() / sq.as_expr())
    ok = ratio.free_symbols == set() and ratio != 0
    print('masses', m, ': dim', info['dim'], 'vdim', info['vdim'], 'vdim(radical)', info['vdim_radical'],
          '| eliminant degree', g.degree(), 'generators', info['ngens'],
          '| squarefree degrees: eliminant', sg.degree(), 'Lemma B product', sq.degree(),
          '| equal up to a constant:', ok)
    print('factorization of the eliminant:', sp.factor_list(g.as_expr()))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
