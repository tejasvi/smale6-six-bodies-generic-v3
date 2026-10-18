# Independent check of Lemma 3 (shape list) at given integer masses: Singular eliminant of the full normalized
# 3-body system (my formulation: unknowns z1,z2,z3,w1,w2,w3,P12,P13,P23 with P = p, slice z1 - z2 = 1, NO centre-of-mass
# equations given explicitly), compared with my own exact construction of S_mu.
import sys, os, subprocess
from fractions import Fraction as Fr
import sympy as sp
m = [int(v) for v in sys.argv[1:4]]; wd = sys.argv[4]
out = os.path.join(wd, 'el_%d_%d_%d.txt' % tuple(m)); sing = out.replace('.txt', '.sing')
open(sing, 'w').write(r'''
LIB "elim.lib";
ring r = 0, (z1,z2,z3,w1,w2,w3,a,b,c,t), dp;
int m1 = %d; int m2 = %d; int m3 = %d;
ideal I = z1 - z2 - 1, t - z1 + z3,
  z1 - m2*a^3*(z1-z2) - m3*b^3*(z1-z3), z2 - m1*a^3*(z2-z1) - m3*c^3*(z2-z3), z3 - m1*b^3*(z3-z1) - m2*c^3*(z3-z2),
  w1 - m2*a^3*(w1-w2) - m3*b^3*(w1-w3), w2 - m1*a^3*(w2-w1) - m3*c^3*(w2-w3), w3 - m1*b^3*(w3-w1) - m2*c^3*(w3-w2),
  a^2*(z1-z2)*(w1-w2) - 1, b^2*(z1-z3)*(w1-w3) - 1, c^2*(z2-z3)*(w2-w3) - 1;
ideal J = std(I);
ideal E = eliminate(I, z1*z2*z3*w1*w2*w3*a*b*c);
link l = ":w %s";
write(l, "dim=" + string(dim(J)));
write(l, "vdim=" + string(vdim(J)));
write(l, "g=" + string(E[1]));
write(l, "ngens=" + string(size(E)));
close(l);
quit;
''' % (m[0], m[1], m[2], out))
subprocess.run(['nice', '-n', '10', 'Singular', '-q', sing], check=True, stdout=subprocess.DEVNULL)
info = dict(line.strip().split('=', 1) for line in open(out) if '=' in line)
t = sp.symbols('t')
g = sp.Poly(sp.sympify(info['g']), t)
# my S_mu
m1, m2, m3 = [Fr(v) for v in m]
x = t - 1
facs = [t**2 - t + 1]
# Lagrange quartics, products of conjugate quadratics, multiplied out by hand (see report)
facs += [t**4 - 5*t**3 + 9*t**2 - 5*t + 1, t**4 + t**3 - 2*t + 1, t**4 - 2*t**3 + t + 1]
for s12, s13, s23 in [(1, 1, 1), (1, 1, -1), (1, -1, -1), (1, -1, 1)]:
    A = (m1 + m2) * s12 * x**2 * (1 + x)**2 + m3 * s13 * x**2 - m3 * s23 * (1 + x)**2
    Bq = -m1 * s12 * x**2 * (1 + x)**2 + m1 * s13 * x**2 + (m2 + m3) * s23 * (1 + x)**2
    facs.append(sp.expand(x * A - Bq))
S = sp.Poly(sp.Mul(*facs), t)
sq = lambda p: sp.Poly(sp.quo(p, sp.gcd(p, p.diff(t))), t)
sg, ss = sq(g), sq(S)
ratio = sp.cancel(sg.as_expr() / ss.as_expr())
print('masses', m, 'dim', info['dim'], 'vdim', info['vdim'], 'ngens', info['ngens'], '| deg eliminant', g.degree(),
      'deg S', S.degree(), '| squarefree degs', sg.degree(), ss.degree(), '| equal up to const:', ratio.free_symbols == set(), ratio)
print('quartics:', [sp.Poly(f, t).all_coeffs() for f in facs[1:4]])
