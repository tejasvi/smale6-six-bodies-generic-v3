import os, sys, random, subprocess, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import myprev
from fractions import Fraction as Fr
# toy 1: x + y + 1 (min convention): expected rays (-1,-1), (0,1), (1,0)
cells = myprev.prevariety([[(1,0),(0,1),(0,0)]], 2, [0])
print('toy1', [(c.w, c.faces) for c in cells])
# toy 2
cells = myprev.prevariety([[(2,1),(0,0)], [(1,0),(0,1),(0,0)]], 2, [0,1])
print('toy2', [(c.w, c.faces) for c in cells])
# test exact simplex fallback vs float on random small systems
random.seed(1)
bad = 0
for trial in range(300):
    d = random.randint(1, 4)
    m = random.randint(1, 6)
    A = [[random.randint(-3, 3) for _ in range(d)] for _ in range(m)]
    B = [[random.randint(-3, 3) for _ in range(d)] for _ in range(random.randint(0, 2))]
    k1, v1 = myprev.exact_motzkin_or_point(A, B, d)
    ok1 = (k1 == 'point') and myprev.verify_point(A, B, v1)
    ok1c = (k1 == 'cert') and myprev.verify_cert(A, B, v1[0], v1[1], d)
    f, t = myprev.feasible(A, B, d)
    if not (ok1 or ok1c) or (f != (k1 == 'point')):
        bad += 1
        print('MISMATCH', A, B, k1, v1, f, t)
print('random exact-vs-float trials, mismatches:', bad, myprev.STATS)
