"""Two facts about the 4788 solutions of KC at mu0 = (1, 2, 3, 30), from the certified boxes of Lemma 6.19(d).

Usage: python3 -I kc_ttest_count.py <kc_cert_1_2_3_30.jsonl>     (needs mpmath)

Each line of the input holds the midpoint "mid" and the radius "r" of a certified box (unknowns X2, X3, Y1, Y2, Y3,
Y4, p12, ..., p34 of KC_12, with X1 = 1 and X4 = 0; each midpoint entry a pair of decimal strings, real and imaginary
part, and each coordinate of the zero within r of it in real and imaginary part), and the certified lower bound
"torque_min_rel_lower" of the 32 sums of Lemma 6.17(b) at (m5, m6) = (1, 2).
1. The T-test over the bodies 1, 2, 3: some k in {1, 2, 3} has m_k |X_k|^(-1/2) > sum over l in {1, 2, 3}, l != k,
   of m_l |X_l|^(-1/2), with (m1, m2, m3) = (1, 2, 3). It is decided at the zero in each box in interval arithmetic
   (mpmath.iv, 50 digits): "fails" means that every k has margin < 0 on the whole box, "passes" that some k has
   margin > 0 on it. The script counts both and the undecided boxes.
2. |Y4| at the solutions with the smallest torque margins, against the median of |Y4| over all solutions, and the
   largest |Y_l/Y_4| (l <= 3) at the solutions with margin below 1e-4 (midpoints).
"""
import json, statistics, sys
from mpmath import iv, mp, mpf

mp.dps = iv.dps = 50
m = [1, 2, 3]
fail = passed = undecided = 0
rows = []
for line in open(sys.argv[1]):
    if not line.strip():
        continue
    rec = json.loads(line)
    r = iv.mpf([-mpf(repr(rec['r'])), mpf(repr(rec['r']))])
    absx = [iv.mpf(1)]
    for re_s, im_s in rec['mid'][:2]:
        re, im = iv.mpf(re_s) + r, iv.mpf(im_s) + r
        absx.append(iv.sqrt(re * re + im * im))
    T = [m[k] / iv.sqrt(absx[k]) for k in range(3)]
    margins = [T[k] - (T[(k + 1) % 3] + T[(k + 2) % 3]) for k in range(3)]
    if any(g.a > 0 for g in margins):
        passed += 1
    elif all(g.b < 0 for g in margins):
        fail += 1
    else:
        undecided += 1
    y4 = complex(float(rec['mid'][5][0]), float(rec['mid'][5][1]))
    ratio = max(abs(complex(float(rec['mid'][2 + l][0]), float(rec['mid'][2 + l][1]))) / abs(y4) for l in range(3))
    rows.append((rec['torque_min_rel_lower'], abs(y4), ratio))
print(f'solutions {fail + passed + undecided}; T-test over bodies 1, 2, 3 (interval arithmetic on the boxes): '
      f'fails at {fail}, passes at {passed}, undecided at {undecided}')
rows.sort()
print('six smallest torque margins and |Y4|: ' + '; '.join(f'{a:.3e} at {b:.3e}' for a, b, _ in rows[:6]))
small = [b for a, b, _ in rows if a < 1e-4]
print(f'{len(small)} margins below 1e-4, all with |Y4| >= {min(small):.3e}; median |Y4| over all solutions '
      f'{statistics.median(b for a, b, _ in rows):.3f}')
print(f'at these {len(small)} solutions max over l <= 3 of |Y_l/Y_4| = {max(c for a, b, c in rows if a < 1e-4):.3e}')
