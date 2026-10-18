"""Floating-point version (the check of Table 3): two facts about the 4788 solutions of KC at mu0 = (1, 2, 3, 30), from the certified boxes of Lemma 6.19(d).

Usage: python3 -I kc_ttest_count_float.py <kc_cert_1_2_3_30.jsonl>

Each line of the input holds the midpoint "mid" of a certified box (unknowns X2, X3, Y1, Y2, Y3, Y4, p12, ..., p34
of KC_12, with X1 = 1 and X4 = 0; each entry a pair of decimal strings, real and imaginary part) and the certified
lower bound "torque_min_rel_lower" of the 32 sums of Lemma 6.17(b) at (m5, m6) = (1, 2).
1. The T-test over the bodies 1, 2, 3: some k in {1, 2, 3} has m_k |X_k|^(-1/2) > sum over l in {1, 2, 3}, l != k,
   of m_l |X_l|^(-1/2). The script counts the solutions at which it fails, and prints the smallest relative margin
   in absolute value, to show that the verdicts are far from the rounding of the midpoints (radii below 5e-54).
2. |Y4| at the solutions with the smallest torque margins, against the median of |Y4| over all solutions.
"""
import json, statistics, sys

m = [1.0, 2.0, 3.0]
fail = total = 0
closest = None
rows = []
for line in open(sys.argv[1]):
    if not line.strip():
        continue
    r = json.loads(line)
    total += 1
    mid = [complex(float(a), float(b)) for a, b in r['mid']]
    X = [1.0, abs(mid[0]), abs(mid[1])]
    T = [m[k] * X[k] ** -0.5 for k in range(3)]
    margin = max(T[k] - (sum(T) - T[k]) for k in range(3)) / sum(T)
    if margin <= 0:
        fail += 1
    if closest is None or abs(margin) < closest:
        closest = abs(margin)
    rows.append((r['torque_min_rel_lower'], abs(mid[5])))
print(f'solutions {total}; T-test over bodies 1, 2, 3 fails at {fail}; passes at {total - fail}; '
      f'smallest |relative margin| {closest:.3e}')
rows.sort()
print('six smallest torque margins and |Y4|: ' + '; '.join(f'{a:.3e} at {b:.3e}' for a, b in rows[:6]))
small = [b for a, b in rows if a < 1e-4]
print(f'{len(small)} margins below 1e-4, all with |Y4| >= {min(small):.3e}; median |Y4| over all solutions '
      f'{statistics.median(b for a, b in rows):.3f}')
