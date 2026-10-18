import json, os
from collections import Counter, defaultdict
exec(open('cumul_ref.py').read().split("F = {k: flags(k) for k in mine}")[0])
F = {k: flags(k) for k in mine}
rows = defaultdict(Counter)
for k, r in mech.items():
    if r['kind'] != 'single':
        continue
    idt, term = r['engine_single']
    idt = eval(idt) if isinstance(idt, str) else idt
    term = eval(term) if isinstance(term, str) else term
    if idt[0] == 'T':
        J = idt[1]
        t = term[0]
        if len(J) > 3:
            t = {'T1': 'T2', 'T2': 'T1'}[t]
        name = 'torque |J|=%d %s' % (min(len(J), 6 - len(J)), {'T1': 'd3 z_k w_l', 'T2': 'd3 w_k z_l'}[t])
    elif idt[0] == 'S':
        J = idt[2]
        name = 'subset |J|=%d %s' % (min(len(J), 6 - len(J)), term[0])
    else:
        name = str(idt[0]) + ' ' + str(term[0])
    f = F[k]
    rows[name]['cells'] += 1
    for n in ('T', 'P', 'C', 'B'):
        rows[name][n] += n in f
    rows[name]['TPCB'] += bool(f & {'T', 'P', 'C', 'B'})
    rows[name]['gen'] += bool(f & {'E', 'E1', 'R1', 'R5', 'R6', 'Q'})
    rows[name]['res'] += r['first'] == 'comp'
for name, c in sorted(rows.items(), key=lambda x: -x[1]['cells']):
    print('%-28s' % name, ' '.join('%s=%d' % (k, c[k]) for k in ('cells', 'T', 'P', 'C', 'B', 'TPCB', 'gen', 'res')))
