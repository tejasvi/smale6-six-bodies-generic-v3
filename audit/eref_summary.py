"""Summarize the engine referee's independent checks quoted in the paper (Table 2, Section 9).
Reads ENGINE_REFEREE_ROOT/out/* (engine/independent/out/ of the supplement).
Usage: python3 -I eref_summary.py ENGINE_REFEREE_ROOT"""
import json, os, sys, collections
root = sys.argv[1]
o = lambda f: os.path.join(root, 'out', f)
def load(fn):
    return [json.loads(l) for l in open(fn) if l.strip()] if os.path.exists(fn) else []
r = load(o('recert.jsonl'))
st = [x for x in r if x['stored_dim'] == -1]
print('recert: stored-certified distinct cores', len(st), '; Singular -1 and Macaulay2 unit:',
      sum(1 for x in st if x['singular_dim'] == -1 and x['m2'] == 'unit'), '; cells covered', sum(x['count'] for x in st))
a = load(o('recert_alt.jsonl'))
print('recert_alt: cores', len(a), '; subset of cell system', sum(1 for x in a if x['subset']),
      '; Singular (one mass 1) -1:', sum(1 for x in a if x['singular_fix1'] == -1),
      '; Macaulay2 all six masses', dict(collections.Counter(x['m2_all6'] for x in a)))
f1 = load(o('m2_fix1.jsonl')) + load(o('m2_fix1_last.jsonl'))
print('m2_fix1 (Macaulay2, one mass 1, for the all-six timeouts): records', len(f1), dict(collections.Counter(x.get('m2_fix1') for x in f1)))
L = load(o('lift_sample.jsonl'))
print('lift sample:', len(L), dict(collections.Counter(x['lift'] for x in L)), 'max cert bytes', max(x['cert_bytes'] for x in L))
for f in ['test_terms.txt', 'roberts.txt', 'negctl_c63.txt', 'certtotals.txt', 'single_check.txt', 'test_enum.txt']:
    print('---', f)
    print(open(o(f)).read().rstrip())
print('--- split_check.txt (last line)')
print(open(o('split_check.txt')).read().rstrip().splitlines()[-1])
cmp = load(o('cmp_rerun.jsonl'))
print('--- cmp_rerun.jsonl: classes', sorted(set(x.get('class') for x in cmp)))
