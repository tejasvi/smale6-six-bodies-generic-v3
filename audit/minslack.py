import glob, json, sys
mn = (9, None); cnt = 0
for f in glob.glob(sys.argv[1] + '/*/exact6/c*/cells.jsonl'):
    for i, l in enumerate(open(f)):
        r = json.loads(l); cnt += 1
        if r['slack'] < mn[0]:
            mn = (r['slack'], f.split('/')[-2], i, r['sumx'])
print(cnt, mn)
