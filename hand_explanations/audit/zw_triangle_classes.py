"""The classes of Section 9.3 (after Corollary 9.10): diagrams with three bodies pairwise joined by zw-edges, none of
them circled and met by no other stroke.

Usage: python3 -I -B zw_triangle_classes.py N6_JSON PER_CLASS_TSV

Reads the 191 class representatives of enum/n6.json (edge kinds 1 = z-stroke, 2 = w-stroke, 3 = zw-edge; circles),
prints the classes with such a triangle, their Chang-Chen numbers and their numbers of listed cells (audit/per_class.tsv).
"""
import itertools, json, sys

n6 = json.load(open(sys.argv[1]))
cells, cc = {}, {}
for line in open(sys.argv[2]):
    f = line.rstrip('\n').split('\t')
    if f[0].isdigit():
        cc[int(f[0])], cells[int(f[0])] = f[1], int(f[4])
found = []
for ci, c in enumerate(n6['classes']):
    edges = {tuple(sorted((int(k[0]), int(k[1])))): v for k, v in c['edges'].items()}
    circ = set(c['zcircles']) | set(c['wcircles'])
    for T in itertools.combinations(range(6), 3):
        pairs = [tuple(sorted(p)) for p in itertools.combinations(T, 2)]
        if all(edges.get(p) == 3 for p in pairs) and not circ & set(T) \
                and not [e for e in edges if (e[0] in T or e[1] in T) and e not in pairs]:
            found.append(ci)
            break
print('classes: %d of %d' % (len(found), len(n6['classes'])))
for ci in found:
    print('class %d  CC %s  listed cells %d' % (ci, cc.get(ci) or '-', cells.get(ci, 0)))
print('listed cells in these classes: %d, in %d classes' % (sum(cells.get(ci, 0) for ci in found), sum(1 for ci in found if cells.get(ci, 0))))
