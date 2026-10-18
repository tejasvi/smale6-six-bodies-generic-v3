#!/usr/bin/env python3
"""Text form of the labelled six-body diagrams written by count6.py and read by canon6.py (n6_labelled.txt; it
replaces the Python pickle of the original tree, which can run code when loaded). Line 1 is a comment; line 2 lists
the 15 pairs of bodies as two digits each; then one labelled diagram per line: the colours of the 15 pairs in that
order as 15 digits (0 none, 1 z, 2 w, 3 zw), the z-circle mask and the w-circle mask (bit k = body k).

  load(path)              -> (pairs, diags): pairs a list of (a, b), diags a list of (edge tuple, zmask, wmask),
                             equal to the objects that count6.py computes
  save(path, pairs, diags)
  labelled_io.py IN.pkl OUT.txt   converts a pickle of the original tree (and checks the round trip)"""
import sys


def save(path, pairs, diags):
    with open(path, 'w') as f:
        f.write('# labelled zw-diagrams of six bodies: edge colours of the 15 pairs (0 none, 1 z, 2 w, 3 zw), '
                'z-circle mask, w-circle mask\n')
        f.write('pairs ' + ' '.join(f'{a}{b}' for a, b in pairs) + '\n')
        for ev, cz, cw in diags:
            assert len(ev) == len(pairs) and all(0 <= x <= 3 for x in ev)
            f.write(''.join(map(str, ev)) + f' {cz} {cw}\n')


def load(path):
    with open(path) as f:
        assert f.readline().startswith('#')
        head = f.readline().split()
        assert head[0] == 'pairs'
        pairs = [(int(p[0]), int(p[1])) for p in head[1:]]
        diags = []
        for line in f:
            ev, cz, cw = line.split()
            assert len(ev) == len(pairs)
            diags.append((tuple(int(ch) for ch in ev), int(cz), int(cw)))
    return pairs, diags


if __name__ == '__main__':
    import pickle   # only to convert a pickle of the original tree; nothing here unpickles otherwise
    src, out = sys.argv[1], sys.argv[2]
    pairs, diags = pickle.load(open(src, 'rb'))
    save(out, pairs, diags)
    assert load(out) == (pairs, diags), 'round trip differs'
    print(f'{src}: {len(pairs)} pairs, {len(diags)} diagrams -> {out}; round trip equal')
