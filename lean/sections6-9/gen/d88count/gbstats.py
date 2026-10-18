#!/usr/bin/env python3
"""Size of a Groebner basis printed by msolve (-g 2): number of elements, of terms, and the largest element.
Usage: gbstats.py FILE. Streams the file (it can be large)."""
import sys

n_el = 0
n_terms = 0
cur = 0
mx = 0
depth = 0
started = False
prev = ''
with open(sys.argv[1]) as f:
    while True:
        chunk = f.read(1 << 20)
        if not chunk:
            break
        for ch in chunk:
            if ch == '[':
                depth += 1
                if depth == 1:
                    started = True
                    cur = 1
                prev = ch
                continue
            if not started:
                continue
            if ch == ']':
                depth -= 1
                if depth == 0:
                    n_el += 1
                    n_terms += cur
                    mx = max(mx, cur)
                    started = False
                prev = ch
                continue
            if depth == 1:
                if ch == ',':
                    n_el += 1
                    n_terms += cur
                    mx = max(mx, cur)
                    cur = 1
                elif ch in '+-' and prev not in '^*,[\n ' and prev != 'e':
                    cur += 1
            if not ch.isspace():
                prev = ch
print('elements %d, terms %d, largest element %d terms' % (n_el, n_terms, mx))
