#!/usr/bin/env python3
"""Prints the modules of the deps files given (lines `module: dependencies`, written by the generators) by levels of
the dependency order, one line per level, each module as PATH.lean:EST_GB for kf1_build.py. The estimate of a module
is that of the first rule whose regular expression matches its name (rules `REGEX=GB`, separated by spaces, in
KS_EST_RULES).
Usage: levels.py DEPS.txt...   (run from the root)"""
import os, re, sys

rules = [(re.compile(r.rsplit('=', 1)[0]), float(r.rsplit('=', 1)[1])) for r in os.environ['KS_EST_RULES'].split()]
deps = {}
for f in sys.argv[1:]:
    for line in open(f):
        m, _, ds = line.partition(':')
        if m.strip():
            deps[m.strip()] = ds.split()
level = {}


def lev(m):
    if m not in level:
        level[m] = 1 + max([lev(d) for d in deps[m] if d in deps], default=-1)
    return level[m]


for m in deps:
    lev(m)


def est(m):
    for rx, gb in rules:
        if rx.search(m):
            return gb
    sys.exit(f'no estimate for {m}')


for k in range(max(level.values()) + 1):
    print(' '.join(f'{m.replace(".", "/")}.lean:{est(m):g}' for m in sorted(deps) if level[m] == k))
