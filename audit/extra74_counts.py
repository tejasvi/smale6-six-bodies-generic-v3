#!/usr/bin/env python3
"""Counts of the rules that exclude the 74 classes of diagrams not among the 117 of Chang-Chen (diagrams/extra74.json):
for each set of failing rules, the number of classes; the classes excluded by Rule T alone; the classes that fail Rule T.
Written for the supplement (the stored audit/extra74_counts.txt had no shipped producer); it reproduces that file byte
for byte.  Usage: python3 -I -B audit/extra74_counts.py diagrams/extra74.json > extra74_counts.txt"""
import collections, json, sys

d = json.load(open(sys.argv[1]))
c = collections.Counter(tuple(v) for v in d.values())
print('classes', len(d))
for k, v in c.most_common():
    print(v, k)
print('only RuleT:', [int(k) for k, v in d.items() if v == ['RuleT']])
print('with RuleT:', sum('RuleT' in v for v in d.values()))
