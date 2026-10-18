#!/usr/bin/env python3
"""Shared helpers for the residual analysis (read-only use of the engine data and of ../mechanisms).

- residual(): the 115 residual cells (first applicable 'comp' in mechanisms/data/coverage.jsonl)
- load_cell(c, i): the cell record of class c, cell i (cells.jsonl), with 'class' set
- core_of(c, i): the certified core used by the mechanisms coverage (cores_h.jsonl)
- single_of(c, i): the engine's single-term identity and term
- diag(c): the class diagram (edges, circles)"""
import glob, json, os, sys
from functools import lru_cache

ENG = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')   # the supplement
MECH = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'mechanisms')
sys.path.insert(0, os.path.join(MECH, 'scripts'))
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, '..', 'data')


@lru_cache(None)
def class_dir(c):
    d = glob.glob(os.path.join(ENG, '*', 'exact6', f'c{c}'))
    assert len(d) == 1, (c, d)
    return d[0]


@lru_cache(None)
def cells_of(c):
    return [json.loads(l) for l in open(os.path.join(class_dir(c), 'cells.jsonl'))]


def load_cell(c, i):
    r = dict(cells_of(c)[i])
    r['class'] = c
    return r


@lru_cache(None)
def classes():
    return json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'diagrams', 'n6.json')))['classes']


def diag_str(c):
    cl = classes()[c]
    s = ' '.join(f'{k}:{v}' for k, v in cl['edges'].items())
    if cl['zcircles']:
        s += ' zc' + ''.join(map(str, cl['zcircles']))
    if cl['wcircles']:
        s += ' wc' + ''.join(map(str, cl['wcircles']))
    return s


@lru_cache(None)
def residual():
    out = []
    for l in open(os.path.join(MECH, 'data', 'coverage.jsonl')):
        if '"first": "comp"' in l:
            r = json.loads(l)
            out.append(r)
    return out


@lru_cache(None)
def _cores():
    cores = {}
    for l in open(os.path.join(MECH, 'data', 'cores_h.jsonl')):
        r = json.loads(l)
        if r['certified'] is False:
            continue
        key = (r['class'], r['cell'])
        if key not in cores or r['certified'] is True:
            cores[key] = r
    return cores


def core_of(c, i):
    return _cores().get((c, i))


@lru_cache(None)
def _singles():
    s = {}
    for l in open(os.path.join(MECH, 'data', 'single.jsonl')):
        if '"class": ' not in l[:40]:
            continue
        r = json.loads(l)
        s[(r['class'], r['cell'])] = (r['identity'], r['term'])
    return s


def single_of(c, i):
    return _singles().get((c, i))


def system_of(c, i):
    """the engine's full system record (sec/p*.sec.jsonl) of a core cell: vars, eqs, names, sats (numeric masses)."""
    for f in glob.glob(os.path.join(class_dir(c), 'sec', 'p*.sec.jsonl')):
        for line in open(f):
            head = line[:60]
            if f'"cell": {i},' in head:
                r = json.loads(line)
                if r.get('cell') == i:
                    return r
    return None


def cores_file_of(c, i):
    for f in glob.glob(os.path.join(class_dir(c), 'sec', 'p*.cores.jsonl')):
        for line in open(f):
            if f'"cell": {i},' in line[:40]:
                r = json.loads(line)
                if r.get('cell') == i:
                    return r
    return None
