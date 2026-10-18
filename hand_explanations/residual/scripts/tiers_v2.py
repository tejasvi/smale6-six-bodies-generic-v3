#!/usr/bin/env python3
"""Tiered coverage for RESIDUAL_v2.md and MECHANISMS_v2.md: every one of the 91,273 nonpositive cells is put in the
first tier that excludes it, by the weakest input needed (referee report §5). Reads only stored data:
../mechanisms/data/coverage.jsonl (cell-level flags, 'first' = template or d-folder), ../data/global_cover.jsonl
(residual lemmas on all cells) and ../data/resid_cover.jsonl (witnesses on the 115 residual cells: the centre type
of R1*, TQ, TD).
  A1  every positive mass, cell-level hand lemma: T, P, C, B (MECHANISMS); B0, K, L (RESIDUAL)
  A2  every positive mass, core template whose hypotheses are initial forms of secondary identities (P4, LIN with a
      one-signed minor, B)
  A3  every positive mass, exact torque certificate (TD)
  G1  generic, cell-level hand lemma: E (class-level), E1, R1, R5, R6, Q; R1*(alpha/beta), W3, EQ2
  G2  generic, one secondary identity (exact certificate): R1*(gamma), TQ
  G3  generic core template LIN (maximal minors)
  D   only the hand proofs of d64/d88/d98 (paper §§6-7)
Output ../data/tiers_v2.jsonl (one line per cell) and ../data/tiers_v2_summary.json."""
import json, os, sys
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rkit as R
import exactlp as X
import lemmas_resid as LR

ECLS = {3, 148, 149, 40, 150, 183}
ALL_MECH = {'T', 'P', 'C', 'B'}
GEN_MECH = {'E1', 'R1', 'R5', 'R6', 'Q'}
ALL_RES = {'B0', 'K', 'L'}
GEN_RES = {'R1*', 'W3', 'EQ2'}
TEMPL_ALL = {'coreP4', 'coreLIN-all', 'coreB'}
DFIRST = {'d64', 'd88', 'd98'}


def main():
    mech = {}
    for l in open(os.path.join(R.MECH, 'data', 'coverage.jsonl')):
        r = json.loads(l)
        mech[(r['class'], r['cell'])] = r
    glob_ = {}
    for l in open(os.path.join(R.DATA, 'global_cover.jsonl')):
        r = json.loads(l)
        glob_[(r['class'], r['cell'])] = r
    resid = {}
    for l in open(os.path.join(R.DATA, 'resid_cover.jsonl')):
        r = json.loads(l)
        resid[(r['class'], r['cell'])] = r
    assert len(mech) == len(glob_) == 91273 and len(resid) == 115
    cnt = Counter()
    out = open(os.path.join(R.DATA, 'tiers_v2.jsonl'), 'w')
    for key in sorted(mech):
        m, g = mech[key], glob_[key]
        mfl = {k for k, v in m['lemmas'].items() if v}
        rfl = set(g['resid_lemmas'])
        sec = set()
        if key in resid:
            w = resid[key]['witness']
            # on a residual cell, R1* via a subset sum (gamma) rests on a secondary identity; R1* stays cell-level
            # only if it holds without the subset sum (the stored witness is the first one found)
            if 'R1*' in w and w['R1*']['centre'] == 'subset':
                C = LR.Ctx(R.load_cell(*key), X.Diag(R.classes()[key[0]]))
                if not LR.lemma_R1star(C, try_subset=False):
                    rfl.discard('R1*')
                    sec.add('R1*gamma')
            if 'TQ' in rfl:
                rfl.discard('TQ')
                sec.add('TQ')
            if 'TD' in rfl:
                rfl.discard('TD')
                sec.add('TD')
        cl_all = sorted((mfl & ALL_MECH) | (rfl & ALL_RES))
        cl_gen = sorted((mfl & GEN_MECH) | (rfl & GEN_RES) | ({'E'} if key[0] in ECLS else set()))
        first = m['first']
        if cl_all:
            tier = 'A1'
        elif first in TEMPL_ALL:
            tier = 'A2'
        elif 'TD' in sec:
            tier = 'A3'
        elif cl_gen:
            tier = 'G1'
        elif sec & {'R1*gamma', 'TQ'}:
            tier = 'G2'
        elif first.startswith('core'):
            tier = 'G3'
        elif first in DFIRST:
            tier = 'D'
        else:
            tier = 'NONE'
        cnt['tier ' + tier] += 1
        cnt['tier %s first %s' % (tier, first)] += 1
        cell_level = bool(cl_all or cl_gen)
        cnt['cell-level (any mass condition)'] += cell_level
        if tier in ('A2', 'A3', 'G2', 'G3'):
            cnt['secondary tiers'] += 1
            if cell_level:
                cnt['secondary tiers, also cell-level generic'] += 1
                cnt['secondary tiers, also cell-level generic: %s/%s %s %s' % (key[0], key[1], tier, cl_gen)] += 1
            else:
                cnt['secondary only (no cell-level lemma)'] += 1
        if tier == 'D':
            cnt['D class %d' % key[0]] += 1
        # every-mass recount, cumulative in the order of RESIDUAL.md: MECHANISMS (with templates), B0, K, L, TD
        old = bool(mfl & ALL_MECH) or first in TEMPL_ALL
        if old:
            cnt['allmass MECHANISMS (T, P, C, B, templates)'] += 1
        elif 'B0' in rfl:
            cnt['allmass gain B0'] += 1
        elif 'K' in rfl:
            cnt['allmass gain K'] += 1
        elif 'L' in rfl:
            cnt['allmass gain L'] += 1
        elif 'TD' in sec:
            cnt['allmass gain TD'] += 1
        if 'TD' in sec:
            cnt['TD flagged'] += 1
            if rfl & {'B0', 'K'}:
                cnt['TD flagged, also B0 or K'] += 1
        if cl_all:
            cnt['allmass cell-level only (A1)'] += 1
        if cl_all or 'TD' in sec:
            cnt['allmass cell-level + TD'] += 1
        if key in resid:
            cnt['residual tier ' + tier] += 1
            cnt['residual %s via %s' % (tier, ','.join(cl_all or cl_gen or sorted(sec)))] += 1
        out.write(json.dumps({'class': key[0], 'cell': key[1], 'kind': m['kind'], 'tier': tier,
                              'cell_level_allmass': cl_all, 'cell_level_generic': cl_gen,
                              'secondary': sorted(sec), 'mech_first': first}) + '\n')
    summary = dict(sorted(cnt.items()))
    json.dump(summary, open(os.path.join(R.DATA, 'tiers_v2_summary.json'), 'w'), indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == '__main__':
    main()
