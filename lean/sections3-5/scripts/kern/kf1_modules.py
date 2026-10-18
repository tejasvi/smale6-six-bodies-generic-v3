#!/usr/bin/env python3
"""Generator of the kernel-check modules of F1 (L6CheckK/F1): the shards of the search, the representatives and the
global comparisons. Every module imports only the computational library (L6K.F1.Shard, no Mathlib).
Usage: kf1_modules.py SHARDS_TXT REPS_TXT OUT_ROOT COST_BUDGET REPS_PER_MODULE LEVEL
Writes OUT_ROOT/L6CheckK/F1/{Shards/S<k>,Reps/R<k>,Reps/All,Global}.lean and prints the module names."""
import os, sys

shards_txt, reps_txt, root, budget, rpm = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
level = int(sys.argv[6])
base = os.path.join(root, 'L6CheckK', 'F1')
os.makedirs(os.path.join(base, 'Shards'), exist_ok=True)
os.makedirs(os.path.join(base, 'Reps'), exist_ok=True)
HEAD = ['import L6K.F1.Shard', '', 'set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', '']


def write(path, lines):
    with open(path, 'w') as f:
        f.write('\n'.join(lines) + '\n')


# --- shards, in the order of the file (the order of edgesUpTo 6 LEVEL), grouped by a budget of cost
rows = [line.split() for line in open(shards_txt)]
groups, cur, load = [], [], 0
for i, t in enumerate(rows):
    cnt = int(t[1]) + 3 * (len(t) - 2)  # the kernel cost of a shard: about 3 leaves per labelled diagram found
    if cur and load + cnt > budget:
        groups.append(cur)
        cur, load = [], 0
    cur.append(i)
    load += cnt
if cur:
    groups.append(cur)
shard_mods = []
for k, g in enumerate(groups):
    ns = f'L6CheckK.F1.Shards.S{k}'
    L = HEAD + [f'/-! Shards {g[0]}–{g[-1]} of the search of Proposition 3.1 (prefixes of `edgesUpTo 6 {level}`). -/', '',
                f'namespace {ns}', '', 'open L6F1 L6K.F1', '']
    for j, i in enumerate(g):
        t = rows[i]
        L.append(f'def s{j} : Nat × Nat × List Nat := ({t[0]}, {t[1]}, [{", ".join(t[2:])}])')
    L.append('')
    for j, i in enumerate(g):
        L.append(f'theorem ok{j} : shardOK {level} s{j}.1 s{j}.2.1 s{j}.2.2 = true := by decide +kernel')
    L.append('')
    L.append('/-- The shards of this module. -/')
    L.append('def shards : List (Nat × Nat × List Nat) := [' + ', '.join(f's{j}' for j in range(len(g))) + ']')
    L.append('')
    L.append(f'theorem all_ok : shards.all (fun x => shardOK {level} x.1 x.2.1 x.2.2) = true := by')
    L.append('  simp only [shards, List.all_cons, List.all_nil, Bool.and_true, '
             + ', '.join(f'ok{j}' for j in range(len(g))) + ']')
    L += ['', f'end {ns}']
    write(os.path.join(base, 'Shards', f'S{k}.lean'), L)
    shard_mods.append(ns)

# --- representatives
reps = [line.split() for line in open(reps_txt)]
rep_mods = []
for k in range(0, len(reps), rpm):
    chunk = list(range(k, min(k + rpm, len(reps))))
    ns = f'L6CheckK.F1.Reps.R{k // rpm}'
    L = HEAD + [f'/-! Classes {chunk[0]}–{chunk[-1]} of `n6.json`: representative, orbit size, orbit codes. -/', '',
                f'namespace {ns}', '', 'open L6F1 L6K.F1', '']
    for i in chunk:
        t = reps[i]
        L.append(f'def r{i} : Diagram × Nat := (⟨{t[0]}, {t[1]}, {t[2]}⟩, {t[3]})')
        L.append(f'def oc{i} : List Nat := [{", ".join(t[4:])}]')
    L.append('')
    for i in chunk:
        L.append(f'theorem ok{i} : checkClassK r{i} = true ∧ orbitCodesK r{i}.1 = oc{i} := by decide +kernel')
    L += ['', f'end {ns}']
    write(os.path.join(base, 'Reps', f'R{k // rpm}.lean'), L)
    rep_mods.append(ns)


def repns(i):
    return f'L6CheckK.F1.Reps.R{i // rpm}'


L = ['import L6K.F1.Shard'] + [f'import {m}' for m in rep_mods] + ['', 'set_option maxRecDepth 1000000', '',
     '/-! The 191 classes of `n6.json` as data. -/', '',
     'namespace L6CheckK.F1', '', 'open L6F1 L6K.F1', '']
L.append('/-- The classes of `n6.json` (representative, number of labelled diagrams), in the order of the file. -/')
L.append('def classes6L : List (Diagram × Nat) := [' + ', '.join(f'{repns(i)}.r{i}' for i in range(len(reps))) + ']')
L.append('')
L.append('/-- The orbit codes of the classes, in the same order. -/')
L.append('def repCodes : List (List Nat) := [' + ', '.join(f'{repns(i)}.oc{i}' for i in range(len(reps))) + ']')
L.append('')
L.append('theorem classes_all : classes6L.all checkClassK = true := by')
L.append('  simp only [classes6L, List.all_cons, List.all_nil, Bool.and_true, '
         + ', '.join(f'({repns(i)}.ok{i}).1' for i in range(len(reps))) + ']')
L.append('')
L.append('theorem repCodes_eq : classes6L.map (fun x => orbitCodesK x.1) = repCodes := by')
L.append('  simp only [classes6L, repCodes, List.map_cons, List.map_nil, '
         + ', '.join(f'({repns(i)}.ok{i}).2' for i in range(len(reps))) + ']')
L += ['', 'end L6CheckK.F1']
write(os.path.join(base, 'Reps', 'All.lean'), L)

# --- global comparisons: All (the definitions), Global (the comparisons that do not need all codes), Codes/C<t>
# (the codes compared on one interval each) and Codes/All
allcodes = sorted(int(x) for t in rows for x in t[2:])
K = 32
bounds = [0]
for q in range(1, K):
    b = allcodes[q * len(allcodes) // K]
    if b > bounds[-1]:
        bounds.append(b)
ivls = [(bounds[q], bounds[q + 1] if q + 1 < len(bounds) else 0) for q in range(len(bounds))]
L = ['import L6K.F1.Shard', 'import L6K.F1.Ivl', 'import L6CheckK.F1.Reps.All'] + [f'import {m}' for m in shard_mods] + [
     '', 'set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', '',
     '/-! All shards, their codes, and the intervals of the comparison of codes. -/', '',
     'namespace L6CheckK.F1', '', 'open L6F1 L6K.F1', '']
L.append(f'/-- All shards, in the order of `edgesUpTo 6 {level}`. -/')
# right-nested, so that the kernel reaches every element in constant time (a left-nested chain of appends costs its
# depth per element)
L.append('def allShards : List (Nat × Nat × List Nat) := ' + ' ++ ('.join(f'{m}.shards' for m in shard_mods)
         + ')' * (len(shard_mods) - 1))
L.append('')
L.append('/-- The level of the shards: each shard is a prefix of this many pair kinds. -/')
L.append(f'def level : Nat := {level}')
L.append('')
L.append('/-- The codes listed in the shards. -/')
L.append('def codesAll : List Nat := allShards.flatMap (·.2.2)')
L.append('')
L.append('/-- The intervals of the comparison of codes. -/')
L.append('def ivls : List (Nat × Nat) := [' + ', '.join(f'({a}, {b})' for a, b in ivls) + ']')
L.append('')
L.append('theorem allShards_ok : allShards.all (fun x => shardOK level x.1 x.2.1 x.2.2) = true := by')
L.append('  simp only [allShards, level, List.all_append, Bool.and_self, Bool.true_and, Bool.and_true, '
         + ', '.join(f'{m}.all_ok' for m in shard_mods) + ']')
L += ['', 'end L6CheckK.F1']
write(os.path.join(base, 'All.lean'), L)

L = ['import L6CheckK.F1.All', 'import L6K.F1.SortR', '', 'set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', '',
     '/-! The checks of Proposition 3.1 that need all shards or all classes, except the comparison of codes. -/', '',
     'namespace L6CheckK.F1', '', 'open L6F1 L6K.F1', '']
L.append('theorem g_prefixes : allShards.map (·.1) = edgesUpTo 6 level := by decide +kernel')
L.append('theorem g_prefixes_nodup : strictSorted (msortR 20 (allShards.map (·.1))) = true := by decide +kernel')
L.append('theorem g_sum : (allShards.map (·.2.1)).sum = 932677 := by decide +kernel')
L.append('theorem g_codes_len : codesAll.length = 82712 := by decide +kernel')
L.append('theorem g_chain : chainOK 0 ivls = true := by decide +kernel')
L.append('theorem g_perms : checkPermsK 6 = true := by decide +kernel')
L.append('theorem g_keys : strictSorted (classes6L.map fun x => rawKey 6 x.1) = true := by decide +kernel')
L.append('theorem g_len : classes6L.length = 191 := by decide +kernel')
L += ['', 'end L6CheckK.F1']
write(os.path.join(base, 'Global.lean'), L)

os.makedirs(os.path.join(base, 'Codes'), exist_ok=True)
code_mods = []
for q, (a, b) in enumerate(ivls):
    ns = f'L6CheckK.F1.Codes.C{q}'
    L = ['import L6CheckK.F1.All', '', 'set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', '',
         f'/-! The codes in the interval {q}. -/', '', f'namespace {ns}', '', 'open L6F1 L6K.F1 L6CheckK.F1', '',
         f'theorem ok : ivlCheck codesAll repCodes.flatten {a} {b} = true := by decide +kernel', '', f'end {ns}']
    write(os.path.join(base, 'Codes', f'C{q}.lean'), L)
    code_mods.append(ns)
L = ['import L6CheckK.F1.All'] + [f'import {m}' for m in code_mods] + ['',
     '/-! The comparison of codes on all intervals. -/', '', 'namespace L6CheckK.F1', '', 'open L6F1 L6K.F1', '',
     'theorem g_ivls : ivls.all (fun lh => ivlCheck codesAll repCodes.flatten lh.1 lh.2) = true := by',
     '  simp only [ivls, List.all_cons, List.all_nil, Bool.and_true, ' + ', '.join(f'{m}.ok' for m in code_mods) + ']',
     '', 'end L6CheckK.F1']
write(os.path.join(base, 'Codes', 'All.lean'), L)

print('shard modules', len(shard_mods), 'rep modules', len(rep_mods))
print(' '.join(shard_mods + rep_mods + ['L6CheckK.F1.Reps.All', 'L6CheckK.F1.All', 'L6CheckK.F1.Global'] + code_mods
               + ['L6CheckK.F1.Codes.All']))
