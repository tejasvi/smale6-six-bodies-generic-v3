#!/usr/bin/env python3
"""Generates the F3/F4 check modules (run from the package root; untrusted: Lean checks everything it states).

  L6Check/F34/Data/Common.lean   the embedded n6.json and open43.tsv
  L6Check/F34/Data/C<N>.lean     per class with cells: the embedded cells, single-term list, links, pass tags
  L6Check/F34/C<N>K<k>.lean      per chunk of at most CHUNK consecutive cells: one theorem `checkChunk ... = true`
                                 with the counts of the chunk (computed here from the same files)
  L6Check/F34/Cover.lean         the number of cells of every class (all 191), by native_decide
  L6Check/F34/Main.lean          imports everything; the table of chunks and the totals
  L6Check/F34/Axioms.lean        prints the axioms of every theorem
Usage: gen_checks.py [CHUNK]"""
import os, sys
CHUNK = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
D = 'L6Check/F34'
os.makedirs(f'{D}/Data', exist_ok=True)


def write(p, txt):
    if not os.path.exists(p) or open(p).read() != txt:
        open(p, 'w').write(txt)


def nonempty(p):
    return [l for l in open(p).read().split('\n') if l] if os.path.exists(p) else []


opens = {}
for l in nonempty('data/cells/open43.tsv'):
    if l.startswith('#'):
        continue
    c, _, cell = l.split('\t')
    opens.setdefault(int(c), set()).add(int(cell))
write(f'{D}/Data/Common.lean', '/-! F3/F4: the embedded class file and the list of the 43 open cells. -/\n\n'
      'namespace L6.F34.Data\n\n'
      '/-- `data/f1/n6.json`. -/\ndef n6 : String := include_str "../../../data/f1/n6.json"\n\n'
      '/-- `data/cells/open43.tsv`. -/\ndef open43 : String := include_str "../../../data/cells/open43.tsv"\n\n'
      'end L6.F34.Data\n')
ncells = {}
chunks = []
for c in range(191):
    cells = nonempty(f'data/cells/c{c}.jsonl')
    ncells[c] = len(cells)
    if not cells:
        continue
    single = {int(l.split()[0]) for l in nonempty(f'data/f34/single/c{c}.txt')}
    links = {}
    for l in nonempty(f'data/f4/links/c{c}.txt'):
        p = l.split()
        links[int(p[1])] = p[2]
    passes = {int(l.split()[0]): int(l.split()[1]) for l in nonempty(f'data/f34/pass/c{c}.txt')}
    lk = os.path.exists(f'data/f4/links/c{c}.txt')
    defs = [f'/-- `data/cells/c{c}.jsonl`. -/\ndef cells_{c} : String := include_str "../../../data/cells/c{c}.jsonl"',
            f'/-- `data/f34/single/c{c}.txt`. -/\ndef single_{c} : String := include_str "../../../data/f34/single/c{c}.txt"',
            (f'/-- `data/f4/links/c{c}.txt`. -/\ndef links_{c} : String := include_str "../../../data/f4/links/c{c}.txt"'
             if lk else f'/-- No cell of class {c} rests on a core. -/\ndef links_{c} : String := ""'),
            f'/-- `data/f34/pass/c{c}.txt`. -/\ndef pass_{c} : String := include_str "../../../data/f34/pass/c{c}.txt"']
    write(f'{D}/Data/C{c}.lean', f'/-! F3/F4: the embedded files of class {c}. -/\n\nnamespace L6.F34.Data\n\n' +
          '\n\n'.join(defs) + '\n\nend L6.F34.Data\n')
    n = len(cells)
    for k, lo in enumerate(range(0, n, CHUNK)):
        hi = min(n, lo + CHUNK)
        cnt = {'single': 0, 'core1': 0, 'core2': 0, 'opn': 0}
        ids = []
        for i in range(lo, hi):
            if i in opens.get(c, set()):
                cnt['opn'] += 1
            elif i in single:
                cnt['single'] += 1
            elif i in links:
                cnt['core1' if passes.get(i) == 1 else 'core2'] += 1
                if links[i] not in ids:
                    ids.append(links[i])
        ids.sort()
        name = f'C{c}K{k}'
        imports = ['L6F34.Check', 'L6Check.F34.Data.Common', f'L6Check.F34.Data.C{c}'] + [f'L6Check.Certs.C{i}' for i in ids]
        certs = ', '.join(f'("{i}", L6.Certs.C{i})' for i in ids)
        cstr = '{ single := %d, core1 := %d, core2 := %d, opn := %d }' % (cnt['single'], cnt['core1'], cnt['core2'], cnt['opn'])
        txt = '\n'.join(f'import {m}' for m in imports) + '\n\n'
        txt += (f'/-! F3/F4 (Proposition 5.3), class {c}, cells {lo} ≤ cell < {hi} of `data/cells/c{c}.jsonl`. -/\n\n'
                f'namespace L6.F34.Checks\n\nopen L6.F34 L6.F34.Data\n\n'
                f'-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats\n'
                f'set_option maxHeartbeats 0 in\n'
                f'/-- Every cell `{lo} ≤ cell < {hi}` of class {c} is excluded by a single term (Lemma 5.1, certified), or\n'
                f'its core polynomials are the initial forms of the cell and the generators of the named certificate\n'
                f'(Lemma 5.2), or it is one of the 43 open cells; with the counts {cstr}. -/\n'
                f'theorem F34_c{c}_k{k} : checkChunk {c} n6 cells_{c} single_{c} links_{c} pass_{c} open43\n'
                f'    [{certs}]\n'
                f'    {lo} {hi} {cstr} = true := by\n  native_decide\n\nend L6.F34.Checks\n')
        write(f'{D}/{name}.lean', txt)
        chunks.append((c, k, lo, hi, cnt))
# cover: the number of cells of every class
imports = ['L6F34.Check'] + [f'L6Check.F34.Data.C{c}' for c in range(191) if ncells[c]]
empty_defs = '\n'.join(f'/-- Class {c} has no listed cell. -/\ndef cells_{c} : String := include_str "../../data/cells/c{c}.jsonl"'
                       for c in range(191) if not ncells[c])
lhs = ', '.join(f'numCells cells_{c}' for c in range(191))
rhs = ', '.join(str(ncells[c]) for c in range(191))
write(f'{D}/Cover.lean', '\n'.join(f'import {m}' for m in imports) + '\n\n'
      '/-! F3/F4: the number of stored cells of each of the 191 classes (the chunks of each class cover them). -/\n\n'
      'namespace L6.F34.Data\n\n' + empty_defs + '\n\nend L6.F34.Data\n\nnamespace L6.F34.Checks\n\nopen L6.F34 L6.F34.Data\n\n'
      'set_option maxHeartbeats 0 in\n'
      '/-- The numbers of cells of the classes `0, …, 190`. -/\n'
      f'theorem F34_cover : [{lhs}] =\n    [{rhs}] := by\n  native_decide\n\nend L6.F34.Checks\n')
# SHA-256 of the embedded inputs: the cell lists (manifest data/cells/SHA256SUMS) and n6.json (published hash)
import hashlib
sums = dict((l.split()[1], l.split()[0]) for l in nonempty('data/cells/SHA256SUMS'))
for c in range(191):
    assert hashlib.sha256(open(f'data/cells/c{c}.jsonl', 'rb').read()).hexdigest() == sums[f'c{c}.jsonl'], c
n6h = hashlib.sha256(open('data/f1/n6.json', 'rb').read()).hexdigest()
lhs = ', '.join(f'L6.SHA256.sha256HexBytes cells_{c}.toUTF8' for c in range(191))
rhs = ', '.join(f'"{sums[f"c{c}.jsonl"]}"' for c in range(191))
write(f'{D}/Sha.lean', 'import L6Common.SHA256\nimport L6Check.F34.Data.Common\nimport L6Check.F34.Cover\n\n'
      '/-! F3/F4: the embedded inputs are the stored files: SHA-256 of the 191 embedded cell lists (equal to\n'
      '`data/cells/SHA256SUMS`, the hashes of the engine\'s `cells.jsonl`) and of the embedded `n6.json` (the published\n'
      'hash `0f2ae5d0…`). -/\n\nnamespace L6.F34.Checks\n\nopen L6.F34.Data\n\n'
      'set_option maxHeartbeats 0 in\n'
      '/-- The SHA-256 of the embedded cell lists of the classes `0, …, 190`. -/\n'
      f'theorem F34_sha_cells : [{lhs}] =\n    [{rhs}] := by\n  native_decide\n\n'
      'set_option maxHeartbeats 0 in\n'
      '/-- The SHA-256 of the embedded `n6.json`. -/\n'
      f'theorem F34_sha_n6 : L6.SHA256.sha256HexBytes n6.toUTF8 = "{n6h}" := by\n  native_decide\n\n'
      'end L6.F34.Checks\n')
# main: table and totals
rows = ',\n  '.join('(%d, %d, %d, %d, %d, %d, %d)' % (c, lo, hi, x['single'], x['core1'], x['core2'], x['opn']) for c, k, lo, hi, x in chunks)
tot = {k: sum(x[k] for *_, x in chunks) for k in ('single', 'core1', 'core2', 'opn')}
main = '\n'.join(f'import L6Check.F34.C{c}K{k}' for c, k, *_ in chunks) + '\nimport L6Check.F34.Cover\nimport L6Check.F34.Sha\n\n'
main += ('/-! F3/F4 (Proposition 5.3): the chunks, their counts, and the totals. Each row `(class, lo, hi, single, core1,\n'
         'core2, open)` is the statement of the theorem `F34_c<class>_k<k>`; the rows of a class cover its cells\n'
         '(`F34_cover`, `F34_chunks_cover`). -/\n\nnamespace L6.F34.Checks\n\n'
         '/-- The chunks and their counts. -/\n'
         f'def chunkTable : List (Nat × Nat × Nat × Nat × Nat × Nat × Nat) := [\n  {rows}]\n\n'
         '/-- The chunks of each class are consecutive from `0` to its number of cells (`F34_cover`). -/\n'
         'def coverOK (ncells : List Nat) : Bool :=\n'
         '  (List.range 191).all fun c =>\n'
         '    let rs := chunkTable.filter (·.1 == c)\n'
         '    let n := ncells.getD c 0\n'
         '    (rs.foldl (fun (pos : Option Nat) r => pos.bind fun p => if r.2.1 == p then some r.2.2.1 else none) (some 0)) == some n\n\n'
         f'theorem F34_chunks_cover : coverOK [{", ".join(str(ncells[c]) for c in range(191))}] = true := by decide +kernel\n\n'
         '/-- Totals: single-term cells, first-pass core cells, second-pass core cells, open cells. -/\n'
         'theorem F34_totals :\n'
         '    (chunkTable.map (·.2.2.2.1)).sum = %d ∧ (chunkTable.map (·.2.2.2.2.1)).sum = %d ∧\n'
         '    (chunkTable.map (·.2.2.2.2.2.1)).sum = %d ∧ (chunkTable.map (·.2.2.2.2.2.2)).sum = %d := by decide +kernel\n\n'
         'end L6.F34.Checks\n') % (tot['single'], tot['core1'], tot['core2'], tot['opn'])
write(f'{D}/Main.lean', main)
ax = 'import L6Check.F34.Main\n\n' + '\n'.join(f'#print axioms L6.F34.Checks.F34_c{c}_k{k}' for c, k, *_ in chunks) + \
     ('\n#print axioms L6.F34.Checks.F34_cover\n#print axioms L6.F34.Checks.F34_chunks_cover\n#print axioms L6.F34.Checks.F34_totals\n'
      '#print axioms L6.F34.Checks.F34_sha_cells\n#print axioms L6.F34.Checks.F34_sha_n6\n')
write(f'{D}/Axioms.lean', ax)
open(f'{D}/chunks.txt', 'w').write('\n'.join(f'C{c}K{k}' for c, k, *_ in chunks) + '\n')
print(len(chunks), 'chunks; totals', tot, 'cells', sum(ncells.values()))
