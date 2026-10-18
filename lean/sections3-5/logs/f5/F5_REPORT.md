# F5: Proposition 5.9 (the clique census) in Lean 4

Proposition 5.9: of the 91,273 cells of Proposition 4.5, 86,938 have a clique as in Corollary 5.8; they include all
cells of 18 classes, among them all 44,247 cells of diagram 7 and all 32,864 cells of diagram 11 of Chang and Chen.
The text after it: the other 4,335 cells include 32 of the 43 open cells of Proposition 5.3 and the cell 122 of
class 30; the 11 open cells of diagram 64 have a clique of four bodies; the other nine cells whose cores rest on
Singular alone have a clique.

All of this is checked in Lean 4 (toolchain v4.35.0-rc3), by `native_decide` on the stored cells embedded with
`include_str`, and the numbers agree with the census program of the paper, cell by cell. No discrepancy.

## Files

| file | contents |
|---|---|
| `L6F5/Json.lean` | reading (`parseVal`) and writing (`render`, the layout of `json.dumps`) of the nested arrays of strings and numbers in the `argmin` values; byte search helpers |
| `L6F5/Clique.lean` | `Cell` (the argmin sets of the 12 equations of the bodies), `readCell` (all 14 base identities, each once, labels of the expected form), the conditions of Corollary 5.8 (`kindOK`, `internalIn`, `generators`, `rank`, `dimL`, `dimsOK`, `cliqueOK`), `has3`, `has4`, `hasClique`; `forcedOK` (forced argmin sets = the diagram's) |
| `L6F5/Census.lean` | lines of a file, `readLine` (with the round-trip check), `Tally`, `Status`, `census`, `statuses`, `cellStatus`, `readOpen`, `openStatus`, `ccInClass`, `sumFor` |
| `L6Check/F5/Data.lean` | the embedded files: `c0` … `c190` (`data/cells/c<N>.jsonl`), `files`, `n6` (`data/f1/n6.json`), `open43` (`data/cells/open43.tsv`), `sums` (`data/cells/SHA256SUMS`); written by `scripts/f5/gen_data.py` |
| `L6Check/F5/Census.lean` | `table`, `census_table`, `F5_main`, `F5_three_four`, `F5_forced`, `openTable`, `open_status`, `F5_open`, `singularOnly`, `F5_singular`, `F5_cc`, `rank_unit_vectors` |
| `L6Check/F5/Sha.lean` | `files_length`, `cells_sha256`, `sums_lines`, `sums_sha256`, `open43_sha256`, `n6_sha256` |
| `L6Check/F5/Axioms.lean` | prints the statements and the axioms into the build log |
| `L6Check/F5/Print.lean` | prints the census table, the open cells, the cells without a clique and the cells with a clique of four bodies into the build log (not a check) |
| `L6Sound/F5/Rank.lean` | `finrank_units`, `finrank_units_one`, `finrank_units_one_univ` (Mathlib): the dimensions of the spans of the vectors that occur in `L^c` |
| `scripts/f5/` | `build.sh` (the build), `gen_data.py` (writes `Data.lean`), `gen_table.py` (the literals `table`, `openTable` from a build log), `percell_ref.py` (per-cell output of the census program), `crosscheck.py` (the comparisons) |
| `logs/f5/` | `build.log` (clean build), `crosscheck.log`, `lean_percell.txt`, `ref_percell_out.txt`, `ref_census_out.txt`, this report |

The code imports the reader of `n6.json` of the family F1 (`L6F1.parseFile`, accepted only if `L6F1.renderFile`
writes the file back identically), `L6F1.kind`, `L6F1.circled`, and for `F5_cc` the list of Chang and Chen and the
orbits of F1 (`L6F1.parseCC`, `L6F1.orbitList`).

## The reading of Corollary 5.8 (`L6F5/Clique.lean`)

Every condition is read off the diagram of the class and the stored argmin sets of the cell, literally as stated, for
each of the 35 sets `K` of three or four bodies (`choose 3`, `choose 4` of `0, …, 5`; no maximality):

1. `kindOK d K`: all pairs of `K` have kind `zw` (a `zw`-clique); or all have kind `z` and no body of `K` is
   `z`-circled; or all have kind `w` and no body is `w`-circled.
2. `internalIn x c K` for `c = z` and `c = w`: for each `t ∈ K`, every `t' ∈ K \ t` has `["cross", t, t']` in the
   argmin set of the `c`-equation of `t` (stored as `[c, "S", [t]]`).
3. `generators x c K`: `e_t` (coordinates in the order of `K`) for each `t ∈ K` whose `c`-equation has a label
   `["cross", t, X]` with `X ∉ K`, and `𝟙` if some `t ∈ K` has `["pos", t]` in the argmin set of its `c`-equation;
   `dimL x c K = rank |K| (generators x c K)`, the rank over `ℚ` by fraction-free Gaussian elimination;
   `dimsOK`: `dz ≤ 2 ∧ dw ≤ 2 ∧ dz + dw ≤ 3` for three bodies, `dz ≤ 1 ∧ dw ≤ 1` for four.

`cliqueOK d x K` is the conjunction; a cell has a clique iff some `K` satisfies it. `rank_unit_vectors` (kernel
`decide`) shows that `rank` returns `|F| + [𝟙]`, or `k` when `𝟙` and all `e_t` are present, for every set `F` of unit
vectors of `ℚ^3`, `ℚ^4` with and without `𝟙`, i.e. on every input that occurs, and `L6Sound/F5/Rank.lean` proves in
Mathlib that these are the dimensions of the spans.

A line is accepted only if it begins with `{"ztree": `, its value after `"argmin": ` is written back byte for byte by
`render` and is followed by `, "x": `, and `readCell` finds each of the 14 base identities exactly once (labels
`["pos", t]`, `["cross", t, X]` in the body equations, `["E"]`, `["delta", k, l]`, `["zw", k, l]` in `U`, `I`).
Otherwise `census` returns `none` and the theorems fail. All 91,273 lines are accepted.

## Theorems (`L6Check/F5/`)

| theorem | statement (in words) |
|---|---|
| `census_table` | `census n6 files = some table` (`native_decide`): for each of the 191 classes, `⟨cells, clique, three, four, forced⟩` |
| **`F5_main`** | **Prop. 5.9**: the census has 191 entries; total cells 91,273; with a clique 86,938; without 4,335; the classes all of whose (≥ 1) cells have a clique are exactly 3, 4, 40, 42, 44, 47, 53, 55, 84, 128, 129, 148, 149, 150, 167, 169, 170, 183 (18); class 3 has 44,247 cells, all with a clique; class 128 has 32,864, all with a clique |
| `F5_three_four` | 86,842 cells have a clique of three bodies, 96 a clique of four bodies, and in every class `clique = three + four` (no cell has both); 69 classes have cells |
| `F5_forced` | in every class, `forced = cells`: in each stored cell, the argmin set of each equation of a body with a stroke or a circle in its colour is exactly the position (if circled) and the terms of its strokes |
| `open_status`, **`F5_open`** | of the 43 cells of `open43.tsv`, the 11 cells of class 124 (diagram 64; cells 0, 16, 17, 30, 46, 83, 105, 109, 110, 111, 121) have a clique, each of four bodies (none of three), and the other 32 (classes 31, 132, 133, 127, 147, 143) have none |
| **`F5_singular`** | the cells 8722, 13414, 17222, 24695, 31349, 41091, 41143, 41569 of class 3 and 218 of class 14 have a clique (of three bodies); the cell 122 of class 30 has none (the ten cells of Section 9) |
| `F5_cc` | the diagrams 7, 11, 14, 16, 64, 66, 88, 89, 93, 94, 98 of Chang and Chen lie in the orbits of the classes 3, 128, 14, 30, 124, 143, 127, 31, 132, 147, 133, and the diagram of each line of `open43.tsv` in the orbit of its class |
| `rank_unit_vectors` | see above (kernel `decide`, no native code) |
| `cells_sha256` | for each `N < 191`, `SHA256SUMS` records `sha256Hex cN` for `cN.jsonl` |
| `sums_lines`, `files_length` | `SHA256SUMS` has 191 lines; 191 embedded files |
| `sums_sha256`, `open43_sha256`, `n6_sha256` | digests `deb001fe…b895`, `bd7a5a9a…a60f`, `0f2ae5d0…2ff4` (the last is the published one of `n6.json`) |
| `finrank_units`, `finrank_units_one`, `finrank_units_one_univ` | (Mathlib) `dim span{e_t : t ∈ F} = |F|`; with `𝟙` added, `|F| + 1` if `F ≠ univ`, `k` if `F = univ` |

## Counts and log lines (`logs/f5/build.log`)

* Census table, one line `class cells clique three four forced` per class: lines 243–433 (class 3: line 246, `3 44247
  44247 44247 0 44247`; class 128: line 371, `128 32864 32864 32864 0 32864`; class 124: line 367, `124 143 95 0 95
  143`; class 84: line 327, `84 1 1 0 1 1`); totals line 434: `total 91273 86938 86842 96 91273`.
* The cells with a clique of four bodies: the 95 cells of class 124 (diagram 64) and the one cell of class 84; no
  other class has one (`four` column).
* Open cells: lines 436–478; Singular-only cells: lines 4911–4920.
* Cells without a clique (`none c k`, 4,335 lines) and with a four-body clique (`four c k`, 96 lines): from line 479
  on; extracted into `lean_percell.txt`.
* Axioms: lines 200–241. Every `native_decide` theorem depends on `propext`, `Quot.sound`, its own
  `…._native.native_decide.ax_1_1` and, except `sums_sha256`, `open43_sha256`, `n6_sha256`, on `Classical.choice`;
  the theorems derived from them (`F5_main`, …) on the same; `rank_unit_vectors` and the Mathlib lemmas on `propext`,
  `Classical.choice`, `Quot.sound` only; `files_length` on none.

## Cross-check with the census program (`logs/f5/crosscheck.log`)

* The program of the paper (`tools/clique_census.py`, with `cliques.py`, `zwexcess.py`, `cell_killers.py` of the
  conceptual note, read-only copies; the modules `numpy` and `highspy`, imported but not used by these functions,
  replaced by empty modules) was run on the embedded cell files: its output (`ref_census_out.txt`) is identical, byte
  for byte, to the published `audit/clique_census.txt` (86,938; 18 classes; the open and Singular-only cells).
* Per cell: `scripts/f5/percell_ref.py` evaluates the program's own expressions (`k`, `three`) for every cell
  (`ref_percell_out.txt`). The cells without a clique (4,335) and the cells with a clique but none of three bodies (96)
  are, in order, exactly the Lean lists (`lean_percell.txt`).
* Per class: the Lean numbers of cells and of cells with a clique equal those of the conceptual note's own run for all
  191 classes.

**No discrepancy.** The two readings differ in form, not in result. The program reads the `zw`-cliques and, for a
`z`- or `w`-clique, the colour of its strokes off the diagram (forcing = strokes leaving `K`, `𝟙` = some body circled),
reads only the other colour off the argmin sets, and considers only maximal cliques (`cliques.info`). Lean reads every
condition off the argmin sets and considers all sets of three or four bodies. They agree because

* `F5_forced`: in all 91,273 stored cells, the argmin set of every equation with a stroke or a circle is the forced
  set, so for the colour of the strokes the argmin sets say exactly what the diagram says (and condition 2 holds
  automatically in that colour);
* a set of three or four bodies inside a larger clique of the same kind never qualifies: each of its bodies has a
  stroke of that colour to a body outside it, so `dim L^c = |K|`, which is 3 > 2 or 4 > 1;
* by (E3) a triangle of edges has one kind, so a clique is never of mixed kind.

The per-cell identity above is the actual evidence; these remarks explain it.

## Timings (`logs/f5/build.log`; 384 vCPUs, nice 10, clean `.lake/build`, Mathlib from the cache)

| step | wall |
|---|---|
| `L6F5` (with the F1 modules it imports) and `L6Common.SHA256` | 4.3 s |
| `L6Sound.F5.Rank` | 1.8 s |
| `L6Check.F5.Data` (138 MB embedded, 3.3 s), `Sha` (2.8 s), `Census` (4.3 s) | 8.3 s |
| `L6Check.F5.Axioms`, `L6Check.F5.Print` | 6.6 s |

`native_decide` evaluations: `census_table` 2.39 s (all 91,273 cells), `cells_sha256` 2.64 s (SHA-256 of 138 MB),
`F5_singular` 0.73 s, `F5_cc` 0.29 s, `open_status` below the profiler threshold. The kernel checks of `open_status`,
`F5_singular`, `F5_cc` take 2.9 s, 3.0 s, 3.7 s ("type checking" in the profiler).

## Notes for the integration

* The roots `L6Check.lean` and `L6Sound.lean` were not edited; the F5 entry points are `L6Check.F5.Axioms` (imports
  `L6Check.F5.Census`, `L6Check.F5.Sha`, `L6Sound.F5.Rank`) and `L6Check.F5.Print`.
* Building `L6Check.F5.Sha` builds the library `L6Common` (Lake builds `L6Common:shared` for an imported precompiled
  module), so it depends on the current state of `L6Common/LP.lean`.
