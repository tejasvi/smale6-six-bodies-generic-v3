# Lean 4 checks of the computations of Sections 3–5 (version 1)

This package checks in Lean 4 every computation that the proofs of Sections 3–5 of the paper *Smale's sixth problem
for six bodies in the plane: finiteness of central configurations for generic masses* rely on, and the clique census
of Section 9 (Proposition 9.19). The computations are evaluated by `native_decide` (compiled code); everything that a
computation's result means is proved in Lean without `sorry`. The mathematical framework of Sections 2–5 (places at
infinity, exponents, trees, cells, initial forms, Lemmas 5.1 and 5.2) is stated in the paper and is **not** formalized
in this version (this package alone; the framework is formalized in `../full`, which proves Theorem 1.1 from these checks); the statements below say which of its definitions each Lean function implements.

Toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib `c55e6e7` (`lake-manifest.json`). Data: the engine's outputs of the
run pinned in the paper (tag `generic-v1`), embedded byte for byte with `include_str` and identified by SHA-256
computed in Lean.

Paper numbers in this file are those of the current version of the paper: Table 2 lists the computations of
Sections 3–5, Section 9 gives the hand explanations of the cells and Table 5 its computations, and §10.1 (in
Section 10, Verification) summarizes the checks of this package. The Lean sources, scripts and logs were written
against an earlier version and use some of its numbers: Proposition 5.9 there is Proposition 9.19, Corollary 5.8 is
Corollary 9.18, "Section 9" (the verification section) is Section 10, and "§5.1" is the list of identities at the
start of Section 5. The other numbers they use (Lemmas 2.11, 4.2, 4.3, 4.6, 5.1, 5.2, Definitions 4.1, 4.4,
Propositions 3.1, 4.5, 5.3) are unchanged.

## How to run

```
lake exe cache get          # Mathlib
bash scripts/build_all.sh   # = unpack the certificates, generate their modules, lake build L6Sound L6Check
```

On a machine with 384 cores the full build from a fresh copy took 30 min 59 s wall clock, 24,032 s user and 458 s
system time, largest resident set of one process 7.2 GB, 11,763 build jobs, exit 0 (`logs/final/final_build.log`, last
lines). The modules `L6Check/F34/All.lean`, `AllCerts.lean` and `CertsOK/` were added after that run and built on top
of it (`logs/final/final_build_incremental.log`: `lake build L6Check L6Sound`, 11,888 jobs, exit 0; axioms of the
printed theorems in `logs/final/axioms_summary_incremental.txt`), and so were, later still, the modules of the
specification search (`L6F2S`, `L6Sound/F2S`, `L6Check/F2S`; see Proposition 4.5, completeness, below). The last
build, of `L6Sound` and `L6Check` with all modules, is `logs/final/final_build_f2s.log` (12,580 jobs, completed
successfully; axioms of the printed theorems in `logs/final/axioms_summary_f2s.txt`). The families separately:
F1 41 s, F2 30 min (6.2 CPU-hours), F3/F4 48 s (9 CPU-minutes), the certificates 78 s (850 CPU-seconds), F5 21 s, the
check modules of the specification search 10 min 37 s. Every `native_decide` theorem is evaluated when its module is
built, and the axioms of all main theorems are printed into the build log by `L6Check.Main` and the modules
`L6Check.<family>.Axioms`.

The computational libraries (`L6Common`, `L6F1`, `L6F2`, `L6F34`, `L6F5`, `L6Poly`) import no Mathlib and are compiled
to native shared libraries (`precompileModules`); measured: a list-heavy check takes 0.18 s precompiled against 6.44 s
in the interpreter. Proofs are in `L6Sound` (Mathlib), the evaluated theorems in `L6Check`.

## Axioms

In this Lean version `native_decide` adds, for each theorem `T` that uses it, one auxiliary axiom
`T._native.native_decide.ax_1_1 : decide P = true`, where `P` is the statement (the form that `Lean.ofReduceBool`
takes here). Every theorem below depends only on `propext`, `Classical.choice`, `Quot.sound` and such auxiliary
axioms of the `native_decide` theorems it uses; the soundness lemmas in `L6Sound` use no `native_decide` and depend
only on the three standard axioms. No `sorryAx`, no other axiom. `scripts/axioms_summary.py` reads every
`#print axioms` output of a build log: `logs/final/axioms_summary.txt` covers the 2,120 theorems printed by the clean
full build, `logs/final/axioms_summary_incremental.txt` the 2,128 printed by the build that added the modules of
`F34_all_meaning`, and `logs/final/axioms_summary_f2s.txt` the 2,143 printed by the last build, which includes the
specification search. In all three, no theorem has another axiom, and `sorryAx` occurs nowhere in the logs.
Per-family axiom logs: `logs/f1/axioms.log`, `logs/f2/axioms.log`, `logs/f34/axioms.log`, `logs/f5/build.log` lines
200–241, `logs/f2s/axioms_summary.txt`.

The top theorems (from `logs/final/axioms_summary_f2s.txt`; the auxiliary axioms are those of the
`native_decide` theorems each one uses: for example `f2_all` uses the 426 chunk and tiling checks of F2,
`F34_all_meaning` the 123 chunk checks and the 1,928 certificate checks, `f2s_cells_sound` the 659 checks of the
specification search and the check of its insertion orders):

| theorem | standard axioms | auxiliary `native_decide` axioms |
|---|---|---|
| `L6F1.F1_main` | Classical.choice, Quot.sound, propext | 1 |
| `L6F1.F1_one_representative` | Classical.choice, Quot.sound, propext | 1 |
| `L6F1.F1_reps_distinct_orbits` | Classical.choice, Quot.sound, propext | 1 |
| `L6F1.F1_canonKey_invariant` | Classical.choice, Quot.sound, propext | 1 |
| `L6F1.F1_n5` | Classical.choice, Quot.sound, propext | 1 |
| `L6F1.F1_n4` | Classical.choice, Quot.sound, propext | 1 |
| `L6F1.F1_chang_chen` | Classical.choice, Quot.sound, propext | 2 |
| `L6F1.n6json_sha256` | Quot.sound, propext | 1 |
| `L6.Farkas.check_sound` | Classical.choice, Quot.sound, propext | 0 |
| `L6.Farkas.check_sound_strict` | Classical.choice, Quot.sound, propext | 0 |
| `L6.Farkas.check_sound_strict_all` | Classical.choice, Quot.sound, propext | 0 |
| `L6.F2.Checks.f2_all` | Classical.choice, Quot.sound, propext | 426 |
| `L6.F2.Checks.f2_totals` | none | 1 |
| `L6.F2.Checks.f2_classes_with_cells` | none | 1 |
| `L6.F2.Checks.tree_counts` | Classical.choice, Quot.sound, propext | 1 |
| `L6.F2.decideLP_discard` | Classical.choice, Quot.sound, propext | 0 |
| `L6.F2.discard_no_solution` | Classical.choice, Quot.sound, propext | 0 |
| `L6.F2S.search_complete` | Classical.choice, Quot.sound, propext | 0 |
| `L6.F2S.Checks.f2s_cells_sound` | Classical.choice, Quot.sound, propext | 660 |
| `L6.F34S.Checks.f34s_excluded` | Classical.choice, Quot.sound, propext | 2713 |
| `L6.F34.Checks.F34_all` | Classical.choice, Quot.sound, propext | 123 |
| `L6.F34.Checks.F34_all_totals` | none | 0 |
| `L6.F34.Checks.F34_all_cover` | propext | 0 |
| `L6.F34.Checks.F34_cover` | Classical.choice, Quot.sound, propext | 1 |
| `L6.F34.Checks.F34_all_certs` | Classical.choice, Quot.sound, propext | 1928 |
| `L6.F34.Checks.F34_all_meaning` | Classical.choice, Quot.sound, propext | 2051 |
| `L6.F34.Checks.F34_sha_cells` | Quot.sound, propext | 1 |
| `L6.F34.Checks.F34_sha_n6` | Quot.sound, propext | 1 |
| `L6.F34.single_strict` | Classical.choice, Quot.sound, propext | 0 |
| `L6.F34.constantArgmin_strict` | Classical.choice, Quot.sound, propext | 0 |
| `L6.F34.core_cell_excluded` | Classical.choice, Quot.sound, propext | 0 |
| `L6.F34.chunk_meaning` | Classical.choice, Quot.sound, propext | 0 |
| `L6.Poly.checkCert_sound` | Classical.choice, Quot.sound, propext | 0 |
| `L6.Poly.checkParsed_vanish` | Classical.choice, Quot.sound, propext | 0 |
| `L6.Poly.checkParsed_nonzero` | Classical.choice, Quot.sound, propext | 0 |
| `L6.Poly.Checks.cert_1459bbf4f7537687` | Classical.choice, Quot.sound, propext | 1 |
| `L6F5.F5_main` | Classical.choice, Quot.sound, propext | 1 |
| `L6F5.census_table` | Classical.choice, Quot.sound, propext | 1 |
| `L6F5.F5_three_four` | Classical.choice, Quot.sound, propext | 1 |
| `L6F5.F5_forced` | Classical.choice, Quot.sound, propext | 1 |
| `L6F5.F5_open` | Classical.choice, Quot.sound, propext | 1 |
| `L6F5.F5_singular` | Classical.choice, Quot.sound, propext | 1 |
| `L6F5.F5_cc` | Classical.choice, Quot.sound, propext | 1 |
| `L6F5.rank_unit_vectors` | Classical.choice, Quot.sound, propext | 0 |
| `L6F5.cells_sha256` | Classical.choice, Quot.sound, propext | 1 |

Each auxiliary axiom states that one specific Boolean computation returns `true`, namely `decide P = true` for the
statement `P` of its theorem, and is accepted because the compiled code evaluated it so; it is the trust placed in
`native_decide` (the Lean compiler and runtime), and nothing else is assumed.

## The claims, by paper label

### Proposition 3.1 (`prop:enum`) and the checks after it — family F1

| | |
|---|---|
| Lean theorem | `L6F1.F1_main` (`L6Check/F1/Main.lean`); `L6F1.F1_one_representative`, `F1_reps_distinct_orbits`, `F1_canonKey_invariant`, `F1_n5`, `F1_n4`, `F1_chang_chen`, `n6json_sha256` |
| checks | `#{d : okRules 6 d} = 82,712`; `#{e < 4^15 : (E2), (E3), (E6)} = 932,677`; these diagrams are the disjoint union of the orbits under the 720 relabellings and the colour exchange of the 191 representatives of the embedded `n6.json`, with the stored orbit sizes; each representative has the least key of its orbit (the class order of `n6.json`); n = 5: 1376 diagrams, 24 classes (`n5.json`); n = 4: 41, 5 (`n4.json`); SHA-256 of `n6.json`, `n5.json` = the published values; Chang–Chen's 117 diagrams satisfy the rules and lie in 117 distinct classes |
| proved | `mem_search`: the search lists every labelled diagram satisfying `okRules` (no tables; the pruning checks are instances of the rules); `canonKey_actP`: the key is constant on orbits; `mem_component_iff` |
| assumes | that `okRules` (`L6F1/Rules.lean`, written from Lemma 2.11 with explicit quantifiers, (E3) and (E6) on kinds) is the "combinatorial part" of the rules |
| time | `native_decide` 25.4 s (n = 6); clean build of all F1 targets 41 s |
| log | `logs/f1/F1_REPORT.md`; counts in `logs/f1/build.log` lines 179–190, 198–223 |
| not checked | the "Rule T" count (8 of the 74 extra classes violate only the triangle rule): it needs Chang–Chen's further rules |

### Lemma 4.6 (`lem:farkas`)

| | |
|---|---|
| Lean theorem | `L6.Farkas.check_sound`, `L6.Farkas.check_sound_strict`, `check_sound_strict_all` (`L6Sound/Common/Farkas.lean`) |
| statement | if `Farkas.check n rows cert = true` (`L6Common/Rows.lean`: integer multipliers with the sign conditions, `Σ y a = 0`, `β + g⁻ ≤ 0`, `g + g⁻ > 0 ∨ β + g⁻ < 0`, used rows monotone in `s`), then over any ordered field no heights and `s > 0` satisfy the rows of the certificate; and no heights satisfy their strict forms (`c = 0`: `lo ≤ a·h ≤ hi`; `c < 0`: `lo < a·h`; `c > 0`: `a·h < hi`) |
| axioms | `propext`, `Classical.choice`, `Quot.sound` |

### Proposition 4.5 (`prop:cells`), its proof, and the Proposition 4.5 row of Table 2 — family F2

| | |
|---|---|
| Lean theorems | `L6.F2.Checks.f2_all` (`L6Check/F2/All.lean`), `L6.F2.Checks.f2_totals`, `L6.F2.Checks.f2_classes_with_cells`, `L6.F2.Checks.tree_counts`, `L6.F2.Checks.sha_c<k>`; proved: `L6.F2.decideLP_discard`; composed: `L6.F2.discard_no_solution` (`L6Sound/Composed.lean`) |
| checks | for each of the 191 classes, a replica of the engine's certified search (`treplay.enumerate_cells`, `--mode le --base --split 3 --nparts 384`: trees with the engine's insertion orders and node numbers, `base_lp`, the relaxation of `ℓ(x) ≤ 0`, the base identities, the argmin branching) run on its 384 parts writes exactly the stored cells of `data/cells/c<k>.jsonl` (trees and argmin sets; the stored floating-point fields are ignored), in the engine's order; every linear program is decided by a floating-point simplex in Lean that only proposes; a program is discarded only with a certificate that `Farkas.check` accepts, and no prune lacked one; every listed cell has an exact rational point (heights, `s > 0`, all rows, `ℓ(x) ≤ 0`), so it is nonempty and nonpositive; the numbers of linear programs and prunes equal the engine's, part by part; totals 91,273 cells in 69 classes, 133,538,490 programs, 76,087,734 prunes; without pruning the insertions give 55,720 trees (39,208 with seven leaves, 16,512 with a body on the leaf of O) |
| proved | `decideLP_discard`: the search discards a program only if `Farkas.check` accepted its certificate; with Lemma 4.6, `discard_no_solution`: every discarded program has no solution of its strict form |
| assumes | the framework of the proof of Prop. 4.5: the rows are the conditions of Lemma 4.3 and Definition 4.4, the relaxation of `ℓ(x) ≤ 0` for the pairs not yet placed is valid, the four combinatorial cuts are justified, and the restriction of two trees to the points inserted so far is a node of the search. These steps are now proved in Lean for the specification search (next section); what remains assumed is that `Cond` states Lemma 4.3(a)–(c) for a singular place, which the paper proves and the formal proof in `../full` proves for germs (`cond_of_germ`, `Compose/CC6Compose/CellsConv.lean`) |
| time | 29 min 42 s wall, 22,370 s CPU; longest module class 3 part 358 (9,934,314 programs) 1,769 s; 0.16–0.18 ms per program |
| log | `logs/f2/F2_REPORT.md`; per class `logs/f2/build_final_axioms.log` lines 17–207 (`per_class.tsv`), totals lines 5–12, 69 classes line 13, trees line 14 |
| not checked | the engine's split of its certificates into dual solutions, dual rays and exact simplex, and the slacks of Table 2 (properties of the Python run) |

### Proposition 4.5, completeness — the specification search

| | |
|---|---|
| Lean theorems | `L6.F2S.search_complete` (`L6Sound/F2S/Complete.lean`), `L6.F2S.Checks.f2s_cells_sound` (`L6Check/F2S/All.lean`), with the pieces `options_complete`, `levelFacts` (trees: `Tree.lean`, `TreeAux1–3.lean`), `partialRows_strict`, `idents_eval`, `forced_facts` (rows: `RowsSem.lean`, `RowsAux*.lean`), `argminRec_complete`, `branchRec_complete` (`Argmin.lean`), `keepLP_sound`, `treeLevel_complete`, `cellsBelow_complete`, `cells_sound` (`Complete.lean`, `CompleteAux.lean`, `StoredSem.lean`) |
| statement | `f2s_cells_sound`: for every class `k < 191` and every pair of complete trees with heights `Xz`, `Xw` satisfying `Cond (diagOf k) Xz Xw` (heights increasing strictly from the root to the leaves; the conditions of Lemma 4.3(a)–(c) for the representative: root heights `≥ −2`, (O1), (O2) with its strokes, its circles, the root rule, each base identity's least exponent attained twice; and `ℓ(x) = Σ x_kl ≤ 0`), some stored line of `data/cells/c<k>.jsonl` has the key `(Xz.T.key, Xw.T.key, argminString …)`: the same two trees (as sets of nodes, each node the set of points below it, with the body on the leaf of `O`) and the same argmin sets. This is the statement "every nonpositive cell of a representative is in the list" of Proposition 4.5, proved in Lean (not only computed) |
| how | `L6F2S` is a specification of the search written as total functions (trees as families of point sets). `search_complete` proves that it lists every such pair, using only that a discarded linear program has no solution of its strict form (`KeepSound`, which holds for `keepLP` by Lemma 4.6); the native_decide checks `f2s_c<k>`, `f2s_c<k>_m<j>` (659 modules, `L6Check/F2S/`) check that every cell it lists is a stored cell, and `f2s_order` that each insertion order lists the six bodies. The fast replica `L6F2` (partial functions, by construction not provable) remains the check of the counters |
| axioms | `search_complete` and all pieces: `propext`, `Classical.choice`, `Quot.sound`; `f2s_cells_sound`: these and the 660 auxiliary axioms of the checks it uses (`logs/f2s/axioms_summary.txt`) |
| time | 10 min 37 s wall, 29,576 s CPU on 384 cores for the check modules (`logs/f2s/f2s_build.log`, `lake build L6Check.F2S.Index`); the specification search reproduces the stored lists exactly (pilot: classes 63, 0, 29, both inclusions) |
| assumes | `Cond` states Lemma 4.3(a)–(c) for a singular place, which the paper proves and the formal proof in `../full` proves for germs (`cond_of_germ`, `Compose/CC6Compose/CellsConv.lean`). Its last condition, `ℓ(x) ≤ 0`, is the nonpositivity in the statement of Proposition 4.5, not an assumption |

### Proposition 4.5, completeness, for evaluation in the kernel — the search with lists of rows

| | |
|---|---|
| Lean theorems | `L6.F2S.searchL_complete`, `cellL_stored`, `searchL_split`, `argminString_eq_renderIdx` (`L6Sound/F2S/SearchL.lean`), on the functions of `L6F2S/SearchL.lean` |
| statement | `searchL_complete`: for a decision `keep` on linear programs given as lists of rows that discards a program only if it has no solution of its strict form (`KeepSoundL keep`), an insertion order `ord` with `ord.Perm (List.range 6)`, and every pair of complete trees with heights satisfying `Cond D Xz Xw`, some cell of `searchL keep D ord` has the key `(Xz.T.key, Xw.T.key, argminIdx D Xz Xw)`. `argminIdx` lists, for the identities whose argmin set the diagram forces and then for the other base identities, the code of the identity (its position in `idents`) and the positions of its terms of least exponent; `argminString D Xz Xw` is its rendering with the names and labels of the base identities (`argminString_eq_renderIdx`). `cellL_stored`: if every cell of `searchL keep D ord` has its key in a list `ks`, so does the key of every pair satisfying `Cond D` |
| why | the same search as `L6F2S.Search`, written so that it reduces in the kernel: rows as lists, the argmin sets structured instead of rendered as strings, and the insertion order as a parameter (the loop of `orderBodies` does not reduce in the kernel). The definitions and theorems of the specification search used by version 1 and by the full formalization are unchanged |
| how | the tree level and the argmin recursion are the functions of `L6F2S.Search` read through `Array.toList` (`treeLevel_eq_L`, `argminRecL_eq`), so their completeness is that of `search_complete`; the cells below a complete pair follow the proof of `cellsBelow_complete` with structured entries (`cellsBelowL_complete`) |
| axioms | `propext`, `Classical.choice`, `Quot.sound` (`logs/f2s/axioms_searchL.txt`); the build with these modules: `logs/final/final_build_upd.log` (12,725 jobs, completed successfully, 2,165 theorems with only the allowed axioms, `logs/final/axioms_summary_upd.txt`) |
| assumes | as `f2s_cells_sound`: `Cond` states Lemma 4.3(a)–(c) for a singular place |

### Proposition 4.5, completeness, with the rows of each cell — the search `searchN`

| | |
|---|---|
| Lean theorems | `L6.F2S.searchN_complete`, `searchN_split` (`L6Sound/F2S/SearchN.lean`), on the functions of `L6F2S/SearchN.lean` |
| statement | `searchN_complete`: for `keep` with `KeepSoundL keep`, an insertion order `ord` with `ord.Perm (List.range 6)`, and every pair of complete trees with heights satisfying `Cond D Xz Xw`, some cell `c` of `searchN keep D ord` has the key `(Xz.T.key, Xw.T.key, argminIdx D Xz Xw)`, trees equivalent to `Xz.T`, `Xw.T` with distinct nodes, and rows that all hold strictly at the heights read off the complete trees (`heightVec Xz Xw c.pair`) |
| why | for a decision on linear programs that reads the rows newest first, and for checking the claim of a cell on its rows: in the argmin recursion the state is the whole list of rows of the cell, newest first, and `keep` is applied to it; the cells carry their rows |
| how | the argmin recursion is that of `L6F2S.Search` read through `Array.toList` and reversed (`argminRecN_eq`), so its completeness is that of `argminRec_complete`; the tree level is `treeLevelL`; the cells below a pair follow `cellsBelowL_complete` |
| axioms | `propext`, `Classical.choice`, `Quot.sound` (`logs/f2s/axioms_summary_n.txt`; build `logs/f2s/final_build_n.log`, 12,735 jobs, completed successfully) |

### Proposition 5.3 at every pair satisfying `Cond` — F3, F4 on the cells of the specification search

| | |
|---|---|
| Lean theorems | `L6.F34S.Checks.f34s_excluded` (`L6Check/F34S/All.lean`), from the 123 chunk theorems `L6.F34S.Checks.F34S_c<class>_k<k>` (`L6Check/F34S/C<class>K<k>.lean`), `F34S_class_c<class>`, `class_meaning`, `lines_ok`, `open_ok`, the certificate theorems and `f2s_cells_sound`; proved: `chunkS_meaning`, `claimHolds_meaning`, `link_meaning`, `single_meaning`, `constant_meaning` (`L6Sound/F34S/Meaning.lean`), `itemPoly_spec`, `distPoly_spec` (`PolySem.lean`), `termForm_spec` (`Forms.lean`), `cellsBelowR_complete` (`BelowR.lean`), `itemVal_congr` (`Congr.lean`) |
| statement | `f34s_excluded`: for every class `k < 191` and every pair of complete trees with heights `Xz`, `Xw` satisfying `Cond (diagOf k) Xz Xw`, either `k` is one of the seven classes of the 43 open cells (`openClasses`: 31, 124, 127, 132, 133, 143, 147, the diagrams 89, 64, 88, 93, 98, 66, 94), or `ClaimMeaning Xz Xw` holds. `ClaimMeaning` is one of two things. **Single term**: a valid identity of `L6F34S/Ids.lean` has a term whose exponent is finite and strictly smaller than that of every other term (`IsArgminX … [i]`, the hypothesis of Lemma 5.1). **Core**: a certificate with `CertMeaning` (fixing no mass, or a mass `F < 6`), each of whose generators, at the point `phiOf` of the variables of its link, equals `1` or `2` times the value of an item that holds at `(Xz, Xw)`. An item is either twice the initial form `Σ_{i∈S} c_i lc(g_i)` of a valid identity whose argmin set at `(Xz, Xw)` is `S` (times the engine's factor `m_k` for the equation of body `k`), or a row `P_kl² lc(z_kl) lc(w_kl) − 1`. This holds for all node coordinates, `P_kl`, `E` and masses (with `m_F = 1`) in every commutative ring, with the values `itemVal` computed on the trees `Xz.T`, `Xw.T` themselves (they depend only on the nodes as a set, `itemVal_congr`). The point `phiOf` takes a node coordinate of the certificate as the difference of the coordinates of its child and of its base child, so any base convention can be used to read it |
| how | each stored line is checked on the cells that the specification search itself lists below its pair of trees (`cellsBelowR`: the cells with their rows), so the rows of the cell hold strictly at the heights of every pair satisfying `Cond` with that key (`cellsBelowR_complete`, the proof of `cellsBelow_complete`). Single terms and argmin sets are certified on those rows by `Farkas.check` (Lemma 4.6). The generators of the certificates are compared with the initial forms written from the trees (`itemPoly`, `distPoly`). `f2s_cells_sound` provides the stored line of every pair |
| identities | `L6F34S/Ids.lean`: the identities as term lists. The families, parameters, order of the terms and coefficients are those of the full formalization, and terms with a vanishing position are kept, with exponent `⊤`. Each term carries the engine's label, by which the stored claims name it |
| axioms | the semantic lemmas: `propext`, `Classical.choice`, `Quot.sound`; `f34s_excluded`: these and 2,713 auxiliary axioms (123 chunk theorems, 1,928 certificate theorems, `lines_ok`, `open_ok`, and the 660 of `f2s_cells_sound`) (`logs/f34s/axioms_summary.txt`) |
| time | `lake build L6Sound L6Check` after the modules of F3/F4 on the specification search were changed, which rebuilt the 123 chunks and the modules above them: 1 min 31 s wall, 2,975 s user time on 384 cores, largest resident set 7.5 GB, longest chunk 70 s; 12,720 jobs, completed successfully (`logs/f34s/final_build_f34s.log`) |
| assumes | `Cond` states Lemma 4.3(a)–(c) for a singular place (as for `f2s_cells_sound`); the identities of `L6F34S/Ids.lean` are those of §2.3 (they mirror the term lists of the full formalization, where they are proved to hold); Lemmas 5.1 and 5.2 themselves |
| from the meaning of the certificates | `L6.F34S.Checks.f34s_excluded_of (hcerts : AllChunkCertsMeaning)` (`L6Check/F34S/AllOf.lean`) states the same with the meaning of the certificates as a hypothesis: every certificate text of every chunk parses to a certificate with `CertMeaning` (`CertLists.lean`; per chunk `chunkS_meaning_of`, `L6Sound/F34S/MeaningOf.lean`). Its axioms are the standard three and 785 auxiliary axioms (123 chunk theorems, `lines_ok`, `open_ok`, and the 660 of `f2s_cells_sound`), none for the certificates. With `allChunkCertsMeaning_native` (the native certificate checks, 1,928 auxiliary axioms) it gives back `f34s_excluded`; the hypothesis can also be given by checks of the certificates in the kernel (`logs/f34s/axioms_summary_of.txt`, `logs/f34s/final_build_of.log`) |
| with the certificates of the class | `L6.F34S.Checks.f34s_excluded_in (hcerts : AllChunkCertsMeaning) : ∀ k < 191, ∀ Xz Xw, Cond (diagOf k) Xz Xw → k ∈ openClasses ∨ ClaimMeaningIn (certsOfClass k) Xz Xw` (`L6Check/F34S/AllIn.lean`, `L6Sound/F34S/MeaningIn.lean`): in `ClaimMeaningIn`, the certificate of a core is parsed from a text of the list of the class (`certsOfClass k`, the lists of its chunks), so the polynomials `h` of a class form a finite family fixed before the pair, and the argmin sets of the initial forms have no repetition. Axioms: the standard three and 785 auxiliary axioms (as `f34s_excluded_of`); `f34s_excluded_in_native`, from the native certificate checks: 2,713 (`logs/f34s/axioms_summary_in.txt`, `logs/f34s/final_build_in.log`) |

### Proposition 5.3 (`prop:exclusion`), Lemmas 5.1 and 5.2 — families F3, F4

| | |
|---|---|
| Lean theorems | the 123 chunk theorems `L6.F34.Checks.F34_c<class>_k<k>` (`L6Check/F34/C<class>K<k>.lean`) and, over the list `chunkArgs` of their arguments, `L6.F34.Checks.F34_all` (every chunk passes), `F34_all_totals` (52,432 / 37,808 / 990 / 43, summed over the checked chunks), `F34_all_cover` (with `F34_cover`: the chunks of each class are all its cells, in order), `F34_all_certs` (every certificate named in a chunk passes), **`F34_all_meaning`** (`L6Check/F34/All.lean`, `AllCerts.lean`); `F34_sha_cells`, `F34_sha_n6`; the 1,928 certificate theorems `L6.Poly.Checks.cert_<certid>` (`L6Check/Poly/B<k>.lean`); composed: `L6.F34.single_strict`, `L6.F34.constantArgmin_strict`, `L6.F34.core_cell_excluded`, `L6.F34.chunk_meaning` (`L6Sound/Composed.lean`) |
| checks | every one of the 91,273 stored cells is in exactly one of three lists: **single term** (52,432 cells): for the identity named for the cell (one of those listed at the start of Section 5) and every other term `k`, the system `Π + {e_k − e_i ≤ 0}` has a certificate accepted by `Farkas.check`, where `Π` is the cell polyhedron rebuilt in Lean from the stored cell (independently of F2's code) and the exponent forms are those of the secondary identities; **core** (38,798 cells: 37,808 of the first pass, 990 of the second pass): the generators of the named certificate equal the initial forms of the named identities computed in Lean from the cell's trees (rows `D_kl² z_kl w_kl − 1`; base identities on the cell's argmin sets; secondary identities on an argmin set certified constant on `Π` by accepted certificates), multiplied by 2 when they have a coefficient ½, with `m_F = 1` when a mass is fixed; **open** (43 cells): listed in `data/cells/open43.tsv` (diagrams 64: 11, 66: 11, 88: 9, 89: 1, 93: 1, 94: 9, 98: 1); per-class counts equal `per_class.tsv` in all 191 classes. Each certificate: `Σ cofᵢ·genᵢ = h` in `ℤ[m, x]` after normalization, `h` involves only masses, `h(3,5,7,11,13,17) ≠ 0` (with `m_F = 1`) |
| proved | `checkCert_sound` (`L6Sound/Poly/Sound.lean`): a passing certificate text gives `h`, nonzero at that point, that vanishes in every commutative ring wherever all generators vanish; `chunk_meaning`, and for all chunks at once `F34_all_meaning`: for a passing chunk whose certificates pass, every cell is open, or single-term (`e_i < e_k` for all `k ≠ i` at every point of the strict form of `Π`, the hypothesis of Lemma 5.1), or a core cell (an `h ≠ 0` vanishing wherever the Lean initial forms vanish, the hypothesis of Lemma 5.2 without saturation) |
| interface | `L6.Poly.CertMeaning c` (the meaning of a certificate), `checkParsed_meaning`, `checkCert_meaning`, and `L6.F34.core_cell_excluded_of_meaning`, the form shared with the planned kernel-only and fully formalized versions (standard axioms only) |
| axioms | `F34_all_meaning`: the three standard axioms and the 2,051 auxiliary axioms of the 123 chunk theorems and the 1,928 certificate theorems |
| assumes | that the rows of `Π` and the exponent forms are those of §§4–5 (framework), that `genFor` computes the initial system defined in Section 5 (before Lemma 5.2), and Lemmas 5.1 and 5.2 themselves (for 974 cells with a fixed mass, Lemma 5.2(b)) |
| time | chunks: 48 s wall, 9 min 12 s CPU, longest chunk 40 s; certificates: 78 s wall, 850 s CPU, the largest (263 MB and 342 MB of text) about 60 s and 4.5 GB each |
| log | `logs/f34/F34_REPORT.md`, `logs/f34/counts.log`, `per_class_compare.log`, negative controls `negctl.log`; `logs/poly/build_certs_box.log` (134 modules, 1,928 theorems) |
| cores | the engine's run stored 1,935 distinct cores (over all classes; a core is identified by its generators, with the variables renamed in order of appearance, `scripts/f4/collect.py`); 1,900 of them have a certificate and 35 do not. The 35 cells whose stored core has none (class 29 cell 601 of the first pass and 34 second-pass cells) are certified with another subset of the same cell's initial system, because their stored cores were not lifted to a certificate within the limits tried (7,200 s for six of them, at most 1,800 s per method for the others; see the table below). These 35 replacement cores are distinct: 7 are stored cores of other cells, already among the 1,900, and 28 are new subsets, so the certificates are for 1,928 = 1,900 + 28 distinct cores, as in Table 2 and §10.1 of the paper. The six cells with attempts of 7,200 s are exactly those of the 35 that are among the ten cells whose cores rest on Singular alone (class 3 cells 8722, 13414, 17222, 41091, 41143; class 14 cell 218); 17 of the replacement cores keep all six masses as parameters (`logs/f4/replaced.jsonl`, `logs/f4/SUMMARY.md`). The other four Singular-only cores (class 3 cells 24695, 31349, 41569; class 30 cell 122) have certificates of their own. |
| replaces | Table 2's Singular standard bases and the Macaulay2 confirmations (2,403 of 2,413): every core cell now has an explicit cofactor identity checked in Lean, for its stored core or, in the 35 cells, for the replacement core; and Table 2's 184,997,938 argmin decisions, of which the checks re-certify exactly those the exclusions use |

### The certificate set and the 35 replacement cores

**Which certificates the theorems check.** The theorems check the 1,928 certificates of `data/f4/certs/`, one for each
distinct certified core: 1,900 of the 1,935 distinct cores stored by the engine's run and the 28 new replacement cores
below. `scripts/f4/` computed them with Singular, without saturation and without an extra variable, with the mass `F`
set to 1 where the core fixes one: 1,458 by `lift` of `1` in the ideal of the core over ℚ(masses), 379 by `liftstd`
over ℚ(masses) with the algorithm `slimgb` (the standard basis is then a nonzero constant), and 91 by an elimination
(the masses as ring variables in a block order, `liftstd`, and `h` the element of the standard basis in the masses
alone with fewest terms). Denominators are cleared, and each certificate was verified by python-flint before it was
written (`logs/f4/SUMMARY.md`, with the method of every kept certificate). `L6.Poly.Checks.cert_<certid>` checks the
file `data/f4/certs/<certid>.txt[.gz]`, embedded as `L6.Certs.C<certid>`; the links of the cells to the certificates
are `data/f4/links/c<class>.txt`. The independent set of the engine's own lift pipeline (`lift_v1`: 2,058
certificates, 420 cells through smaller cores of their own systems, checked there by exact python-flint expansion) is
**not** checked in Lean in version 1.

**The 35 cells whose certified core is not the stored one.** For 35 cells (one of the first pass, 34 of the second) no
certificate was obtained for the core that the engine's run stored, within the limits tried (7,200 s for six of them,
at most 1,800 s per method for the others; see the table); the Lean check uses another core of the same cell. The 35
stored cores are distinct and belong to no other cell, so 1,900 of the 1,935 distinct stored cores are certified. The
35 replacement cores are distinct as well: 7 of them are stored cores of other cells, with certificates among the
1,900, and 28 are new, which gives the 1,928 certified cores. The replacement cores were found by the same procedure
as the stored ones (QuickXplain modulo 32003 at random masses over the cell's full initial system, equation orders
biased towards equations with few variables; `scripts/f4/altcore.py`) and then lifted. Each is a subset of the same
cell's initial system: in the Lean check every generator is recomputed as the initial form of its named identity on
the cell, with the argmin set of a secondary identity certified constant on the cell (and `scripts/f4/check.py` found
every (name, polynomial) pair in the engine's stored initial system of the cell). So the exclusion of the cell by
Lemma 5.2 is unchanged; only the polynomial `h(m)` differs. 17 of the replacement cores keep all six masses as
parameters (F = −1), so 16 second-pass cells are certified by Lemma 5.2(a). Among the 35 are six of the ten cells
whose cores rest on Singular alone in the paper (class 3 cells 8722, 13414, 17222, 41091, 41143; class 14 cell 218);
the other four of the ten (class 3 cells 24695, 31349, 41569; class 30 cell 122) are checked through certificates of
their stored cores. The engine's own lift pipeline (`lift_v1`) also replaced the stored core of every one of the 35
cells. Table: `logs/f4/replaced_table.md` (`scripts/f4/replaced_table.py`, from `logs/f4/replaced.jsonl` and
`logs/f4/lift.jsonl`). Pass: the pass of the engine's run that certified the cell; F: the mass set to 1 (−1: none).

| class | cell | pass | stored core: certid, F, generators | certified core: certid, F, generators | attempts on the stored core | lift_v1 |
|---|---|---|---|---|---|---|
| 3 | 8722 | second | `554cf28bbe3c176c`, 2, 10 | `18a6212a7127e854`, -1, 6 | elim: memory limit (10 GB); lift: timeout 7,200 s, memory limit (10 GB); liftstd: timeout 3,600 s; liftstd_slimgb: memory limit (15 GB) | also replaced |
| 3 | 13414 | second | `3fb29ae96b879aab`, 0, 8 | `f14ef6ce4398650f`, -1, 6 | elim: timeout 1,800 s; lift: timeout 7,200 s, memory limit (9 GB); liftstd: memory limit (12 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 3 | 17222 | second | `0c669317b45c3f18`, 1, 10 | `63440898f2dbec78`, 3, 6 | elim: memory limit (10 GB); lift: timeout 7,200 s; liftstd: timeout 3,600 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 3 | 24725 | second | `304bfbe73dccade5`, 3, 7 | `40e932c9efbff8ca`, 0, 7 | elim: timeout 1,800 s; liftstd_slimgb: memory limit (10 GB) | also replaced |
| 3 | 31232 | second | `12c2ebdf7446ded3`, 3, 7 | `a152f608aaf33d4a`, -1, 4 | elim: timeout 1,800 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 3 | 31274 | second | `5021f4b8aa02c581`, 3, 7 | `1ae7a9e75141fac8`, 3, 6 | elim: timeout 1,800 s; liftstd_slimgb: memory limit (11 GB) | also replaced |
| 3 | 31294 | second | `a96600ac093191b7`, 3, 7 | `a1d7c492700e0acb`, 0, 4 | elim: memory limit (16 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 3 | 32603 | second | `5b64d70cf7765943`, 3, 7 | `5380c10c49621d0a`, 0, 7 | elim: timeout 1,800 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 3 | 33516 | second | `b7af1da5c9e8d214`, 3, 6 | `c4e4752dac82d237`, 3, 6 | elim: timeout 1,800 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 3 | 40246 | second | `27f49c33642245f5`, 3, 7 | `45b7edf950821bea`, -1, 4 | elim: memory limit (10 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 3 | 41091 | second | `311de1ceb9499b5e`, 0, 8 | `ecbfe587eaa77e7f`, -1, 6 | elim: timeout 1,800 s; lift: timeout 7,200 s; liftstd: timeout 3,600 s; liftstd_slimgb: memory limit (9 GB) | also replaced |
| 3 | 41143 | second | `0b6e5f6afe4cc9bb`, 3, 7 | `840c82e8ce38adf2`, -1, 4 | elim: timeout 1,800 s; lift: timeout 7,200 s; liftstd: timeout 3,600 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 3 | 42702 | second | `6f90dce812c6e87c`, 3, 7 | `6c61163370247b04`, -1, 6 | elim: timeout 1,800 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 14 | 218 | second | `919069b72a23260d`, 0, 10 | `b76600618d698a5e`, -1, 4 | elim: memory limit (9 GB); elim_slimgb: memory limit (10 GB); lift: timeout 7,200 s; liftstd: timeout 3,600 s; liftstd_slimgb: timeout 3,600 s | also replaced |
| 14 | 235 | second | `1c7fd2dff66942f8`, 0, 9 | `f0a1d909bb386f2d`, 1, 4 | elim: memory limit (10 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 14 | 246 | second | `76b37bbf10824e2d`, 0, 9 | `3f99b20d30c3b6e7`, -1, 4 | elim: memory limit (10 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 14 | 258 | second | `f319bd17c47cb72d`, 0, 9 | `e95a3e69b6637b6a`, 1, 4 | elim: memory limit (10 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 14 | 260 | second | `8b120e49ff1a484f`, 0, 9 | `f7aff496e481acdf`, 1, 4 | elim: memory limit (10 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 14 | 377 | second | `4a818de2c5ea4f29`, 2, 7 | `29f9e03ae6c6af77`, 1, 4 | elim: timeout 1,800 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 29 | 601 | first | `e1dcf7d3509e5f00`, -1, 10 | `9918437f7b3a297d`, -1, 6 | elim: memory limit (11 GB); lift: memory limit (9 GB); liftstd_slimgb: memory limit (9 GB) | also replaced |
| 29 | 831 | second | `f5a95ac7805ac251`, 1, 12 | `e83ac031d183144d`, 1, 7 | elim: timeout 1,800 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 29 | 1444 | second | `7a1020554264b34a`, 0, 10 | `fbe4a25afe0be9a8`, -1, 6 | elim: memory limit (10 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 29 | 1476 | second | `e0e6f901b35ebcb2`, 1, 7 | `e07ae38753a76d9e`, 2, 6 | elim: memory limit (9 GB); liftstd_slimgb: memory limit (16 GB) | also replaced |
| 29 | 1484 | second | `13aaedb3d5763636`, 0, 9 | `587c52351a8ffff2`, 2, 6 | elim: memory limit (10 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 29 | 1508 | second | `e5235da7d0793e20`, 0, 9 | `a5ce291fd63b43b1`, -1, 6 | elim: memory limit (11 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 29 | 1518 | second | `cf8ae9951ff9f143`, 0, 10 | `b328af070b6cb40b`, 2, 6 | elim: timeout 1,800 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 29 | 1542 | second | `86c713a305d6aa4d`, 0, 10 | `972e9014b176196b`, -1, 6 | elim: timeout 1,800 s; liftstd_slimgb: memory limit (13 GB) | also replaced |
| 29 | 1670 | second | `5b002379685d4787`, 0, 10 | `6dd7c8e608b7373e`, 2, 6 | elim: timeout 1,800 s; lift: memory limit (10 GB); liftstd_slimgb: memory limit (11 GB) | also replaced |
| 40 | 211 | second | `6076fa31bd11b1df`, 1, 7 | `c11c7d57d8674628`, 0, 4 | elim: timeout 1,800 s; liftstd_slimgb: memory limit (10 GB) | also replaced |
| 40 | 321 | second | `7d73c225527a05c5`, 1, 7 | `e22c0d46e77e8aed`, -1, 7 | elim: memory limit (16 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 149 | 115 | second | `78cd8b78de08cf7d`, 0, 10 | `68c1a1002cc774a2`, -1, 7 | elim: timeout 1,800 s; liftstd_slimgb: memory limit (17 GB) | also replaced |
| 149 | 478 | second | `e425e26ac373ea0b`, 0, 9 | `22a4a3c90f34e0db`, 0, 7 | elim: timeout 1,800 s; liftstd_slimgb: memory limit (12 GB) | also replaced |
| 149 | 487 | second | `b2d7aa02be49da10`, 0, 13 | `75d8263ef29760f8`, 0, 13 | elim: timeout 1,800 s; lift: memory limit (25 GB); liftstd_slimgb: memory limit (16 GB) | also replaced |
| 149 | 613 | second | `b075a2e324a12cc1`, 0, 8 | `dd9300dbab7e39e2`, -1, 6 | elim: memory limit (10 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 149 | 682 | second | `e8b905ff357bcdad`, 0, 14 | `de13238c8be61fb2`, -1, 7 | elim: timeout 1,800 s; liftstd_slimgb: timeout 1,800 s | also replaced |

The names of the generators of both cores, for each cell: `logs/f4/replaced_table.md`, last section.

### Proposition 9.19 (`prop:cliquecount`), the facts after it and its row of Table 5 — family F5

| | |
|---|---|
| Lean theorems | `L6F5.F5_main`, `census_table`, `F5_three_four`, `F5_forced`, `F5_open`, `F5_singular`, `F5_cc`, `rank_unit_vectors`, `cells_sha256` (`L6Check/F5/`); `L6Sound/F5/Rank.lean` |
| checks | 86,938 of the 91,273 cells have a clique as in Cor. 9.18 (86,842 of three bodies, 96 of four, none both), 4,335 do not; exactly the 18 classes 3, 4, 40, 42, 44, 47, 53, 55, 84, 128, 129, 148, 149, 150, 167, 169, 170, 183 have all their cells with a clique, among them all 44,247 cells of class 3 (diagram 7) and all 32,864 of class 128 (diagram 11); of the 43 open cells the 11 of diagram 64 have a four-body clique and the other 32 none; the nine Singular-only cells of classes 3 and 14 have a clique, class 30 cell 122 none |
| assumes | that `cliqueOK` (`L6F5/Clique.lean`) is the condition of Cor. 9.18 read off the diagram and the argmin sets (literal transcription; the ranks are proved to be the dimensions) |
| time | 21 s clean build; `census_table` 2.4 s |
| log | `logs/f5/F5_REPORT.md`; table `logs/f5/build.log` lines 243–433, totals line 434; cross-check with the paper's census program cell by cell `logs/f5/crosscheck.log` |

## Kernel-only checks

These checks prove the computational claims of Sections 3–5 without `native_decide`: every computation is reduced by
the Lean kernel (`decide +kernel`), so the theorems below depend only on `propext`, `Classical.choice` and
`Quot.sound`. They are laid out as follows: `L6K/`
(computational code over `Nat` and `List`, no Mathlib, and the generators of the data), `L6SoundK/` (soundness
lemmas), `L6CheckK/` (check modules: F1 and the version-1 links committed, F4 generated) and `L6CheckF/` (the fused
F2–F4 run, generated). They use lean6's libraries unchanged (`L6F1`, `L6Poly`, `L6Common`, `L6F2S`, `L6F34S`,
`L6Sound`). Every check module is compiled by `lean` directly, one process per module, by the memory-budget
schedulers of `scripts/kern/` (driver `scripts/kern/build.sh`); generated modules and data are compared with
committed SHA-256 lists before they are compiled.

### Proposition 3.1 by the kernel — F1

| | |
|---|---|
| Lean theorem | `L6CheckK.F1.F1_main_k` (`L6CheckK/F1/Main.lean`) |
| statement | the combinatorial content of `L6F1.F1_main` (the counts 82,712 and 932,677, the classes as the disjoint union of orbits with their sizes, least keys and increasing keys) for the 191 classes given as the literal list `classes6L`. Reading `n6.json` into `classes6L` is the version-1 check (`classes6 = classes6L`), which needs strings |
| how | lean6's search (`edgesUpTo`, `extendAt`, `searchFrom`) unchanged, split into 18,918 shards by the prefixes of `edgesUpTo 6 10` (266 shard modules), 24 class modules, 32 modules comparing the codes of the 82,712 labelled diagrams with the orbit codes of the classes interval by interval, and `Global`; soundness from `L6Sound.F1` and `L6SoundK.F1` |
| modules | committed; written by `scripts/kern/kf1_modules.py` from `data/f1k` (the output of the generators `f1shardgen`, `f1repgen`), which reproduces the 326 generated modules byte for byte (`Main.lean` is written by hand) |
| axioms | `propext`, `Classical.choice`, `Quot.sound` (`logs/kern/f1_axioms.txt`) |
| time | 327 modules, 26.3 CPU-hours, 22 min 20 s wall clock on 384 cores, largest process 13.8 GB (`Global`) (`logs/kern/f1_build.log`) |

### Lemma 5.2: the 1,928 cofactor certificates by the kernel — F4

| | |
|---|---|
| Lean theorems | `L6CheckK.F4.C<H>.cert : CertMeaning certH` for each certificate `H` of lean6's set (`L6CheckK/F4/M<n>.lean`) |
| statement | `certH : L6.Poly.Cert` holds the generators and `h` of certificate `H` as source literals; `CertMeaning` is the conclusion of lean6's `checkCert_sound`: in every commutative ring, `h` vanishes wherever the generators vanish, and `h ≠ 0` at `hPoint` |
| how | the cofactors, stored in data files (`data/f4k/<H>.bin`, `.idx`) and loaded when the modules are elaborated (`load_f4_cert`, which checks the sizes stated in the source; a relative path is looked up from the directory of the module upwards, then in the working directory, so the modules build from any working directory), are split into pieces; the identity is checked bucket by bucket (sums of term products after merging), with checks that every product occurs exactly once and that the parts make up `h`; soundness `L6SoundK.F4.cert_sound` (the cofactors are the sums of their pieces) |
| modules | generated, not committed: `scripts/kern/kf4_gen.py` writes the 830 modules (11 MB) and the data (1.5 GB) from lean6's certificate texts; `data/f4k/SHA256SUMS` lists all 4,687 files. Two generations with different hash seeds and output directories gave identical files |
| axioms | all 1,928 `cert` theorems: `propext`, `Classical.choice`, `Quot.sound` (`logs/kern/f4_axioms.txt`) |
| time | 830 modules, 24.2 CPU-hours, 24 min 51 s wall clock (the four stages of the scheduler), largest process 17.9 GB (a cover module) (`logs/kern/f4_build.log`) |
| links to the texts (version 1) | `L6CheckK.F4Link.meaning_<H> : ∃ c, parseCert L6.Certs.C<H> = some c ∧ CertMeaning c` (`L6CheckK/F4Link/`, committed; `kf4_link_gen.py` reproduces them), from `link_<H>` (`native_decide`: the text parses to the generators, `h`, `nvar` and `fixed` of `certH`) and the kernel theorem `cert`. Each has the three standard axioms and the auxiliary axiom of its own `link_<H>`, for all 1,928 (`logs/kern/f4link_axioms.txt`); 31 modules, 1.0 CPU-hour. Not used by the kernel route |

### Propositions 4.5 and 5.3 at every pair satisfying `Cond`, by the kernel — F2–F4 fused

| | |
|---|---|
| Lean theorem | `L6CheckF.fusedK` (`L6CheckF/Final.lean`, generated by `scripts/kern/kf34k_final.py`) |
| statement | `∀ k < 191, ∀ Xz Xw : ExpTree, Cond (diagOfL k) Xz Xw → k ∈ openClasses ∨ ClaimMeaningFinK csAll Xz Xw`, where `diagOfL k` is the diagram of class `k` in the literal class list of the kernel F1 (`L6CheckK.F1.classes6L`), `csAll` is the list of the 1,928 certificates `certH` of the F4 kernel modules (`L6CheckF/Certs.lean`), and `ClaimMeaningFinK cs` (`L6SoundK/F34K/Fin.lean`) is `L6.F34S.ClaimMeaning` with the certificate of a core taken from `cs` and, for each initial form, an argmin set without repetition |
| how | lean6's specification search (`L6F2S`: `treeLevelL`, `cellsBelowL` and `searchL_complete`, unchanged) with the keep test `keepR` (`L6K/F2S/KeepR.lean`; `keepR_sound : KeepSoundL (keepR T)` for every table `T`, so the keep tables are untrusted hints), run in units of at most 1,000 weighted programs; at every cell the claim is checked with the argmin sets and the certificates of the linear programs given as data (`L6K/F34K/Check.lean`, `claimK_meaning` in `L6SoundK/F34K/Meaning.lean`); `unit_coversF`, `level_covers` (`L6SoundK/F34K/Assembly.lean`) and the class theorems `L6CheckF.C<k>.classOK` |
| modules | generated, not committed: the exporter `f34kexport` writes the units, level nodes, claims and keep tables of the 184 classes without open cells (`data/f34k`, 489,151 files, 6.8 GB, 11 min on 384 cores), and `kf34k_gen.py`, `kf34k_certs.py`, `kf34k_final.py` write the 31,324 modules (726 MB with their dependency lists). `data/f34k/SHA256SUMS` lists every generated file, `data/f34k/EXPORT.sha256` the exporter's output per class |
| reproduced | regenerated from the committed generators and compared with an earlier kernel run (2026-10-17), whose modules were compiled: the exporter's output is identical for all 184 classes (`data/f34k/EXPORT.sha256` is the run's list), and with the run's table directory the generators give all 31,324 modules byte for byte as compiled. In the form committed here, 15,847 modules are those bytes and the other 15,477 (the groups of kernel checks) differ only in the directory of the keep tables they read (`data/f34k/c<k>`, relative to the root, instead of an absolute directory of the run) (`logs/kern/compare.log`) |
| axioms | `propext`, `Classical.choice`, `Quot.sound`, from that kernel run (927 CPU-hours for the 31,154 modules with a time record; largest process 26.7 GB, `L6CheckF.Final`). `scripts/kern/build.sh` (stage `f34k`) compiles these modules |

### Building the kernel checks

```
bash scripts/kern/build.sh libs f1 f4gen f4 f4link f34kexport f34kgen f34k
```

The stages run in this order. `f4gen` and `f34kexport` read lean6's certificate texts (`data/f4/certs_txt/`, unpacked
by `scripts/build_all.sh`), `f4link` needs lean6's `L6Check.Certs` (the native build), and the others need only the
libraries that `libs` builds. The schedulers start modules while the sum of their memory estimates stays within
`BUDGET_GB` (at most `MAXJOBS` processes); the estimate of every module is set in the driver, per family, with the
largest peaks measured. On one machine with 384 cores and 708 GB: F1 22 min (`BUDGET_GB=600 MAXJOBS=150`), F4 25 min
and F4Link 7 min (`BUDGET_GB=650`), the exporter 11 min (`JOBS=300`), the generators 3 min. The fused stage took
about 3 hours on four such machines in the kernel run; `kf34k_split.py` splits a class over machines by export run,
and the stage, run again on one machine after the `.olean` files are gathered, skips the modules already built.

## Claims not checked in Lean (v1), and why the proof does not need them

* **The framework** (Sections 2–4, Lemmas 5.1, 5.2, Cor. 9.18, Theorem 9.9 as mathematics, and the correspondence of
  the Lean functions with the definitions: rows of a cell, exponent forms, initial forms): stated, not formalized,
  except that the steps of the proof of Proposition 4.5 are proved for the specification search, relative to `Cond`.
  The framework is formalized in `../full`, which proves Theorem 1.1 from these checks.
* **Rule T** (8 of the 74 classes outside Chang–Chen's list violate only the triangle rule): not implemented. It is a
  remark about the comparison with Chang–Chen; the proof treats all 191 classes and does not use it.
* **Table 2, Proposition 4.5 row:** the split of the engine's prune certificates into dual solutions, dual rays and
  an exact simplex (26,563,313 / 49,524,037 / 384), and the slacks (0.0055 over kept programs, 0.0345 over listed
  cells, 1.4·10⁻¹⁴ over pruned optima). These describe how the Python run found and checked its certificates and how
  far its floating-point decisions were from the threshold. They are not needed: the Lean search finds and checks its
  own certificate for every prune (and reproduces the engine's prune and program counts), and every listed cell has
  an exact rational point, so no floating-point decision is trusted in either direction. The counts 133,538,490 and
  76,087,734 themselves are re-checked (`f2_totals`).
* **Table 2, Proposition 5.3 row:** the 184,997,938 argmin decisions of the engine's run (it decided every secondary
  identity of every cell); the Singular standard bases over ℚ(m) that certified the cores; the Macaulay2 confirmations
  (2,403 of 2,413) and the ten cores that rested on Singular alone; the lift cofactors of 40 random cores; the
  identity tests at complex solutions; the five-body Roberts control. Not needed: the Lean checks re-certify every
  argmin decision that an exclusion uses (the named single term of each single-term cell, the argmin sets of the
  identities of each core), and replace the Gröbner-basis certification of the cores by explicit integer cofactor
  identities checked by expansion (every core cell, for its stored core or a replacement core, including all ten cells
  of the first remark after the tables in Section 10). The identity tests and the Roberts control are tests of the
  engine's programs, not steps of the proof.
* **Table 5, Proposition 9.19 row:** re-checked (F5), against the stored cells.
* **The 43 open cells:** treated in Sections 6 and 7 at the level of places; outside this package (the companion
  checks of those sections are a separate package).

## Files

`L6Common/` (rows, Lemma 4.6's check, the floating-point proposer, SHA-256), `L6F1/`, `L6F2/`, `L6F34/`, `L6F5/`,
`L6Poly/` (checkers), `L6F2S/` (the specification search of Proposition 4.5), `L6F34S/` (F3, F4 on its cells),
`L6Sound/` (proofs), `L6Check/` (evaluated theorems; `L6Check/Main.lean` is the entry point), `data/` (embedded
inputs: `data/cells/` the stored cell lists with `SHA256SUMS`, `data/f1/` the diagram files, `data/f4/` the cofactor
certificates and the links of the cores to the cells, `data/f34/` the single-term claims and pass tags), `scripts/`
(generators and converters; untrusted, Lean re-checks everything they produce), `logs/`.

Kernel-only checks: `L6K/` (computational code of the kernel checks and the generators of their data),
`L6SoundK/` (their soundness lemmas), `L6CheckK/` (check modules of F1 and the version-1 links; those of F4 are
generated into `L6CheckK/F4/`), `L6CheckF/` (generated: the fused F2–F4 run), `data/f1k/` (the shard and class data of
F1), `data/f4k/SHA256SUMS`, `data/f34k/SHA256SUMS`, `data/f34k/EXPORT.sha256` (the hashes of the generated modules and
data), `scripts/kern/` (generators, schedulers, `build.sh`), `logs/kern/`; the schedulers write the `.olean` files of
the check modules to `out/`.
