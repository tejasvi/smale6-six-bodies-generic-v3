# Supplementary material for "Smale's sixth problem for six bodies in the plane: finiteness of central configurations for generic masses, with a proof formalized in Lean"

Tejasvi Singh Tomar, independent researcher. ORCID 0000-0003-4668-3639.

* Paper: https://doi.org/10.5281/zenodo.23451290
* This supplement: https://doi.org/10.5281/zenodo.23451291
* Repository (programs, Lean projects and small certificates): https://github.com/tejasvi/smale6-six-bodies-generic-v3

This is version 3 of the supplement. In version 3 Lean's kernel checks the formal proof of Theorem 1.1, except two
computations, the dimension bounds of Lemma 6.19(b): the theorem `CC6Compose.V3.main_theorem_v3 :
CC6Full.MainTheorem` (`lean/full/`, checked by `lean/full/check_v3.sh`) depends on `propext`, `Classical.choice`,
`Quot.sound` and the two auxiliary axioms of `native_decide` of the F4 runs behind `count_S12` and `count_KC`. The
certificate projects (`lean/sections3-5/`, `lean/sections6-9/`, at their version-3 commits; `lean/COMMITS`) carry
kernel-only checks of the computations next to the checks of versions 1 and 2; the cofactor certificates of the
kernel checks of `lean/sections6-9/` ship as archive parts. The logs of the developers' release run are in
`logs/release_check_v3/`, and `logs/check_staged_layout_v3.log` is the check of the staged release layout. Version 2 (October 2026; paper https://doi.org/10.5281/zenodo.23440983, supplement
https://doi.org/10.5281/zenodo.23440984, repository https://github.com/tejasvi/smale6-six-bodies-generic-v2 at commit
210ced5d612bacdc17fcab65ae610f0696f5eb23) added the formal proof, whose larger computations ran as compiled code;
version 1 (17 October 2026; paper https://doi.org/10.5281/zenodo.23433407, supplement
https://doi.org/10.5281/zenodo.23433410, repository https://github.com/tejasvi/smale6-six-bodies-generic at commit
f51cba739eb2bb4900b23c52c6c1329f6fece3ff) checked the paper's computations in Lean. The files that version 3 does not
change are those of version 2, byte for byte; `CHANGES.md` says which files changed. The DOIs
https://doi.org/10.5281/zenodo.23433406 (paper) and https://doi.org/10.5281/zenodo.23433409 (supplement) refer to
all versions and resolve to the latest one.

## The files of this deposit

`SHA256SUMS` lists the SHA-256 of every file of the deposit. Unpack everything in one directory; the archives create
`supplement/`:

```
for f in smale6-six-bodies-generic-*.tar.xz; do tar -xJf "$f"; done          # all but lean/ and the certificates
cat smale6-six-bodies-generic-lean.tar.xz.part* | xz -d | tar -x               # lean/
cd supplement/lean/sections3-5 && bash scripts/fetch_data.sh ../../..          # the 1,928 certificates of lean6, checked
cd ../sections6-9 && bash scripts/fetch_kern_certs.sh ../../..                 # the kernel certificates, checked
cd ../../.. && (cd supplement && sha256sum -c --quiet SHA256SUMS)              # every file of supplement/
```

The two scripts check the archive parts against `data/f4/certs_parts.sha256` and `data/kern/kcert_parts.sha256` and
every certificate against the committed lists, then unpack them; given no directory, they download the parts from
this deposit. The certificates are not listed in `supplement/SHA256SUMS`.

## What this is

The programs, certificates and logs of every computation of the paper, together with the independent checks of them.
Section 10 of the paper lists the computations and the checks made of them; the statements marked † in the paper
depend on the files below. Statement numbers in this file follow the paper.

| directory | contents | paper |
|---|---|---|
| `diagrams/` | enumeration of the zw-diagrams (rules E1–E6, C1–C4; code names C1, C2, C4, C5): 41 labelled diagrams in 5 classes for four bodies, 1,376 in 24 for five, 82,712 in 191 for six (`n4.json`, `n5.json`, `n6.json`); the comparison with the 117 diagrams of Chang and Chen (not used in the proof); `separate/`: an enumeration written separately from the statements of the rules, assembling the diagrams from their connected components | Prop. 3.1, Table 2 |
| `engine/` | the programs of Sections 4 and 5: trees, constraints and exact cells (`tengine.py`, `texact.py`, `tsign.py`), the certified enumeration (`treplay.py`), secondary identities and initial systems (`tsec.py`, `tsec_exact.py`, `tinit.py`), cores modulo 32003 and their certification over Q(m) (`tcore.py`, `tcert.py`, `talt.py`), counts (`exact_summary.py`, `uncertified.py`, `tcorehash.py`), the test of the identity terms (`test_identities.py`); `jobs/`: the job scripts | Prop. 4.5, Lemma 4.6, Prop. 5.3 |
| `engine/independent/` | the independent checks of the engine: recertification of the cores in Singular and in Macaulay2 with all six masses as parameters, lift cofactors, tests of the generators and exponents, negative controls, the split into 384 parts, resampled single-term exclusions, the control at Roberts' continuum, the re-run of seven classes; outputs in `out/` | Sec. 10 |
| `results/exact6/c<N>/` | for each class N = 0, …, 190: the cells (`cells.jsonl`; a cell's number is its line, from 0), the 384 parts of the certified enumeration with their certificate counters (`rep/p*.jsonl`, `rep/p*.jsonl.replay.json`), the secondary identities and initial systems with their certificate counters (`sec/p*.sec.jsonl`, `.cert.json`), the cores (`sec/p*.cores.jsonl`) and the certification of the distinct cores over Q(m) (`cert.jsonl`); `*.done` mark completed steps, `sec/p*.timeout` the 32 core searches that were stopped | Props. 4.5, 5.3 |
| `results/` | `uncertified.json`, `UNCERTIFIED.txt`: the 1,033 cells left by the first pass; `unc_alt.json`, `unc_c3.json`: the inputs of the two runs of `talt.py`; `alt_out.jsonl`, `alt3_out.jsonl`: the 990 cells certified by alternative cores (390 + 600); `GENERIC_OPEN.txt`: the 43 remaining cells and where the paper excludes them | Sec. 5, Sec. 10 |
| `audit/` | per-class counts, certificate counters, the least slack, the causes of the 1,033, the Rule T counts, the summary of the independent checks of the engine, the test of `sat`, the Macaulay2 checks without saturation; and the checks of Sections 6 and 7 listed under those sections below | Sec. 10 |
| `cliques/` | the census of Corollary 9.18 over the stored cells (86,938 of 91,273), and the status of the 43 open cells and of the ten cells certified by Singular alone | Prop. 9.19 |
| `d98/` | diagrams 89, 90, 98 and 93: the eliminations of Lemma 6.9, the check of Lemma 6.13 at (1,2,7) by two programs, the factorization of Theorem 6.15 and P93(1,2,7) ≠ 0, numerical zeros of P93 (labelled numerical in the paper); `independent/`: independent checks; and in `audit/` the bounds of Lemma 6.13 at (1,2,40), the square-free parts of Lemma 6.9 and the correspondence of the factors of S_μ with the shapes S1–S8 of Albouy and Kaloshin | Sec. 6 |
| `d88/` | diagrams 88 and 94: the systems S12, S11, KC12 and the counts of Lemma 6.19(b) at p = 65521 and 2^31 − 1, the prevarieties and cone tests of Lemma 6.19(a), the positive controls at (1,1,2,2) and (1,1,1,5), the Krawczyk certificates of Lemma 6.19(c), (d) with two checkers each; `independent/`: an independent prevariety with exact certificates, msolve cone tests, Macaulay2 counts, a third Krawczyk check | Lemma 6.19, Thm. 6.20 |
| `d64/` | diagrams 64 and 66: the check after Proposition 7.8 at (3,5,7,11) by two programs, Lemma 7.9 by two checkers with the comparison of the builders, numerical sanity checks (not used in the proof); `independent/`: a Macaulay2 implementation, checks without the reductions, the equal-mass runs and the runs of Remark 7.14 | Sec. 7 |
| `hand_explanations/` | the explanation of every one of the 91,273 cells by hand mechanisms: the notes `MECHANISMS.md` and `RESIDUAL.md` (corrected; the versions that the referee report reviewed are in `refereed/`); `mechanisms/` and `residual/` with the programs (`scripts/`), the Singular and SymPy checks of their lemmas (`checks/`) and the outputs (`data/`); `independent/`: an independent re-implementation and classification of all cells (`final_classification.jsonl`), with its report, programs and outputs; `inputs/`: the label files of the engine that the programs read; `audit/`: the coverage of the cells by the lemmas of Section 9 from both classifications compared cell by cell (Proposition 9.23), the polynomials of Lemmas 9.13 and 9.14 in the 74 cells where they are needed, the classes with an isolated zw-triangle, and the rerun of the independent checkers | Sec. 9 |
| `lean/` | the Lean 4 proof of Theorem 1.1 (`full/`: the framework `CC6Full` and the package `Compose` with the bridges, `CC6Compose.V3.main_theorem_v3` checked by the kernel except the two bounds of Lemma 6.19(b), and version 2's `CC6Compose.main_theorem`; `full/README.md`, `full/check_v3.sh`, `full/check.sh`) and the checks of the computations on which the proof rests, with their kernel-only versions: `sections3-5/` (Sections 3–5, with the completeness of the list of cells) and `sections6-9/` (the computations of Sections 6 and 7, Lemma 6.19 included, and those inside the hand proofs of Sections 2–9), each with `LEAN_CHECKS.md`; `lean/README.md` says how to build them. The cofactor certificates are in this deposit as archive parts: the 1,928 of `sections3-5/` (`smale6-six-bodies-generic-lean-certs.tar.xz.part000`–`part021`, `sections3-5/data/f4/certs_parts.sha256`) and the 16 of the kernel checks of `sections6-9/` (`smale6-six-bodies-generic-lean-kernel-certs.tar.part*`, `sections6-9/data/kern/kcert_parts.sha256`); `lean/` itself is in `smale6-six-bodies-generic-lean.tar.xz.part*` | Sec. 10.1 |
| `tools/ms_lint.py` | the strict syntax check of msolve inputs (see "Input hygiene") | |

`CHANGES.md` lists every file whose bytes differ from the file of the original computation, and the files written
for this supplement. `SHA256SUMS` lists every file with its SHA-256.

## Versions of the programs

The programs of Sections 3–5 (`diagrams/` from the engine, `engine/`) are those of tag `generic-v1` of the author's
engine repository, commit `d257663d3d06efe7ab23d8428914169880f5063a`, apart from the changes listed in `CHANGES.md`
(paths relative to this supplement, a docstring, and in `engine/jobs/exact_job.sh` the defaults `P=64`, `NP=384` and
`LC_ALL=C`, which fixes the order of the parts as in the stored runs). The stored runs were made before that tag. The files changed between the runs and
the tag are these (among them the engine referee's fixes 1-3: the prune rule of `treplay.py`, and the hash and the
`__main__` guard of `tcert.py`), and none of the changes affects a stored result:

* `texact.py`: the cells of a tree pair are streamed; the output is the same, byte for byte.
* `tsec_exact.py`: reads only the lines of its part.
* `tsec.py`: an optional time limit for Singular.
* `tcore.py`: an optional pre-check (off unless `TCORE_PRECHECK` is set).
* `tcert.py`: the hash of a core includes its saturation set (`tcorehash.py` gives both hashes; `exact_summary.py`
  and `uncertified.py` accept either), a `__main__` guard (Python 3.14 starts workers with forkserver), explicit
  worker arguments.
* `treplay.py`: a prune whose certificate fails is not used as a prune; the stored runs have no such case (0
  failures in all 73,344 counter files).
* `exact_summary.py` reads the counters of the replay under the key `cert` and prints them (`replay_lp`,
  `replay_pruned`, `sec_pruned`); `audit/exact_summary.out` was written by the earlier version, and
  `audit/exact_summary_generic-v1.out` is the output of the version here (the six common values are equal).

The cores of `tinit.py`, `tcore.py`, `tcert.py` and `talt.py` were computed and certified without saturation: these
programs request saturations, but do not load the Singular library `elim.lib` that defines `sat`, so Singular reports
"`sat` undefined", leaves the ideal unchanged and continues (`audit/sat_test/`). The certified statement is that the
cores generate the unit ideal, as the paper states (Section 10). A later tag of the engine, `generic-v2`, loads
`elim.lib` before `sat`; it was not used for any stored result and is not included here.

`n6.json`, on which all class numbers and file names depend, is the output of `count6.py` followed by `canon6.py`
(sha256 `0f2ae5d0e1e8619eeb680c12b04fb168faaa856e43d61b16074df50a874e2ff4`, also in `diagrams/SHA256SUMS`).
`zwenum.py --out` writes the same 191 classes in another order and with other representatives, so it must not be used
to regenerate `n6.json`.

## Software

The stored runs used Python 3.13 (engine runs) and 3.14, with numpy, scipy, sympy 1.14, mpmath 1.3, highspy (HiGHS
1.15.1) and python-flint 0.9.0; Singular 4.4.1; msolve 0.9.4; gfan 0.7; Macaulay2 1.25.11 (independent checks only).
The re-checks of 2026-10-17 used Python 3.13.5, numpy 2.5.3, scipy 1.18.1, sympy 1.14.0, mpmath 1.3.0, highspy 1.15.1,
python-flint 0.9.0, Singular 4.4.1, gfan, msolve 0.9.4 and Macaulay2 1.24.11. The msolve outputs were made with msolve
0.9.4; use that version (some Linux distributions ship msolve 0.7.x).

## Input hygiene

* The inputs to msolve are fully expanded integer polynomials, without parentheses, `**`, products of equal variables or
  rational numbers, and pass `tools/ms_lint.py`: msolve 0.9.4 misreads some of these forms without warning. All 4,607
  msolve inputs of `d88/` and `d64/` pass it.
* The variables given to gfan have single-letter names (gfan reads a name such as `X23` as `X2*3`).
* Where Singular's `sat` is used, `LIB "elim.lib";` is loaded and the result is used as `ideal S = sat(I, f)` (the
  cone tests of `d88/tropcheck.py` do this). The core programs of the engine do not load it (see above).
* The square-root enclosure in `d88/kc_check_iv.py` uses a safety factor rather than outward rounding; the Arb checker
  `d88/kc_krawczyk.py` and the third implementation `d88/independent/my_krawczyk.py` are rigorous throughout.

## Re-running the checks

Run every command from the root of this supplement, with outputs in a directory `$OUT` outside it, at low priority,
with single-threaded BLAS:

```
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 RAYON_NUM_THREADS=1 LC_ALL=C
export PATH=/path/to/msolve-0.9.4/bin:$PATH      # msolve -h must print version 0.9.4
PY="python3 -I -B"; OUT=/path/to/empty/directory; SUP=$PWD     # SUP: the root of this supplement
```

`-B` keeps Python from writing `__pycache__` into the supplement. Some programs write next to their inputs or into the
working directory; the commands below say where. A copy of the engine programs with `n6.json` and `fig11.json` serves as
`$CODE` for the independent checks: `mkdir -p $CODE && cp engine/*.py diagrams/n6.json engine/independent/fig11.json engine/independent/find_cell.py $CODE/`.
Runtimes are those of the re-checks on one 384-core machine.

### Diagrams (`diagrams/`)

```
$PY diagrams/zwenum.py 4 --out $OUT/n4.json                  # = diagrams/n4.json
$PY diagrams/zwenum.py 5 --out $OUT/n5.json                  # = diagrams/n5.json
$PY diagrams/zwenum.py 6 --out $OUT/zwenum_n6.json           # = engine/independent/out/zwenum_n6_rerun.json (3 min)
mkdir $OUT/w && cp diagrams/zwenum.py diagrams/count6.py diagrams/canon6.py diagrams/labelled_io.py $OUT/w/
(cd $OUT/w && $PY count6.py > count6.log && $PY canon6.py)   # n6_labelled.txt, n6.json = diagrams/ (40 s)
(cd diagrams && sha256sum -c SHA256SUMS)
python3 -c "import json; json.dump(json.load(open('diagrams/chang_chen_diagrams.json'))['diagrams'], open('$OUT/cc_list.json', 'w'))"
(cd diagrams && $PY compare_cc.py $OUT/cc_list.json n6.json $OUT/cc_compare.json)    # = cc_compare.json
for n in 4 5 6; do (cd diagrams && $PY ccrules.py $n n$n.json $OUT/ccrules_n$n.json); done
(cd diagrams && $PY tri1.py 6 n6.json)     # prints the list of classes passed below
(cd diagrams && $PY extra_account.py n6.json ccrules_n6.json "[26, 36, 38, 50, 59, 61, 72, 80, 82, 96, 106, 107, 125, 138, 139, 144, 145, 155, 160, 162, 166, 168]" cc_compare.json $OUT/extra74.json)
(mkdir -p $OUT/s/data && cd $OUT/s && S=$SUP/diagrams/separate && \
  for k in 2 3 4 5; do $PY $S/pieces_enum.py $k data/pieces_k$k.json; done && $PY $S/pieces_enum6.py data/connected_n6.json && \
  for n in 4 5; do $PY $S/connected_from_pieces.py $n data/connected_n$n.json; done && \
  for n in 4 5 6; do $PY $S/assemble.py $n data/connected_n$n.json $SUP/diagrams/n$n.json; done)   # = separate/assemble.txt
```

`n6_labelled.txt` lists the 82,712 labelled diagrams that `count6.py` writes and `canon6.py` reads, in a text form
(`labelled_io.py`; the original tree stored them as a Python pickle).

### Cells and their generic exclusion (`engine/`, `results/`)

The pipeline runs per class: `treplay.py` in 384 parts, `tsec_exact.py` and `tcore.py` per part of the cells, and
`tcert.py` on the distinct cores. The results go to `engine/runs/exact6/c<N>/`, to be compared with
`results/exact6/c<N>/`:

```
CLASSES="0 1 2" P=64 NP=384 PY=python3 bash engine/jobs/exact_job.sh
```

Class 3 takes about 2.2 hours on 376 processes (its longest enumeration part takes 86 minutes); the whole pipeline
took about 2.2 hours on six machines. In the stored runs `engine/jobs/kill_stragglers.sh` stopped 32 core searches
that had run for more than 30 minutes (classes 31, 124, 127, 133, 143 and 147; `sec/p*.timeout`), and the
certification of classes 30 and 149 never finished (no `cert.jsonl.done`; 49 and 42 cells not attempted). The
alternative cores:

```
PY=python3 bash engine/jobs/alt_job.sh     # the 433 cells of results/unc_alt.json -> engine/runs/alt_out.jsonl
PY=python3 bash engine/jobs/alt3_job.sh    # the 600 cells of class 3 (results/unc_c3.json) -> engine/runs/alt3_out.jsonl
```

`talt.py` writes its records in completion order, so a re-run agrees with the stored file up to the order of lines.
`alt_out.jsonl` holds the 390 certified cells of the first run; it has no records for the 43 open cells, which had
not finished their eight tries.

Counts and lists over the stored results (`uncertified.py` writes `engine/runs/` next to itself, so run it from a copy):

```
$PY engine/exact_summary.py results                                   # = audit/exact_summary_generic-v1.out
cp -r engine diagrams $OUT/ && $PY $OUT/engine/uncertified.py results  # = results/UNCERTIFIED.txt, uncertified.json
(cd engine && $PY test_identities.py)                                 # = audit/test_identities.log
$PY audit/per_class.py . diagrams/n6.json diagrams/cc_compare.json   # = audit/per_class.tsv
$PY audit/minslack.py .                                               # = audit/minslack.txt
$PY audit/uncert_causes.py .                                          # = audit/uncert_causes.txt
$PY audit/extra74_counts.py diagrams/extra74.json                     # = audit/extra74_counts.txt
$PY audit/eref_summary.py engine/independent                          # = audit/eref_summary.txt
$PY audit/alt_check.py results/alt_out.jsonl results/alt3_out.jsonl results/uncertified.json results/GENERIC_OPEN.txt
bash audit/sat_test/run.sh                                            # = audit/sat_test/sat_test.out
$PY cliques/clique_census.py cliques . results/GENERIC_OPEN.txt 3:8722,3:13414,3:17222,3:24695,3:31349,3:41091,3:41143,3:41569,14:218,30:122
```

The lists `UNCERTIFIED.txt`, `uncertified.json`, `engine/independent/out/bk.json` and line 2 of
`audit/exact_summary.out` follow the order of the directories of the original runs (one per machine); regenerated
here they hold the same lines in the order of `results/exact6/`.

The independent checks (`engine/independent/`, outputs in `out/`):

```
$PY engine/independent/test_terms.py $CODE                 # = out/test_terms.txt
$PY engine/independent/test_enum.py $CODE                  # = out/test_enum.txt (12 min)
$PY engine/independent/test_negctl.py $CODE 63             # out/negctl_c63.txt, see below
$PY engine/independent/split_check.py $CODE                # = out/split_check.txt
$PY engine/independent/single_check.py $CODE . 1500 1      # = out/single_check.txt
(cd $CODE && $PY find_cell.py 5 fig11.json 4 $SUP/engine/independent/cells5_c4.jsonl $SUP/engine/independent/roberts_a0.json)   # cell 884
$PY engine/independent/roberts.py $CODE engine/independent/cells5_c4.jsonl 884    # = out/roberts.txt
$PY engine/independent/certtotals.py .                     # = out/certtotals.txt
$PY engine/independent/bk.py . $OUT/bk.json                # = out/bk.json up to order
$PY engine/independent/recert.py . $OUT/recert.jsonl --only-certified --jobs 56 --timeout 900    # 1,423 cores
$PY engine/independent/recert_alt.py . $OUT/recert_alt.jsonl results/alt_out.jsonl results/alt3_out.jsonl --jobs 56 --timeout 900
$PY engine/independent/lift_sample.py engine/independent/out/recert.jsonl $OUT/lift_sample.jsonl --n 40 --seed 7 --timeout 600
$PY engine/independent/m2_fix1.py engine/independent/out/recert_alt.jsonl $OUT/m2_fix1.jsonl results/alt_out.jsonl results/alt3_out.jsonl --timeout 3600 --jobs 19
$PY engine/independent/lift_alt.py engine/independent/out/m2_fix1.jsonl,engine/independent/out/m2_fix1_last.jsonl $OUT/lift_alt.jsonl results/alt_out.jsonl results/alt3_out.jsonl --timeout 2400 --jobs 14
mkdir -p $OUT/spec_tmp && $PY engine/independent/m2_spec.py engine/independent/out/lift_alt.jsonl $OUT/m2_spec.jsonl results/alt_out.jsonl results/alt3_out.jsonl
CODE=$CODE STORE=$SUP P=64 bash engine/independent/rerun_job.sh   # with CLASSES; then cmp.py CLASS ... (RERUN_EXACT6)
```

`cells5_c4.jsonl` is the output of `cd $CODE && $PY texact.py 5 fig11.json 4 cells5_c4.jsonl` (39 minutes).
`recert.jsonl` also holds 44 records of uncertified cores from an earlier run without `--only-certified`. The seed 7
of `lift_sample.py` is the one of the stored sample; with the default seed 1 two of the 40 Macaulay2 verifications
take longer than 600 s. `test_negctl.py` gives the stored `negctl_c63.txt` with the `treplay.py` of the stored runs;
with the `treplay.py` of `generic-v1`, which keeps a branch whose prune is not certified, test (b) reports 68 kept
branches and test (d) 17 injected faults with 17 failures (stored: 0, and 15 with 15); both end with `RESULT PASS`.
`m2_unsat.py` (Macaulay2 without saturation on the 14 hardest alternative cores) gave one unit ideal and 13 timeouts
at 7,200 s.

### Diagrams 89, 90, 98 and 93 (`d98/`)

```
cp -r d98 $OUT/ && (cd $OUT/d98 && for m in "1 2 7" "1 2 8" "2 3 11"; do $PY lemB_check.py $m certificates/lemB; done)  # = certificates/lemB/*
$PY d98/d98_certify_arb.py 1 2 7 1 2 7 $OUT/d98_cert_127_127.json > $OUT/d98_cert_127_127.log     # and 1 2 7 1 2 8
for B in "1 2 7" "1 2 8"; do $PY d98/d98_check_rational.py 1 2 7 $B; echo "exit $?"; done      # = certificates/d98_check_rational.log
(cd $OUT && Singular -q $SUP/d98/p93_resultants.sing)        # writes p93_factors_full.txt = certificates/p93_factors.txt
$PY d98/p93_analyze.py d98/certificates/p93_factors.txt 1 2 7 400   # = certificates/p93_analyze_127.log
$PY d98/p93_zeros_refine.py d98/certificates/p93_factors.txt        # = logs/p93_zeros.txt
$PY d98/p93_minima.py d98/certificates/p93_factors.txt 50           # start points of p93_zeros_refine.py (17 min)
bash d98/independent/rerun_checkers.sh $OUT/rc                      # = independent/rerun_checkers.log
for m in "3 5 13" "2 9 4" "1 2 7"; do mkdir -p $OUT/sing && $PY d98/independent/lem3_sing.py $m $OUT/sing; done
$PY d98/independent/ak_terms.py d98/certificates/p93_factors.txt
$PY audit/p98_heavy_mass.py                                          # = audit/p98_heavy_mass.txt
$PY audit/lemma69_sqfree.py d98/certificates/lemB/elim_1_2_7.txt d98/certificates/lemB/elim_1_2_8.txt d98/certificates/lemB/elim_2_3_11.txt
$PY audit/ak_shapes.py                                              # = audit/ak_shapes.txt (the factors of S_mu and S1-S8 of AK)
```

The JSON key `seconds` and the lines `time N s` record runtimes.

### Diagrams 88 and 94 (`d88/`)

```
for p in 65521 2147483647; do $PY d88/k4sys.py full 1 2 3 30 $p $OUT/full_1_2_3_30_p$p.ms
  msolve -v 1 -t 32 -g 1 -f $OUT/full_1_2_3_30_p$p.ms -o $OUT/full_1_2_3_30_p$p.lead > $OUT/full_1_2_3_30_p$p.log; done   # certificates/count/
for p in 65521 2147483647; do $PY d88/kc_sys.py full 1 2 3 30 $p $OUT/kc_full_1_2_3_30_p$p.ms
  msolve -t 16 -g 1 -f $OUT/kc_full_1_2_3_30_p$p.ms -o $OUT/kc_full_1_2_3_30_p$p.lead; done                             # certificates/kc/
$PY d88/staircase.py d88/certificates/count/full_1_2_3_30_p65521.lead   # 20,316 standard monomials (also the other three .lead)
msolve -v 1 -t 32 -f d88/certificates/count/full_1_2_3_30_p65521.ms -o $OUT/full.param > $OUT/msolve_fglm_p65521.log   # 17 min
Singular -q d88/certificates/kc/singular_std_kc_65521.sing                                    # = singular_std_kc_65521.out (27 min)
TROP_NPROC=16 $PY d88/n4_trop.py n4 1 2 3 30 65521 $OUT/work all                               # = certificates/n4_trop/ (13 min)
TROP_NPROC=16 $PY d88/n4_trop.py kc 1 2 3 30 65521 $OUT/single_pass all                        # = certificates/kc_trop/single_pass/
TROP_NPROC=16 $PY d88/kc_trop_cert.py 1 2 3 30 65521 $OUT/work                                 # = certificates/kc_trop/kc_trop_cert_1_2_3_30.log, work/
$PY d88/kc_escape.py 1 2 3 30 65521 $OUT/kc_escape_1_2_3_30.sing && Singular -q $OUT/kc_escape_1_2_3_30.sing   # and 1 1 1 5 (sanity)
$PY d88/n4_diagrams.py 1 2 3 30 $OUT/n4_1_2_3_30.sing && (cd $OUT && Singular -q n4_1_2_3_30.sing)   # = certificates/n4/; see below
TROP_NPROC=16 $PY d88/certificates/validation/val.py n4 1 1 2 2 $OUT/v1   # = validation/n4_trop_at_1_1_2_2.log
TROP_NPROC=16 $PY d88/certificates/validation/val.py kc 1 1 1 5 $OUT/v2   # = validation/kc_trop_at_1_1_1_5.log
$PY d88/k4_krawczyk.py d88/certificates/k4_sols_1_2_3_30.txt 1 2 3 30 $OUT/k4_cert_1_2_3_30.jsonl 64 256   # = k4_cert_1_2_3_30.jsonl
$PY d88/k4_check_iv.py d88/certificates/k4_cert_1_2_3_30.jsonl 1 2 3 30 64 256
$PY d88/kc_krawczyk.py d88/certificates/kc/kc_sols_1_2_3_30.txt 1 2 3 30 1 2 $OUT/kc_cert_1_2_3_30.jsonl 48 384
$PY d88/kc_check_iv.py d88/certificates/kc/kc_cert_1_2_3_30.jsonl 1 2 3 30 1 2 64 384
$PY d88/independent/my_krawczyk.py n4 d88/certificates/k4_cert_1_2_3_30.jsonl 64
$PY d88/independent/my_krawczyk.py kc d88/certificates/kc/kc_cert_1_2_3_30.jsonl 64 1 2
$PY d88/independent/run_myprev.py d88/certificates/n4_trop/work/n4_all.gfan $OUT/n4_prev.json            # 21 min
$PY d88/independent/run_myprev.py d88/certificates/kc_trop/single_pass/kc_all.gfan $OUT/kc_prev.json
$PY d88/independent/check_cells_msolve.py d88/certificates/n4_trop/work/n4_all.gfan d88/independent/myprev/n4_prev.json d88/certificates/n4_trop/work/n4_all.fan $OUT/n4_cells 65521 24
$PY d88/independent/check_cells_msolve.py d88/certificates/kc_trop/single_pass/kc_all.gfan d88/independent/myprev/kc_prev.json d88/certificates/kc_trop/single_pass/kc_all.fan $OUT/kc_cells 65521 16
(cd d88/independent/m2count && M2 --script kc_count.m2; M2 --script n4_count.m2)   # degrees 4788 and 20316 (n4: 47 min, 37 GB)
$PY audit/kc_ttest_count.py d88/certificates/kc/kc_cert_1_2_3_30.jsonl        # = audit/kc_ttest_count.txt
$PY audit/kc_ttest_count_float.py d88/certificates/kc/kc_cert_1_2_3_30.jsonl  # = audit/kc_ttest_count_float.txt
```

The approximate solutions from which the Krawczyk programs start (`k4_sols_1_2_3_30.txt`, `kc/kc_sols_1_2_3_30.txt`)
are in an exact text form, each value in `float.hex` (`d88/arrayio.py`; the original tree stored them as NumPy files).
The cell tests of `independent/myprev/val1122_cells/` read the gfan input at (1,1,2,2), which the validation run writes
(`n4_trop.py n4 1 1 2 2 65521 V all` writes it to `V/`). `count/singular_std_65521.out` is empty: that Singular run
never finished, and the count rests on msolve and Macaulay2. `n4/n4_1_2_3_30.out` is the output of a run that was
stopped: its last system, over Q, does not finish; stop it with SIGTERM (SIGINT appends Singular's prompt).
`independent/myprev/val1122_prev.json.log` is the log of an unfinished run of `run_myprev.py` at (1,1,2,2). The logs of
the msolve runs and `k4_check_iv`, `my_krawczyk` also record runtimes.

### Diagrams 64 and 66 (`d64/`)

```
$PY d64/e4_cert_macaulay.py 3 5 7 11 2147483629                   # = certificates/e4_cert_macaulay_3_5_7_11.json
Singular -q d64/e4_cert_singular.sing                             # = certificates/e4_cert_singular_3_5_7_11.log
Singular -q d64/c4_cert_singular.sing                             # = certificates/c4_cert_singular_3_5_7_11_p32003.log
$PY d64/c4_cert_msolve.py 3 5 7 11 1073741789 $OUT/c4_msolve_work  # = certificates/c4_cert_msolve_3_5_7_11.json, c4_msolve_work/
bash d64/c4_compare_builders.sh                                   # = certificates/c4_compare_builders.log
$PY d64/c4_model_sanity.py                                        # = certificates/c4_model_sanity.log
$PY d64/e4_reduction_check.py                                     # = certificates/e4_reduction_check.log
$PY d64/cells_table.py; $PY d64/cells_xrange.py                    # = certificates/cells_22.txt, cells_22_xrange.txt
M2 --script d64/independent/third_impl.m2                         # = independent/third_impl.log (9 min)
Singular -q d64/independent/direct_e4_c4.sing
Singular -q d64/independent/collinear_saturated.sing              # = independent/collinear_saturated.log
for m in "1 1 1 1" "1 1 1 2" "1 1 2 2" "1 2 3 4" "2 3 5 7"; do t=${m// /_}
  { $PY d64/e4_cert_macaulay.py $m 2147483629; echo "exit=$?"; } > $OUT/e4_$t.json
  { $PY d64/c4_cert_msolve.py $m 1073741789 $OUT/ms_$t; echo "exit=$?"; } > $OUT/c4_$t.json; done   # = independent/scope/
{ $PY d64/e4_cert_macaulay.py 5 2 11 3 2147483629; echo "exit=$?"; }   # = d64/independent/rerun/robust/e4_macaulay_5_2_11_3.json
$PY audit/e4_equal_mass.py                                        # = audit/e4_equal_mass.txt
Singular -q audit/d64_equal/e4_cert_singular_1_1_1_1.sing; Singular -q audit/d64_equal/c4_cert_singular_1_1_1_1.sing
```

Give `c4_cert_msolve.py` a work directory: by default it writes into the supplement.

### Hand explanations (`hand_explanations/`)

The programs write into their own `data/` directories (and the independent ones into their working directory), so run
them in a writable copy of the supplement, or in a copy of `hand_explanations/` next to links to `engine/`,
`results/`, `diagrams/` and `cliques/`. Three interpreters are named below: `PY`, a Python with numpy, scipy, highspy
and python-flint; `PYS`, a Python with SymPy and mpmath; `PYSH`, one Python with both highspy and SymPy (for
`exact_templates.py`, `verify_templates.py`, `p4_check.py`); each run with `-I -B`.

```
mkdir -p hand_explanations/residual/data/work            # the temporary directory of the no-label core programs
cd hand_explanations/mechanisms/scripts
$PY collect_single.py; $PY collect_cores.py; $PY cores_classify1.py
$PYS cores_types.py; $PY core_patterns.py                 # cores_types: 9 min
$PYS coverage.py > ../data/coverage.log                   # data/coverage.jsonl, coverage_summary.json (3 min)
$PY tables.py; $PY per_class_table.py > ../data/per_class_table.md; $PY counts_v2.py > ../data/counts_v2.log
$PY lpcheck.py 0 > ../data/lpcheck_full.log               # 11 min
for L in "E1 1000" "R1 1000" "R6 1000" "R5 500"; do $PY insitu.py $L; done > ../data/insitu.log
$PY insitu.py Q 300 > ../data/insitu_Q.log
$PYS check_labels.py
(cd .. && for c in checks/*.sing; do Singular -q $c > ${c%.sing}.out; done)
cd ../../residual/scripts
$PY run_resid.py; $PY insitu_resid.py; $PY global_cover.py > ../data/global_cover.log; $PY insitu_sample.py 150
$PY nolabel_list.py; $PY certs_dump.py; $PYS algebra_resid.py; $PY tables_resid.py
$PY tiers_v2.py; $PY r1star_branches_v2.py > ../data/r1star_branches_v2.log; $PY dump_resid.py > ../data/resid_dump.txt
(cd .. && $PYS checks/L_steps.py && $PYS checks/coreA_steps.py && for c in R1star W3 EQ2 TQ coreB; do Singular -q checks/$c.sing > checks/$c.out; done)
$PY coreAB_num.py
$PY coreC.py coreC_part1.txt 854f9cb97f452836 a942ebc464768f1a 9dc44c4284b43aee 2e39da8594e724c4 78d53510b38736e3 de05f2d8fe3db5f1 9861d60ca184c3e3 01c96ebcb817106e
$PY coreC.py coreC_part2.txt 9c5d5a0eb5274caf c1343e65a5f12f68 9d52073c7df67ada a7135526b888cf20 f88fb651a732d579 > ../data/coreC_part2.log
$PY coreC_sub.py; $PY coreC_table.py; $PY coreC_sub_table.py
cd ../../independent/scripts
$PY run_ref.py ref_cover.jsonl 12 > run_ref.log; $PY run_resid.py ref_resid_cover.jsonl 12 > run_resid.log
$PY ref_lp.py ref_cover.jsonl ref_lp.jsonl 12 > ref_lp.log; $PY resid_certs.py > resid_certs.out
$PYS L_identity.py > L_identity.out && $PYS L_identity2.py >> L_identity.out
for s in compare_cov cmp_resid cmp_global_resid cumul_ref single_acct table21 misc_counts final_partition clique_overlap families_check; do $PY $s.py > $s.out; done
ALL_TEMPLATES=1 $PYSH exact_templates.py > exact_templates_all.out; ALL_TEMPLATES=1 $PYSH p4_check.py > p4_check_all.out
$PYS resid_polys.py > resid_polys.out
(cd .. && for c in sing/*.sing; do Singular -q --no-warn $c > ${c%.sing}.out; done)
cd ../../audit
$PY hand_coverage.py ../independent/final_classification.jsonl ../residual/data/tiers_v2.jsonl ../../cliques ../.. ../../audit/per_class.tsv ../../results/GENERIC_OPEN.txt ../mechanisms/data/coverage.jsonl > hand_coverage.txt
$PYS cell_polys.py ../independent/scripts ../independent/scripts/ref_resid_cover.jsonl ../independent/final_classification.jsonl > cell_polys.txt
$PY zw_triangle_classes.py ../../diagrams/n6.json ../../audit/per_class.tsv > zw_triangle_classes.txt
```

The three programs of `audit/` reproduce their outputs byte for byte (`hand_coverage.py` about a minute). The rerun of
the independent checkers from a fresh copy of their scripts, with the same commands as above, is recorded in
`audit/rerun/` (its driver `driver.sh`, its outputs and `driver.log`) and compared with the stored outputs in
`audit/rerun_compare.txt`.

`final_partition.py` writes `../final_classification.jsonl`. The no-label core programs (`coreAB_num.py`, `coreC.py`,
`coreC_sub.py`) take about three hours of Singular on one core and use fixed temporary files in `data/work/`, so run
one of them at a time in a tree; `checks/L.sing` and `checks/coreA.sing` are eliminations that do not finish
(`coreA.out` records the stop). `coreC.py` gives up on a branch after 900 s: branch 1 of core `9d52073c7df67ada` in
`coreC_part1.txt` needs about 930 s, so on a slower machine it is reported as a timeout. The programs walk the
classes as `results/exact6/c*`, while the stored outputs followed the directories of the original runs, so most
regenerated files hold the same lines in another order. `data/systems_index.jsonl` and `inputs/core_types.json` name
the stored cells by their paths in this supplement. The outputs of the exploration programs `run_corefam.py` and
`run_tri.py` (`data/corefam.jsonl`, read by `rem_cores.py` and `run_tri.py`, and `data/tri_status.jsonl`) and of the
sample mode of `coverage.py` are not shipped; the notes do not use them, and the programs regenerate them.

## Re-check of 2026-10-17

Before release, every computation above was run again from a fresh copy of this supplement and compared with the stored
files.

* **Engine pipeline, all 191 classes** (`exact_job.sh`, six machines, about 2.2 hours, the stopped core searches
  stopped at the times of the stored runs): of the 247,654 stored files of `results/exact6/`, 242,770 are
  reproduced byte for byte; the 4,818 `replay.json` that differ do so only in the timing fields `time` and
  `max_cert_time`; the 66 `cert.jsonl` that differ do so because `tcert.py` of `generic-v1` hashes a core with its
  saturation set and writes in completion order, and the verdict of every cell agrees, except for the 91 cells of
  classes 30 and 149 whose certification had never run: 33 of them now have a certified core and 58 a core without
  answer within 600 s (all 91 are certified by alternative cores). The 32 stopped core searches give the same files.
* **Alternative cores:** `alt3_job.sh` reproduces all 600 records of `alt3_out.jsonl`, and `alt_job.sh` all 390
  records of `alt_out.jsonl` (the same lines in another order). The 43 open cells, for which the stored file has no
  records, are not part of the comparison.
* **Hand explanations:** every stored output of `hand_explanations/` is reproduced byte for byte, or up to runtimes,
  the order of lines and the examples or samples chosen in that order (`core_patterns.json`, `coreAB_num.txt`,
  `insitu_sample.log`), and the exit line that the original wrapper added to `residual/checks/coreB.out`, except the
  timeout named above.
* **Other checks:** every output listed above is reproduced byte for byte, or up to runtimes, the date, the Singular
  version line, Macaulay2's cpu field and the order of lines, with these exceptions: `test_negctl.py` (the change of
  `treplay.py`, above); one Macaulay2 recertification in `recert_alt.py` (class 3, cell 40246) now finishes within
  900 s (stored: timeout; the totals are 972 unit and 18 timeouts against 971 and 19); in `lift_alt.py` the Singular
  lift of class 3, cell 41569 finishes at 2,393 s (stored: stopped at 2,400 s) and its Macaulay2 check stops at
  2,400 s, so it still has no second certificate; `m2_fix1.log` records two runs (18 cores, then one more in
  `m2_fix1_last`), and one run over the 19 gives the same records; the Macaulay2 run of `m2_unsat.py` that gives a
  unit ideal took 5,864 s (stored 7,050 s). Not re-run: the 13 Macaulay2 runs of `m2_unsat.py` that timed out at 7,200 s, the Singular run of
  `count/singular_std_65521.sing` (stopped after 54 minutes without output, as the stored one), and `cmp.py` (the
  pipeline itself was re-run).

### Lean (`lean/`)

Each of the three directories is a git archive of its project at the commit in `lean/COMMITS` (`lean6` at `17f8b22`,
`lean6_special` at `3bb1297`, `lean6_full` at the commit named there), with the changes listed in `CHANGES.md`: edits
of documentation and of docstrings (in five Lean files, `lean/sections3-5/L6Poly/Basic.lean`,
`lean/sections6-9/Lean6/Special/Ball/Kraw.lean`, `lean/sections6-9/L6KSpec/C4Check.lean`,
`lean/sections6-9/L6KSpec/C4Load.lean` and `lean/sections6-9/L6SoundKSpec/C4Cert.lean`, of the docstrings only), the
wording of one script and of the log it writes (`lean/sections3-5/scripts/f4/replaced_table.py`,
`logs/f4/replaced_table.md`), the comments of `lean/full/check_v3.sh`, and, in `lean/full/`, the paths of the sibling
packages (`Compose/lakefile.toml`, `Compose/lake-manifest.json`, `check.sh`, `check_v3.sh`, `README.md`). In
`lean/sections3-5/` the cell files ship compressed and the internal `PLAN.md` is left out; `lean/COMMITS`,
`lean/sections3-5/data/f4/certs_parts.sha256`, `lean/sections3-5/scripts/fetch_data.sh`,
`lean/sections6-9/data/kern/kcert_parts.sha256` and `lean/sections6-9/scripts/fetch_kern_certs.sh` are added. No Lean
definition or proof differs from the commits: `docstring_only_check.txt` shows, for each of the five Lean files, that
the shipped text differs from the commit only in comments and docstrings (`docstring_only_check.py`, with negative
controls). The documentation edits remove the names of internal work tracks, branches and working sessions, and
`lean/sections3-5/LEAN_CHECKS.md` points to `../full`, where the framework and the conditions `Cond` for germs are
proved (`cond_of_germ`, `Compose/CC6Compose/CellsConv.lean`, on which the bridge `germ_cell_stored` of Proposition 4.5
rests); `lean/full/README.md` describes the formal proof.

`lean/README.md` gives the build of the three packages (Lean `v4.35.0-rc3`, Mathlib pinned in each
`lake-manifest.json`) and the check of version 3, `lean/full/check_v3.sh`. The release run, on machines with 384
hardware threads and 708 GiB of memory (`lean/full/README.md`, Building and checking, Version 3, which gives the
details; the logs are in `logs/release_check_v3/`): the kernel stages of `lean/sections3-5/` took 6 h 18 min and about
963 CPU-hours, almost all of it the fused check of F2-F4 (31,324 modules, 894 CPU-hours), which was split over three
machines and completed after their outputs were gathered, with a largest single process of 26.7 GiB; the kernel stages
of `lean/sections6-9/` took 2 h 21 min and 45.0 CPU-hours, with a largest single process of 40.7 GiB; and the release
check itself, `check_v3.sh` with both stage lists empty on the kernel checks so built, took 15 min 33 s and 8.1
CPU-hours, with a peak of 31.2 GiB of memory in use, and ended with `check_v3.sh: OK`.

Two kinds of logs record the checks of version 3. `logs/release_check_v3/` holds the logs of the developers' release
run on the pinned commits: `check_v3.log` (the release check, `lean/full/check_v3.sh`), `sp_stages.log` (the kernel
stages of `lean/sections6-9/`), `stage2.log` and `stage2f.log` (the kernel stages of `lean/sections3-5/`, the fused
stage completed after its parts were gathered from three machines), the logs of the runs, and `mem.log` (memory
samples). `logs/check_staged_layout_v3.log` is the check of the staged release layout: `lean/full/check_v3.sh` run on
`lean/` as shipped here, with the kernel checks of the release run reused (`L6_STAGES` and `SP_STAGES` empty) after
their outputs were verified against the pinned sources. The release check ended with `check_v3.sh: OK`
(`CC6Full` and the composition built in 890 s, `Check.lean` OK with 47 theorems on the three standard axioms only,
and "CC6Compose.V3.main_theorem_v3 depends on propext, Classical.choice, Quot.sound and the auxiliary axioms of the
F4 runs behind count_S12 and count_KC, nothing else"). The check of the staged release layout first verified the
reused outputs (`lean6`'s verification of its sources against `17f8b22`, its certificates, generated files and `out/`,
ending with "l6reuse: VERIFIED"; the sources of `lean6_special` and `lean6_full` in the release run's tree against git
archives of `3bb1297` and `027dfd1`, with no other files than build outputs) and listed the differences of the shipped
`lean/` from the pinned commits, which are exactly the files of `CHANGES.md`, the compressed cell files and the omitted
`PLAN.md`. It then ran `check_v3.sh` on the shipped `lean/`: `CC6Full` and the composition built in 454 s, `Check.lean`
OK, the same axiom line for `main_theorem_v3`, and `check_v3.sh: OK` (9 min 31 s on a machine with 384 hardware
threads; largest resident set 28.7 GB), with its files unchanged afterwards. The checked tree is the shipped `lean/`
except `lean/README.md`, this supplement's description of the packages, which was rewritten for version 3 after the
check. Of the five Lean files with
docstring-only edits, Lake recompiled `L6Poly/Basic.lean` and `Lean6/Special/Ball/Kraw.lean` from the shipped text, with
the modules of the composition that depend on them; `L6KSpec/C4Check.lean`, `L6KSpec/C4Load.lean` and
`L6SoundKSpec/C4Cert.lean` belong to the reused kernel checks and were not recompiled. For all five,
`docstring_only_check.txt` shows that the shipped text differs from the commit only in comments and docstrings.

## Changes from the original files

The files are those of the original computations, except the files listed in `CHANGES.md`: absolute paths of the
author's machines are replaced by paths relative to this supplement, the directory level that named the machines of
the runs is dropped (`results/exact6/c<N>/`), a few docstrings that named working directories are reworded, and the
notes of `results/GENERIC_OPEN.txt` name where the paper excludes the 43 cells. No mathematical content and no stored
result changes. `CHANGES.md` also lists the files written for this supplement: drivers whose output the stored files
hold (each reproduces its file), the logs of `d88/staircase.py`, and `audit/exact_summary_generic-v1.out`.

## Licences

Programs: Apache License 2.0 (`LICENSE`). Data, logs and documents: Creative Commons Attribution 4.0 International
(`LICENSE-CC-BY-4.0.txt`). `diagrams/chang_chen_diagrams.json` transcribes the 117 diagrams of K.-M. Chang and
K.-C. Chen, arXiv:2303.02853 (J. Symbolic Comput. 123 (2024), 102277); `diagrams/README_chang_chen_diagrams.md` gives
the source and how the diagrams were read. Cite their work when using it.
