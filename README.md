# Smale's sixth problem for six bodies in the plane: finiteness of central configurations for generic masses, with a proof formalized in Lean

Programs and certificates for the paper of the same title by Tejasvi Singh Tomar (independent researcher, ORCID
0000-0003-4668-3639).

* Paper: https://doi.org/10.5281/zenodo.23451290
* Supplement with all data (the stored runs of the engine, the large certificates and outputs, and the cofactor
  certificates of the Lean checks, as compressed archives): https://doi.org/10.5281/zenodo.23451291

This is version 3: Lean's kernel checks the formal proof of Theorem 1.1, except two computations, the dimension
bounds of Lemma 6.19(b). Version 2 (paper https://doi.org/10.5281/zenodo.23440983, supplement
https://doi.org/10.5281/zenodo.23440984, repository https://github.com/tejasvi/smale6-six-bodies-generic-v2 at commit
210ced5d612bacdc17fcab65ae610f0696f5eb23) added the formal proof (`lean/full/`), whose larger computations ran as
compiled code; version 1 (paper https://doi.org/10.5281/zenodo.23433407, supplement
https://doi.org/10.5281/zenodo.23433410, repository https://github.com/tejasvi/smale6-six-bodies-generic at commit
f51cba739eb2bb4900b23c52c6c1329f6fece3ff) checked in Lean the computations on which the proof rests.

## What is proved and what this repository checks

The paper proves that for six bodies in the plane and all positive masses outside a proper algebraic subset of the
mass space, the number of central configurations up to similarity is finite. The proof follows Albouy and Kaloshin:
infinitely many central configurations would give a curve of complex solutions, and the valuations of the mutual
distances at its points at infinity must balance. The computer-assisted parts, all in this repository:

1. **Diagrams** (`diagrams/`, Proposition 3.1): the 191 classes of zw-diagrams of six bodies allowed by the rules
   used, enumerated twice by programs written separately.
2. **Cells** (`engine/`, Proposition 4.5): for each class, the possible valuations at a point at infinity where the
   product of the mutual distances does not tend to zero, as 91,273 polyhedral cells; every pruning step of the
   enumeration carries an exact rational certificate.
3. **Generic exclusion** (`engine/`, Proposition 5.3): all but 43 cells are excluded at generic masses, by a single
   dominant term of an identity (exact linear-programming certificates) or by a subset of the leading equations that
   generates the unit ideal over the field of rational functions of the masses (Singular); Macaulay2 recertifies all
   but ten of the 2,413 certified cores (`engine/independent/`).
4. **The seven remaining diagrams** (`d98/`, `d88/`, `d64/`, Sections 6 and 7): eliminations, ball-arithmetic and exact
   rational certificates, solution counts modulo primes with tropical prevarieties and cone tests, and Krawczyk
   certificates, each with an independent second check.
5. **Lean** (`lean/`, Section 10.1): Theorem 1.1 is proved in Lean 4 with no hypotheses. In version 3 Lean's kernel
   checks the proof, `CC6Compose.V3.main_theorem_v3 : CC6Full.MainTheorem`
   (`lean/full/Compose/CC6Compose/V3/Release.lean`), except two computations, the dimension bounds of Lemma 6.19(b):
   its axioms are `propext`, `Classical.choice`, `Quot.sound` and the two auxiliary axioms of `native_decide` of the F4
   runs behind `count_S12` and `count_KC`. The framework `CC6Full` formalizes the theory of Sections 2–8 with the
   standard axioms only, the bridges in `lean/full/Compose/` connect it to the checks of the computations, and the
   certificate projects `lean/sections3-5/` and `lean/sections6-9/` carry kernel-only checks of those computations
   (`decide +kernel`) next to the checks of versions 1 and 2. `lean/README.md` gives the build and
   `lean/full/check_v3.sh` the check of version 3 (`lean/full/check.sh` checks version 2's theorem
   `CC6Compose.main_theorem`); `lean/sections3-5/scripts/fetch_data.sh` and `lean/sections6-9/scripts/fetch_kern_certs.sh`
   fetch the cofactor certificates from the supplement, checking every file against its SHA-256.

## Layout

| directory | contents |
|---|---|
| `diagrams/` | the enumeration of the diagrams and its outputs, the comparison with the 117 diagrams of Chang and Chen, and `separate/`, the second enumeration |
| `engine/` | the programs of Sections 4 and 5 (tag `generic-v1` of the author's engine repository, commit `d257663d`), the job scripts (`jobs/`) and the independent checks (`independent/`, outputs in `independent/out/`) |
| `results/` | the lists of uncertified cells, the alternative cores and the 43 open cells; the per-class runs (`results/exact6/`) are in the supplement |
| `audit/`, `cliques/` | counts, summaries and the census of Proposition 9.19 |
| `d98/`, `d88/`, `d64/` | the computations of Sections 6 and 7 with their certificates and independent checks |
| `hand_explanations/` | the explanation of every cell by hand mechanisms (Section 9): the notes `MECHANISMS.md` and `RESIDUAL.md`, their programs and checks, an independent re-implementation and classification, and the coverage of Proposition 9.23 from both (`audit/`) |
| `tools/ms_lint.py` | the strict syntax check of msolve inputs |
| `lean/` | the Lean 4 proof (`full/`, with `README.md`, `check_v3.sh` for version 3 and `check.sh` for version 2) and the checks of the computations, with their kernel-only versions: `sections3-5/` and `sections6-9/`, each with `LEAN_CHECKS.md` (every theorem, what it checks and assumes, its axioms and cost) |

`SUPPLEMENT.md` is the description of the supplement: every directory, the versions of the programs, the software, the
input hygiene, the command that re-runs each check with its runtime, and the record of the re-check made before
release. `CHANGES.md` lists the files that differ from the files of the original computations, with the reason and
the SHA-256 of each original, and the files written for the supplement.

## Data that are only in the supplement

The stored runs of the engine (`results/exact6/c<N>/`, 247,654 files) and the files larger than 5 MB are in the
supplement, not here; `SUPPLEMENT_ONLY.txt` lists the latter (among them the Krawczyk boxes of `d88/certificates/`, the
approximate solutions they start from, and the outputs of the hand explanations). The 1,928 cofactor certificates of
the Lean checks are in the supplement as 22 archive parts, which `lean/sections3-5/scripts/fetch_data.sh` downloads and
checks. Unpack the other archives of the supplement at the root of a copy of this repository; their `SHA256SUMS`
covers every file.

## Running

Python 3.13 or 3.14 with numpy, scipy, sympy, mpmath, highspy and python-flint 0.9.0; Singular 4.4.1; msolve 0.9.4;
gfan 0.7; Macaulay2 (independent checks). From the root of the repository:

```
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 RAYON_NUM_THREADS=1 LC_ALL=C
python3 -I -B diagrams/zwenum.py 6 --out /tmp/zwenum_n6.json        # 191 classes, 82,712 labelled diagrams
CLASSES=63 P=8 NP=384 PY=python3 bash engine/jobs/exact_job.sh       # one class of the pipeline -> engine/runs/exact6/c63/
python3 -I -B d98/d98_certify_arb.py 1 2 7 1 2 7 /tmp/d98.json       # Lemma 6.13 at (1,2,7), Arb
```

`SUPPLEMENT.md` gives all the commands.

## Citation

```
@misc{Tomar2026SixBodiesGeneric,
  author = {Tomar, Tejasvi Singh},
  title  = {Smale's sixth problem for six bodies in the plane: finiteness of central configurations for generic masses, with a proof formalized in Lean},
  year   = {2026},
  doi    = {10.5281/zenodo.23451290},
  note   = {Preprint}
}
@software{Tomar2026SixBodiesGenericSupplement,
  author  = {Tomar, Tejasvi Singh},
  title   = {Supplementary material for "Smale's sixth problem for six bodies in the plane: finiteness of central configurations for generic masses, with a proof formalized in Lean"},
  year    = {2026},
  doi     = {10.5281/zenodo.23451291},
  version = {3}
}
```

## Licences

Programs: Apache License 2.0 (`LICENSE`). Data, logs and documents: Creative Commons Attribution 4.0 International
(`LICENSE-CC-BY-4.0.txt`). `diagrams/chang_chen_diagrams.json` transcribes the diagrams of K.-M. Chang and K.-C. Chen
(arXiv:2303.02853); cite their work when using it.
