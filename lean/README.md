# Lean 4: the formal proof of Theorem 1.1 and the checks of the computations

Version 3 of this supplement contains a Lean proof of Theorem 1.1 with no hypotheses that Lean's kernel checks except
two computations, the dimension bounds of Lemma 6.19(b): `CC6Compose.V3.main_theorem_v3 : CC6Full.MainTheorem`
(`full/Compose/CC6Compose/V3/Release.lean`, Section 10.1 of the paper) depends on `propext`, `Classical.choice`,
`Quot.sound` and the two auxiliary axioms of `native_decide` of the F4 runs behind `count_S12` and `count_KC`
(`Lean6.Special.Comp.Count.s12_f4_ok._native.native_decide.ax_1_1`, `….kc_f4_ok._native.native_decide.ax_1_1`). Each
such auxiliary axiom states the result of a compiled evaluation, so these two computations trust the Lean compiler and
the execution of the compiled code; everything else is checked by the kernel (`decide +kernel` for the computations).
Version 2's theorem `CC6Compose.main_theorem`, whose computations all run as compiled code, is kept. Three Lake
packages, all with Lean `v4.35.0-rc3` and Mathlib `c55e6e7`:

* `full/`: the framework `CC6Full`, which formalizes the theory of Sections 2–8 (standard axioms only; `Check.lean`
  prints the axioms of 47 of its theorems), and the package `full/Compose/`, which proves the bridges from the checked
  statements of the two other packages to that theory, and the main theorems: `main_theorem_v3` on the kernel checks,
  `main_theorem` on the compiled ones. `full/README.md` gives the statement, the axioms and what they trust, the
  departures from the paper's proofs, the computations and their bridges, and the build; `full/check_v3.sh` (also
  `./check.sh v3`) checks version 3, `full/check.sh` version 2.
* `sections3-5/`: the checks of Sections 3–5 (the diagrams, the cells with the completeness of their list, their
  exclusion at generic masses, the clique census), with their kernel-only versions (`L6K/`, `L6SoundK/`, `L6CheckK/`,
  and the generated `L6CheckF/` of the fused check of F2–F4). `sections3-5/LEAN_CHECKS.md` lists every theorem, what
  it checks and assumes, its axioms and its running time; the framework, which that package states without
  formalizing it, is formalized in `full/`.
* `sections6-9/`: Sections 6–9 and the computations inside the hand proofs, both parts of Lemma 6.19(b) among them,
  with the kernel-only versions of the computations of Sections 6 and 7 (`L6KSpec/`, `L6SoundKSpec/`, `L6CheckKSpec/`,
  and the generated `L6CheckC4/`, `L6CheckTrop/`). `sections6-9/LEAN_CHECKS.md` lists them in the same way.

Their notes call them `lean6_full`, `lean6` and `lean6_special`, and their directories in the author's tree
`rung3/lean6_full`, `rung3/lean6` and `rung3/lean6_special`. Each is the version-3 commit of its development
(`COMMITS`), with the edits that `../CHANGES.md` lists; `full/Compose/` and `full/check_v3.sh` refer to the other two
packages as `../sections3-5` and `../sections6-9`. In `sections3-5/` the stored cells ship compressed
(`data/cells/c<N>.jsonl.xz`). Two sets of inputs ship as archive parts of the supplement: the 1,928 cofactor
certificates of `sections3-5/` (22 parts, `data/f4/certs_parts.sha256`, as in versions 1 and 2) and the 16 input
files of the kernel checks of `sections6-9/` (`data/kern/kcert_parts.sha256`; `data/kern/SHA256SUMS` lists the digests
of their uncompressed contents).

## Build and check of version 3

```
cd sections3-5
bash scripts/fetch_data.sh [PARTS_DIR]       # the cells, and the 1,928 certificates from their parts, all checked
bash scripts/poly/unpack_certs.sh            # plain texts of the certificates, read by the checks
lake exe cache get
cd ../sections6-9
bash scripts/fetch_kern_certs.sh [PARTS_DIR] # the 16 inputs of the kernel checks from their parts, all checked
lake exe cache get
cd ../full
lake exe cache get
(cd Compose && lake exe cache get)
./check.sh v3                                # = check_v3.sh
```

The scripts download the parts from the supplement (https://doi.org/10.5281/zenodo.23451291) unless given a directory
that holds them. `check_v3.sh` scans the sources for forbidden keywords; builds the kernel checks of `sections3-5/` and
`sections6-9/` with their drivers (`scripts/kern/build.sh` in each, which compile the check modules with `lean`
directly into the package's `out/` under a memory budget and compare the generated files with the committed SHA-256
lists); builds `CC6Full` and the composition; compiles `V3/Kernel.lean` and `V3/Release.lean` against the kernel
checks; and requires the axioms of `main_theorem_v3` to be exactly the five above. Environment: `JOBS` (Lean processes
run by Lake at once, default 40), `BUDGET_GB` (the drivers' memory budget, default 600 GB), `L6_STAGES`, `SP_STAGES`
(the drivers' stages; the empty string uses the package's `out/` as built before). The kernel checks are expensive:
in the release run the stages of `sections3-5/` took about 963 CPU-hours, almost all of it the fused check of F2–F4,
which the driver can split over several machines by class (`sections3-5/scripts/kern/build.sh`), and those of
`sections6-9/` 45 CPU-hours, with single processes of up to 40.7 GiB; `full/README.md` (Building and checking,
Version 3) gives the measurements, and `../logs/release_check_v3/` holds the logs. Version 2's check is `./check.sh` in
`full/` after `scripts/build_all.sh` in `sections3-5/` (`full/README.md`, Version 2).

The paths in `sections6-9/data/*/SHA256SUMS*` other than the lists of the kernel checks (`data/kern`, `data/c4k`,
`data/tropk`) name the input files of the original computations. Those of the form `rung3/<directory>/...` are in the
author's tree; in the supplement they are at `d64/`, `d64/certificates/`, `d64/independent/`, `d88/`,
`d88/certificates/`, `d88/independent/`, `d98/certificates/` and `audit/` (`rung3/d64/scripts/` is `d64/`,
`rung3/d88/scripts/` is `d88/`, `rung3/d88_referee/tools/` is `d88/independent/`, `rung3/d64_referee/scratch/` is
`d64/independent/`, `rung3/paper_generic/audit/` and `rung3/paper_generic/tools/` are `audit/`, and otherwise `rung3/`
is dropped). The paths of `data/d88boxes/SHA256SUMS` are relative to `d88/certificates/`, and those of
`data/d98/SHA256SUMS` to the root of the supplement. All 44 recorded hashes match the files of the supplement.
