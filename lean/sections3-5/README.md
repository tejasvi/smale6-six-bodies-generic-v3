# Lean 4 checks of the computations of Sections 3–5 (version 1)

Lean 4 checks of the computer certificates of Sections 3–5 of the paper *Smale's sixth problem for six bodies in the
plane: finiteness of central configurations for generic masses*: the diagrams (Proposition 3.1), the cells
(Proposition 4.5), their exclusion at generic masses by single terms and by cores with cofactor certificates
(Proposition 5.3), and the clique census of Section 9 (Proposition 9.19); the paper's §10.1 summarizes these checks.
Every computation is evaluated by `native_decide`; what a passing computation means is proved without `sorry`; the
mathematical framework of the paper is stated there, not formalized here.

See `LEAN_CHECKS.md` for every theorem, what it checks and assumes, its axioms and its running time.

## Build

Toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib as pinned in `lake-manifest.json`.

1. Place the 1,928 cofactor certificates in `data/f4/certs/` (distributed separately, 1.2 GB) and check them:
   `bash scripts/poly/verify_certs.sh`.
2. `lake exe cache get` (Mathlib).
3. `bash scripts/build_all.sh`: unpacks the certificates to plain text (`data/f4/certs_txt/`, 3.4 GB; `include_str`
   cannot read compressed files), writes their modules, and builds `L6Sound` and `L6Check`. On 384 cores the build
   took 31 minutes before later modules were added; the check modules of the specification search, built on top,
   took another 11 minutes (`LEAN_CHECKS.md`, How to run). The axioms of the main theorems are printed into the build
   log.

## Kernel-only checks

The libraries `L6K`, `L6SoundK` and the check modules `L6CheckK`, `L6CheckF` prove Proposition 3.1, the 1,928
certificates of Lemma 5.2, and Propositions 4.5 and 5.3 at every pair satisfying `Cond` (`L6CheckF.fusedK`) by
`decide +kernel`, with the standard axioms only. `bash scripts/kern/build.sh libs f1 f4gen f4 f4link f34kexport
f34kgen f34k` regenerates the generated modules and data, compares them with the committed SHA-256 lists, and compiles
them under a memory budget; see `LEAN_CHECKS.md`, Kernel-only checks.
