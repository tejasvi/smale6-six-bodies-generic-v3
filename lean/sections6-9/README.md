# Lean 4 checks of the computations of Sections 6–9

Lean 4 checks of the computer certificates in Sections 6–9 of the paper "Smale's sixth problem for six bodies in the
plane: finiteness of central configurations for generic masses", and of the computations inside the hand proofs of
those sections. The mathematical framework (Lemma 6.18, Lemma 7.10 and the other hand proofs) is stated in the
paper, not formalized; each computation is checked by an exact checker run with `native_decide`, with a soundness
theorem proved in Lean that says what a successful run means.

* `LEAN_CHECKS.md`: per claim of the paper, the Lean theorem, what it proves, what it assumes, how to run it, its cost
  and axioms, and the claims not checked in Lean.
* `PLAN.md`: the inventory written before the work.
* `Lean6/Special.lean`: the root module; `Lean6/Special/Comp/`: the checkers (no Mathlib, compiled);
  `Lean6/Special/{Hand,D98,D88,K4}/`: the statements and soundness proofs.
* `gen/`: the generators of the data modules and the axiom scripts; `data/`: the sha256 sums of the inputs;
  `logs/`: build logs, axioms, negative controls.
* `Cover/`: Proposition 9.23 (which cells the lemmas of Section 9 cover), a separate Lake package. It requires the
  companion project `lean6` checked out beside this repository (`../lean6`); it was built against `lean6` commit
  `d593063` (branch `upd-exclusion`), and the `lean6` modules it uses are unchanged since `lean6`'s release `6fb8b01`.
  Run `cd Cover && lake build` (about 3 min once `lean6`'s libraries are built).

Run (Lean `v4.35.0-rc3`, Mathlib `c55e6e7`; `lake exe cache get` fetches Mathlib's build):

```
ulimit -n 65536                         # on machines with many cores
lake build                              # 10 min 19 s wall on 384 cores, 5.1 CPU-hours, 15 GB
lake env lean gen/axioms_all.lean       # the axioms of the final theorems
```

The ball arithmetic and the Krawczyk test are taken from the Lean development of the five-body paper.

## Kernel-only versions

The libraries `L6KSpec`, `L6SoundKSpec` and the check modules `L6CheckKSpec`, `L6CheckC4`, `L6CheckTrop` prove
Lemma 6.19(c), (d) with the counts of §6.7, Lemma 6.9 and the check at (1,2,7), Lemma 7.7 with the check after
Proposition 7.8, Lemma 7.9 at μ₀ over F_32003, and Lemma 6.19(a) by `decide +kernel`,
with the standard axioms only. With the cofactor certificates and the trace of `hypsN4` in `data/kern/cert/`
(distributed separately),
`bash scripts/kern/build.sh libs boxes d98 e4 c4gen c4 tropgen trop tropmem axioms` regenerates the generated modules
and data, compares them with the committed SHA-256 lists, and compiles them under a memory budget; see
`LEAN_CHECKS.md`, Kernel-only versions.
