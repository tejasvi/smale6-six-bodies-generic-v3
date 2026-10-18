# PROGRESS: the Lean proof of the six-body theorem (CC6Full)

State of 2026-10-17, 19:55 UTC (12:55 Pacific). Plan: `FULL_PLAN.md`; overview: `README.md`.

## Result

`CC6Compose.main_theorem : CC6Full.MainTheorem` (`Compose/CC6Compose/Theorem.lean`): Theorem 1.1, without hypotheses.
Axioms (`Compose/Check.lean`): `propext`, `Classical.choice`, `Quot.sound` and 3,158 auxiliary axioms of the
`native_decide` checks (those of `lean6` and `lean6_special`, and `open_specials` in the composition); no `sorry`
anywhere. Everything in `CC6Full` uses only the three standard axioms (`Check.lean`, 47 theorems), and
`exists_pos_aeval_ne_zero` (`Sanity.lean`) shows that the statement is not vacuous.

`check.sh` (keyword scan of all four packages, builds, axioms) passed on a fresh build from git archives of the versions
of the release: this project at c29be82 (its Lean sources and `check.sh` are those of 3ca5293; later commits change only
documentation), `lean6` at d593063 and `lean6_special` at ef35952, with the certificates of `lean6` checked against its
`SHA256SUMS` and Mathlib from the cache. Keyword scan clean; `CC6Full` built in 78 s (cold file cache; 41 s warm) and
the composition in 1965 s (about 33 minutes; 34 minutes for the whole check; about 1,550 CPU-minutes) on 384 hardware
threads; `Check.lean` OK; `CC6Compose.main_theorem` depends on the three standard axioms and 3,158 auxiliary axioms of
`native_decide` (2,714 from `lean6`, 443 from `lean6_special`, 1 from the composition), nothing else. The wall time is
set by `lean6`'s checks `L6Check.F2.C3.K13`, `K19`, `K31` (about 31 minutes each, single-threaded). Peak memory 85 GiB
above the idle machine (up to 384 Lean processes at once), largest single process 14 GiB (`lean6_special`'s F4 run for
`S12`); disk about 14 GiB besides the 7.5 GiB of Mathlib. Two further fresh checks passed: this project at 3ca5293 with
`lean6` at 69a5dc7 (which adds modules for the kernel-only version), and the first one at bba3b68 with `lean6` at
d593063 (its axiom step, which failed on a bug of `check.sh` fixed in 3ca5293, passed when rerun in the same build).

## Proved in CC6Full (hypothesis-free)

**Part I** (any number of bodies; §§2.1–2.2): `exists_germ` (infinitely many central configurations give a germ with
`ℓ ≤ 0`), with `exists_slice_point`, `finitelyManyCC_of_finite`, `r2_fibre_finite`, `exists_curve` (Cor. 2.4),
`Curve.U_const` (Lemma 2.3(b), all masses), `Expansion_exists` (Lemma 2.5), `Curve.balancing` (Lemma 2.6),
`Curve.exists_singular_place_ell_nonpos` (Cor. 2.7), `germOfPlace`.

**Part II** (germs, any number of bodies; §§2.3–2.4, 4, 5): symmetries; the identities of §2.3; Lemma 2.10; (O1)–(O6);
E1–E6, C1–C4, Rule T; trees, node coordinates, Lemma 4.2 (existence), Lemma 4.3(b),(c); cells; identities as data
with proofs (base and secondary); initial forms; Lemma 5.1 (`Identity.single`); Lemma 5.2(a),(b) (`core`,
`Cell.core_b_int`).

**Sections 6, 7**: Lemmas 6.1–6.3, 6.9–6.11, 6.16–6.18, 7.1–7.6; Theorem 6.5 (`d89_excluded`); from the computations
at one mass point: Theorems 6.12 (`d98_poly`), 6.15 (`d93_poly`), 6.20 (`d88_poly`, `d94_poly`), 7.12
(`d64_poly`, `d64_poly_of_noZero`), 7.13 (`d66_poly`). Tools: `elim_integral_int`, `macaulay_transfer`,
`biMacaulay_transfer_poly`, `goodred`, `goodred_torus_opt`, `encard_complexZeros_le`.

**Section 8**: `main_of_germExclusion`, `germExclusion_of_classes`, `seven_excluded'`, `main_of_classesExcluded`.

## Bridges in Compose (from the certificate projects' theorems)

* `lean6_special`: `heavyFact`, `heavyFact3` (Lemma 6.13), `e4NoZero` (§7.2), `c4Cert` (Lemma 7.9), `d88Box`,
  `d94Box` (Lemma 6.19(c),(d)), `d88Int`, `d94Int` (Lemma 6.18 from Lemma 6.19(a), over any ordered value group),
  `d88Dim`, `d94Dim` (Lemma 6.19(b), from `count_S12`, `count_KC`: `Dims.lean`); `sevenCerts'_of`.
* `lean6`: `classes6_cover` (Proposition 3.1 for germs), `germ_cell_stored` (Proposition 4.5: a germ with `ℓ ≤ 0`
  lies in a stored cell), `diagExcluded_of_mem` (Proposition 5.3 for the classes without open cells),
  `open_specials` (the seven classes with open cells are the diagrams of Table 1, relabelled), `hcells`.
* `main_of_dims : D88Dim → D94Dim → MainTheorem` (`Final.lean`) and `main_theorem` (`Theorem.lean`).

## Departures from the paper's proofs

Listed with explanations in `README.md`; in short, with the result of the paper whose proof is replaced:
* Theorems 6.12, 6.15, 6.20: integral elimination at one mass point (`elim_integral_int`) instead of resultants,
  constructible sets and the implicit function theorem.
* Propositions 7.8, 7.11: the Macaulay transfer (`macaulay_transfer`, `biMacaulay_transfer_poly`) instead of the
  closedness of projections along projective space.
* Lemma 7.7: replaced by the check at `(3, 5, 7, 11)` (no common nonzero zero of the forms) and the Nullstellensatz
  (`d64_poly_of_noZero`).
* Lemma 6.18: valuation rings with any ordered value group instead of discrete valuation rings; tropical certificates
  in torus form.
* Section 2: the identities and rules are proved for germs (Hahn series); Part I produces the germ from a place.
* Lemma 6.17: `X_l ≠ 0` stated as a separate hypothesis (in Lean `‖0‖ ^ (−1/2) = 0`).

## Open

Nothing for Theorem 1.1 in this version. Next: the kernel-only version (checks by `decide +kernel` instead of
`native_decide` in the certificate projects, and in `open_specials`).

## Kernel-only version

* `OpenKernel.lean`: `open_specials_lit` (the seven open classes are diagrams of Table 1, by `decide +kernel` on the
  literal class list `classes6Lit`, about 4 s), `open_specials_of_eq` (the statement of `open_specials` from
  `L6F1.classes6 = classes6Lit`), `classes6_eq_of_parse`; all on the three standard axioms. The equation itself must
  come from the kernel version of F1 (evaluating the reading of `n6.json` in the kernel fails; `FULL_PLAN.md` §14).
* `V3/`: the string-free statements `F1Cover`, `FusedExclusion`, `OpenCheck` (`Interface.lean`); `main_of_v3`,
  Theorem 1.1 from them and `SevenCerts'` on the three standard axioms (`Main.lean`); their instances from the native
  checks and `main_theorem_v3_native` (`Native.lean`; 3 standard and 3,158 auxiliary axioms, as `main_theorem`);
  `SpecialFacts` and `main_of_facts` (`Special.lean`): all consumed statements as hypotheses, standard axioms only.
* `V3/Kernel.lean`: `main_theorem_k_of (h : SpecialFacts) : MainTheorem` from the kernel checks (`F1_main_k`, `fusedK`,
  `OpenCheck` by `decide +kernel`); on the three standard axioms (elaborated against the modules of the kernel checks).
* `main_theorem_k_of3` (`V3/Kernel.lean`): everything from kernel versions except the two counts of Lemma 6.19(b) and
  the torus statement `n4_torus_gamma` of Lemma 6.19(a): Lemma 6.19(c), (d) (`Lean6.Special.D88.BoxesK`), the fact at
  `(3, 5, 7, 11)` (`Lean6.Special.K4.E4K`), Lemma 7.9 over `𝔽_32003` (`L6CheckC4.lemma_7_9_32003`), and of Lemma
  6.19(a) the coefficient checks (`Lean6.Special.Comp.D88.TropK.n4_units_ok`, `kc_units_ok`), the membership
  identities (`Lean6.Special.D88.TropK.n4_G_mem`, `kc_G_mem`) and the torus statement of `KC₁₂`
  (`Lean6.Special.D88.TropK.kc_torus_gamma`); standard axioms only (2026-10-18). `n4_torus_gamma` rests on the N4
  escape-ray system, whose certificate is pending.
* `main_theorem_v3_of1` (`V3/Release.lean`): the counts from `count_S12`, `count_KC`; axioms `propext`,
  `Classical.choice`, `Quot.sound` and the two auxiliary axioms of the F4 runs (`s12_f4_ok`, `kc_f4_ok`), the axiom
  line of version 3; one hypothesis left, `n4_torus_gamma`.
* `main_theorem_v3` (`V3/Release.lean`): Theorem 1.1, with the torus statement of `N4` from its kernel version
  `Lean6.Special.D88.TropK.n4_torus_gamma`; axioms `propext`, `Classical.choice`, `Quot.sound` and the two auxiliary
  axioms of the F4 runs behind `count_S12` and `count_KC`. `check_v3.sh` passed on 2026-10-18 (`README.md`).
* `tools/NativeInterface.lean`: the theorems of the certificate projects that depend on `native_decide` and that the
  proof of `main_theorem` uses directly (`FULL_PLAN.md` §14): in `lean6` `F1_main`, `f2s_cells_sound`, `lines_ok`,
  `open_ok` and 243 chunk theorems of F3/F4; in `lean6_special` 13 theorems.

## Files (lines, `sorry`, build time of the module in the fresh check of the release versions)

Total 27,997 lines (the libraries `CC6Full` and `CC6Compose`). `CC6Full` builds in 41–78 s wall on 384 hardware
threads (Mathlib from the cache); the composition takes about 33 minutes, almost all of it the checks of the
certificate projects.

| file | lines | sorry | build |
|---|---|---|---|
| `CC6Full/Algebra/Elim.lean` | 350 | 0 | 16.0s |
| `CC6Full/Algebra/GoodRed.lean` | 509 | 0 | 15.0s |
| `CC6Full/Algebra/GoodRedTorus.lean` | 205 | 0 | 1.4s |
| `CC6Full/Algebra/Macaulay.lean` | 434 | 0 | 15.0s |
| `CC6Full/Algebra/MacaulayBi.lean` | 745 | 0 | 2.6s |
| `CC6Full/Algebra/PointCount.lean` | 425 | 0 | 15.0s |
| `CC6Full/Classes.lean` | 325 | 0 | 1.6s |
| `CC6Full/Curve/ACurve.lean` | 75 | 0 | 15.0s |
| `CC6Full/Curve/Algebra.lean` | 295 | 0 | 16.0s |
| `CC6Full/Curve/Balancing.lean` | 168 | 0 | 1.8s |
| `CC6Full/Curve/ConstU.lean` | 287 | 0 | 2.1s |
| `CC6Full/Curve/CorU.lean` | 53 | 0 | 1.5s |
| `CC6Full/Curve/Fibre.lean` | 184 | 0 | 1.6s |
| `CC6Full/Curve/FunctionField/AlgRel.lean` | 292 | 0 | 1.8s |
| `CC6Full/Curve/FunctionField/Degree.lean` | 419 | 0 | 8.4s |
| `CC6Full/Curve/FunctionField/Dim.lean` | 92 | 0 | 1.7s |
| `CC6Full/Curve/FunctionField/Divisor.lean` | 254 | 0 | 3.8s |
| `CC6Full/Curve/FunctionField/Expansion.lean` | 413 | 0 | 2.3s |
| `CC6Full/Curve/FunctionField/Places.lean` | 255 | 0 | 5.2s |
| `CC6Full/Curve/FunctionField/Residue.lean` | 144 | 0 | 3.3s |
| `CC6Full/Curve/FunctionField/ValLemmas.lean` | 153 | 0 | 15.0s |
| `CC6Full/Curve/GermOfPlace.lean` | 413 | 0 | 2.1s |
| `CC6Full/Curve/Places6.lean` | 360 | 0 | 2.4s |
| `CC6Full/Curve/SlicePoint.lean` | 244 | 0 | 1.9s |
| `CC6Full/Curve/System.lean` | 214 | 0 | 1.5s |
| `CC6Full/Germ/Basic.lean` | 148 | 0 | 1.2s |
| `CC6Full/Germ/Cell.lean` | 1173 | 0 | 3.8s |
| `CC6Full/Germ/CellCoreB.lean` | 194 | 0 | 1.5s |
| `CC6Full/Germ/CellIds.lean` | 525 | 0 | 1.6s |
| `CC6Full/Germ/Diagram.lean` | 122 | 0 | 1.2s |
| `CC6Full/Germ/Identities.lean` | 330 | 0 | 1.6s |
| `CC6Full/Germ/Initial.lean` | 319 | 0 | 1.3s |
| `CC6Full/Germ/Orders.lean` | 394 | 0 | 1.6s |
| `CC6Full/Germ/Rules.lean` | 779 | 0 | 1.7s |
| `CC6Full/Germ/Symm.lean` | 371 | 0 | 1.6s |
| `CC6Full/Germ/Tree.lean` | 757 | 0 | 1.7s |
| `CC6Full/Germ/TreeExists.lean` | 260 | 0 | 1.2s |
| `CC6Full/Interface.lean` | 81 | 0 | 1.4s |
| `CC6Full/Main.lean` | 47 | 0 | 1.4s |
| `CC6Full/Sanity.lean` | 30 | 0 | 1.1s |
| `CC6Full/Six/Common.lean` | 402 | 0 | 1.5s |
| `CC6Full/Six/D64.lean` | 385 | 0 | 1.9s |
| `CC6Full/Six/D64NoZero.lean` | 297 | 0 | 1.6s |
| `CC6Full/Six/D64Poly.lean` | 226 | 0 | 2.0s |
| `CC6Full/Six/D64PolyForms.lean` | 201 | 0 | 2.1s |
| `CC6Full/Six/D66.lean` | 264 | 0 | 1.3s |
| `CC6Full/Six/D66Poly.lean` | 503 | 0 | 1.9s |
| `CC6Full/Six/D88.lean` | 442 | 0 | 2.4s |
| `CC6Full/Six/D88Gen.lean` | 343 | 0 | 1.0s |
| `CC6Full/Six/D88Lead.lean` | 837 | 0 | 1.8s |
| `CC6Full/Six/D88Sys.lean` | 382 | 0 | 5.8s |
| `CC6Full/Six/D89.lean` | 483 | 0 | 2.7s |
| `CC6Full/Six/D93.lean` | 242 | 0 | 1.7s |
| `CC6Full/Six/D93Lead.lean` | 236 | 0 | 1.3s |
| `CC6Full/Six/D94.lean` | 477 | 0 | 2.4s |
| `CC6Full/Six/D94Sys.lean` | 308 | 0 | 1.0s |
| `CC6Full/Six/D98.lean` | 314 | 0 | 2.0s |
| `CC6Full/Six/D98Elim.lean` | 204 | 0 | 2.2s |
| `CC6Full/Six/D98Lead.lean` | 454 | 0 | 1.5s |
| `CC6Full/Six/E4.lean` | 462 | 0 | 2.0s |
| `CC6Full/Six/K4Aux.lean` | 470 | 0 | 1.4s |
| `CC6Full/Six/Systems.lean` | 57 | 0 | 14.0s |
| `CC6Full/Six/Three.lean` | 375 | 0 | 2.0s |
| `CC6Full/Six/ThreeDefs.lean` | 440 | 0 | 2.2s |
| `CC6Full/Statement.lean` | 66 | 0 | 14.0s |
| `Compose/CC6Compose/Boxes.lean` | 159 | 0 | 6.1s |
| `Compose/CC6Compose/C4.lean` | 190 | 0 | 11.0s |
| `Compose/CC6Compose/Cells.lean` | 66 | 0 | 2.9s |
| `Compose/CC6Compose/CellsConv.lean` | 1080 | 0 | 4.6s |
| `Compose/CC6Compose/Dims.lean` | 335 | 0 | 6.4s |
| `Compose/CC6Compose/E4.lean` | 131 | 0 | 13.0s |
| `Compose/CC6Compose/Enum.lean` | 587 | 0 | 32.0s |
| `Compose/CC6Compose/Exclusion.lean` | 174 | 0 | 3.3s |
| `Compose/CC6Compose/ExclusionClaim.lean` | 295 | 0 | 3.5s |
| `Compose/CC6Compose/ExclusionClasses.lean` | 912 | 0 | 5.2s |
| `Compose/CC6Compose/ExclusionCore.lean` | 396 | 0 | 3.5s |
| `Compose/CC6Compose/ExclusionImports.lean` | 16 | 0 | 3.0s |
| `Compose/CC6Compose/ExclusionPoly.lean` | 158 | 0 | 3.4s |
| `Compose/CC6Compose/ExclusionTerms.lean` | 458 | 0 | 4.0s |
| `Compose/CC6Compose/Final.lean` | 37 | 0 | 3.2s |
| `Compose/CC6Compose/Heavy.lean` | 81 | 0 | 3.4s |
| `Compose/CC6Compose/Integrality.lean` | 1106 | 0 | 7.6s |
| `Compose/CC6Compose/Seven.lean` | 24 | 0 | 2.8s |
| `Compose/CC6Compose/Special.lean` | 62 | 0 | 2.9s |
| `Compose/CC6Compose/Theorem.lean` | 22 | 0 | 3.1s |
