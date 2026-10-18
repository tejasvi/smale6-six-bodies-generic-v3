# CC6Full: a Lean 4 proof of generic finiteness of planar central configurations of six bodies

This project proves in Lean 4 with Mathlib Theorem 1.1 (`thm:main`) of the paper *Smale's sixth problem for six bodies
in the plane: finiteness of central configurations for generic masses*:

> There is a nonzero polynomial `F ∈ ℤ[m₁, …, m₆]` such that for every `m ∈ (ℝ_{>0})⁶` with `F(m) ≠ 0` the planar
> six-body problem with masses `m` has finitely many central configurations up to similarity.

The statement is `CC6Full.MainTheorem` (`CC6Full/Statement.lean`). The proof composes the theory proved here with the
checks of the paper's computations in two sibling projects: `lean6` (Sections 3–5: the diagrams, the cells, the
single-term exclusions and the cores) and `lean6_special` (Sections 6–7).

**Version 3** (this version) checks every computation of the paper in the kernel except the two dimension bounds of
Lemma 6.19(b). Its theorem is `CC6Compose.V3.main_theorem_v3 : CC6Full.MainTheorem`
(`Compose/CC6Compose/V3/Release.lean`); `#print axioms` gives `propext`, `Classical.choice`, `Quot.sound` and the two
auxiliary axioms of the F4 runs behind `count_S12` and `count_KC`
(`Lean6.Special.Comp.Count.s12_f4_ok._native.native_decide.ax_1_1`, `….kc_f4_ok._native.native_decide.ax_1_1`), nothing
else (`check_v3.sh`). No statement or proof of the kernel route of the composition involves reading text: the class
list, the certificates, the sets `G` and the cofactors of Lemma 6.19(a) are Lean literals (generated from the data files
and checked against hash lists), and the open classes are checked by `decide +kernel` (`OpenCore.lean`).

**Version 2**, the previous release, proved `CC6Compose.main_theorem : CC6Full.MainTheorem`
(`Compose/CC6Compose/Theorem.lean`, still part of the composition) with the axioms `propext`, `Classical.choice`,
`Quot.sound` and 3,158 auxiliary axioms of `native_decide` (with `lean6` at `d593063` and `lean6_special` at
`ef35952`), which assert the results of the checks run as compiled code (in the two certificate projects, and
`open_specials` in the composition). Neither version uses `sorry`; the theory in `CC6Full` uses only the three
standard axioms (`Check.lean`).

## The statement in Lean

`CC6Full/Statement.lean`, verbatim (namespace `CC6Full`, `open Finset`):

```lean
/-- A planar configuration of `n` bodies. -/
abbrev Conf (n : ℕ) := Fin n → ℂ

/-- The bodies are at distinct points. -/
def CollisionFree {n : ℕ} (q : Conf n) : Prop := ∀ i j, i ≠ j → q i ≠ q j

/-- Equation (1.1) (`eq:cc`): `q` is a central configuration for the masses `m`. -/
def IsCC {n : ℕ} (m : Fin n → ℝ) (q : Conf n) : Prop :=
  CollisionFree q ∧ ∃ (lam : ℝ) (c : ℂ), ∀ i,
    ((lam * m i : ℝ) : ℂ) * (q i - c) =
      ∑ j ∈ univ.erase i, ((m i * m j / ‖q i - q j‖ ^ 3 : ℝ) : ℂ) * (q i - q j)

/-- `q'` is the image of `q` under a similarity `z ↦ a z + b` (`a ≠ 0`) of the plane, possibly composed with the
reflection `z ↦ z̄`. -/
def Similar {n : ℕ} (q q' : Conf n) : Prop :=
  ∃ a b : ℂ, a ≠ 0 ∧ ((∀ i, q' i = a * q i + b) ∨ (∀ i, q' i = a * starRingEnd ℂ (q i) + b))

/-- The planar `n`-body problem with masses `m` has finitely many central configurations up to similarity: finitely
many central configurations represent all of them up to similarity. -/
def FinitelyManyCC {n : ℕ} (m : Fin n → ℝ) : Prop :=
  ∃ F : Finset (Conf n), ∀ q, IsCC m q → ∃ q' ∈ F, Similar q' q

/-- Generic finiteness for `n` bodies: some nonzero `F ∈ ℤ[m₁, …, mₙ]` such that the planar `n`-body problem has
finitely many central configurations up to similarity for every positive mass vector `m` with `F(m) ≠ 0`. -/
def GenericFiniteness (n : ℕ) : Prop :=
  ∃ F : MvPolynomial (Fin n) ℤ, F ≠ 0 ∧
    ∀ m : Fin n → ℝ, (∀ i, 0 < m i) → MvPolynomial.aeval m F ≠ 0 → FinitelyManyCC m

/-- **Theorem 1.1** (`thm:main`): generic finiteness for six bodies in the plane. -/
def MainTheorem : Prop := GenericFiniteness 6
```

How this matches Theorem 1.1:
* The plane is `ℂ`, and body `k` of the paper is `k − 1 : Fin n`. `IsCC m q` is equation (1.1): the points are
  distinct (`CollisionFree`), and for some `λ ∈ ℝ` (`lam`) and `c` in the plane,
  `λ m_i (q_i − c) = Σ_{j ≠ i} m_i m_j (q_i − q_j) / |q_i − q_j|³` for every `i`. The sum over `univ.erase i` is
  the sum over `j ≠ i`, `‖q i - q j‖` is the Euclidean distance, and the real coefficients are cast to `ℂ`.
* `Similar q q'` says that `q'` is the image of `q` under a similarity of the plane, `z ↦ a z + b` with `a ≠ 0`,
  possibly composed with the reflection `z ↦ z̄`. Either reading of "up to similarity" gives the same theorem: a
  finite set that represents all central configurations up to similarities with reflections, together with the
  complex conjugates of its elements, represents them up to orientation-preserving similarities, since the conjugate
  of a central configuration is one; the converse is immediate.
* `FinitelyManyCC m`: a finite set of configurations represents every central configuration up to similarity. As
  `Similar` is the orbit relation of a group acting on configurations, this says that the central configurations
  fall into finitely many similarity classes.
* `GenericFiniteness n`: a nonzero `F ∈ ℤ[m₁, …, mₙ]` (`MvPolynomial (Fin n) ℤ`, the variable `X (k − 1)` standing
  for `m_k`) such that `FinitelyManyCC m` holds for every `m ∈ (ℝ_{>0})ⁿ` with `F(m) ≠ 0` (`MvPolynomial.aeval m F`
  is the value `F(m) ∈ ℝ`). `MainTheorem` is the case `n = 6`, which is Theorem 1.1.

The statement is not vacuous (`CC6Full/Sanity.lean`, in `Check.lean`): a nonzero `F` does not vanish at some positive
mass vector, so the masses covered by `GenericFiniteness n` form a nonempty subset of `(ℝ_{>0})ⁿ` (and, since `F` is a
nonzero polynomial, a dense open one; the lemma proves nonemptiness).

```lean
theorem exists_pos_aeval_ne_zero {n : ℕ} {F : MvPolynomial (Fin n) ℤ} (hF : F ≠ 0) :
    ∃ m : Fin n → ℝ, (∀ i, 0 < m i) ∧ aeval m F ≠ 0
```

## Axioms and what they trust

`#print axioms CC6Compose.main_theorem` (`Compose/Check.lean`) lists `propext`, `Classical.choice`, `Quot.sound` and
3,158 auxiliary axioms of `native_decide`: 2,714 from `lean6` (1,928 cofactor certificates of the cores, 660 checks of
the cell search F2S, 125 of F34S, one of F1), 443 from `lean6_special` and one from the composition (`open_specials`).
`native_decide` evaluates the Boolean decision procedure of a proposition `P` with compiled code and, if the result is
`true`, adds an axiom `decide P = true`, from which the kernel derives `P`. For example, the F4 run behind `count_S12`:

```lean
axiom Lean6.Special.Comp.Count.s12_f4_ok._native.native_decide.ax_1_1 : decide
    (Lean6.Special.Comp.Count.dimCheck 65521 11
        (Lean6.Special.Comp.Count.f4Basis Lean6.Special.Comp.Count.s12Cfg Lean6.Special.Comp.Count.s12Inputs) 20316 =
      true) =
  true
```

The kernel does not check these evaluations. The auxiliary axioms therefore trust the Lean compiler (here also the C
compiler that builds the precompiled libraries of the certificate projects, whose code the checks run), the Lean
runtime, and the implementations of core functions marked `@[extern]` or `@[implemented_by]`, such as
arbitrary-precision arithmetic. The keyword scan of `check.sh` ensures that the four packages declare no axioms and no
such implementations of their own, and that `CC6Full` does not use `native_decide`. Everything else, Mathlib and the
theory here included, is checked by the kernel. The 47 theorems of `Check.lean` (the main results of `CC6Full`, the
non-vacuity lemma among them) depend only on `propext`, `Classical.choice` and `Quot.sound`.

**Version 3.** `#print axioms CC6Compose.V3.main_theorem_v3` (`Compose/CheckV3.lean`) lists `propext`,
`Classical.choice`, `Quot.sound` and two auxiliary axioms of `native_decide`, those of the F4 runs behind `count_S12`
and `count_KC` (Lemma 6.19(b)): `Lean6.Special.Comp.Count.s12_f4_ok._native.native_decide.ax_1_1` (above) and
`Lean6.Special.Comp.Count.kc_f4_ok._native.native_decide.ax_1_1`, which asserts
`dimCheck 65521 11 (f4Basis kcCfg kcInputs) 4788 = true` (`lean6_special`,
`Lean6/Special/Comp/D88/Count/RunS12.lean`, `RunKC.lean`). They trust what the auxiliary axioms of version 2 trust,
for these two runs only. Every other check is a theorem whose proof the kernel checks by evaluating it
(`decide +kernel`): in `lean6` F1, the 1,928 cofactor certificates of the cores and the fused run of F2–F4; in
`lean6_special` Lemma 6.19(a), (c), (d), the fact at `(3, 5, 7, 11)` and Lemma 7.9 over `𝔽_32003`; and the open
classes of Table 1 (`OpenCore.lean`). The kernel's own arithmetic on natural-number literals is part of the kernel.
The keyword scan of `check_v3.sh` ensures in addition that the modules of the kernel route of the composition do not
use `native_decide`.

## Where the Lean proof departs from the paper's proofs

Each item names the result of the paper whose proof is replaced (numbering of the paper's current version).

* **Theorems 6.12, 6.15 and 6.20 (diagrams 98, 93, 88 and 94): integral elimination at one mass point instead of
  resultants, constructible sets and the implicit function theorem.** `CC6Full.elim_integral_int`
  (`CC6Full/Algebra/Elim.lean`): if the unknowns of a polynomial system over `ℚ[μ]` are integral over `ℚ[μ][1/g]`
  modulo the system and the system has no complex solution at a rational point `μ₀` with `g(μ₀) ≠ 0`, then some
  `h ∈ ℚ[μ]` with `h(μ₀) ≠ 0` vanishes wherever there is a solution and `g ≠ 0`. For diagrams 98 and 93 the
  integrality comes from the roots of `S_μ` and the square roots `c_jl`, so the polynomial `Φ` over the sign matrices
  and the resultants are not used. For diagrams 88 and 94 it comes from Lemma 6.18, and the empty fibre at
  `μ₀ = (1, 2, 3, 30)` replaces the implicit function theorem, the continuity of the tests and the density of real
  points.
* **Propositions 7.8 and 7.11 (the systems `E₄` and `C₄`): a Macaulay transfer instead of the closedness of
  projections along projective space.** `macaulay_transfer`, `biMacaulay_transfer_poly`: if at `μ₀` every monomial of
  some degree (or bidegree) lies in the ideal of the forms, then a maximal minor `h(μ)` of the Macaulay matrix is
  nonzero, and wherever `h ≠ 0` every monomial of that degree lies in the ideal, so the forms have no common
  projective zero. `h` is never computed. What is proved is that there is no solution where `h ≠ 0`, not that `B_E`
  and `B_C` are closed.
* **Lemma 7.7 (`E₄` at equal masses): the mass point `(3, 5, 7, 11)` instead.** The certificate project proves that
  the forms `ℱ_ε`, `𝒢_σ` have no common nonzero zero at `(3, 5, 7, 11)` (the second check that the paper reports after
  Proposition 7.8). The Nullstellensatz then gives the monomials for the Macaulay transfer (`d64_poly_of_noZero`).
  The hand proof at `(1, 1, 1, 1)` and its resultants are not formalized.
* **Lemma 6.18 (good reduction): valuation rings instead of discrete valuation rings.** Mathlib provides valuation
  subrings dominating a local ring (`LocalSubring.exists_le_valuationSubring`), not discrete valuation rings dominating
  Noetherian local domains. So the value group is an arbitrary ordered abelian group. `goodred` and
  `goodred_torus_opt` use the tropical certificates in torus form: the initial forms have no common zero in the torus
  over any field of characteristic `p`, which the certificate project proves for every ordered value group.
* **Lemma 6.19(b) (the dimension bounds): Gröbner bases computed in Lean, and a change of unknowns.** The paper
  computes the Gröbner bases modulo `p = 65521` with msolve. The certificate project computes them in Lean, with an F4
  implementation run as compiled code, and proves that every element lies in the ideal (`count_S12`, `count_KC`).
  Our rows of `S12` (the equations of §6.7 with the denominator `μ₄` cleared) are its rows times units (`1` or
  `μ₄² = 900` at `μ₀`), and its system `KC′` has the eleven unknowns `X₂, X₃, U_k = Y_k − Y₄, p_kl` instead of the
  twelve of `KC₁₂`. `Compose/CC6Compose/Dims.lean` shows that our quotients are quotients of its quotients (for `KC`
  through `U_k ↦ Y_k − Y₄`, with `Y₄` the image of the expression eliminated by the `Y`-equation of body `1`), so the
  bounds carry over (`d88Dim`, `d94Dim`).
* **Section 2: germs.** The identities of §2.3, Lemma 2.10, (O1)–(O6) and the rules of Lemma 2.11 are proved for
  germs (`CC6Full.Germ`: Hahn series `z`, `w` satisfying the body and distance equations, with `U = E ≠ 0`). Part I
  produces a germ with `ℓ ≤ 0` from a singular place of a curve of central configurations (`exists_germ`), whereas the
  paper works with the expansions at the place.
* **Lemma 7.9: one prime.** The paper states the unit ideals on the 14 charts over `𝔽_32003` and over
  `𝔽_1073741789`; Lemma 7.10 needs one prime, and the formal proof uses the statement over `𝔽_32003` only
  (`c4Cert_of`). The computation over `𝔽_1073741789` is the paper's independent check and is not used.
* **Version 3: literal data instead of the data files.** The kernel route states its inputs over Lean literals: the
  191 class representatives (`L6CheckK.F1.classes6L`), the certificates of the cores (`L6CheckF.csAll`), the sets
  `G` and the cofactors of Lemma 6.19(a) (`GN4`, `GKC`, `cofN4`, `c0N4`, `cofKC`, `c0KC`). Checks run as compiled
  code relate them to the data files (`…_eq_parse`, the links of the certificate texts); the kernel route does not use
  those checks.
* **Version 3: Propositions 4.5 and 5.3 as one statement.** `FusedExclusion` (`V3/Interface.lean`): for each class
  a finite list of certificates such that every pair of exponent trees with heights satisfying the conditions of
  Lemma 4.3 lies in a class with open cells or carries a claim with a certificate from the list. The stored cells
  of Proposition 4.5 are internal to the kernel check (`L6CheckF.fusedK`).
* **Stated separately.** The test of Lemma 6.17 uses `|X_l|^{−1/2}`. In Lean `‖0‖ ^ (−1/2) = 0`, so `X_l ≠ 0` is a
  separate hypothesis, which the certificate project checks at the zeros of Lemma 6.19(c), (d).

## The computations

| result of the paper | checked in | bridge (`Compose/CC6Compose/`) | version 3: kernel version used |
|---|---|---|---|
| Proposition 3.1 (the diagrams) | `lean6`, F1 | `classes6_cover` (`Enum.lean`) | `L6CheckK.F1.F1_main_k` |
| Proposition 4.5 (the cells) | `lean6`, F2S (a search proved complete) | `germ_cell_stored` (`Cells.lean`) | `L6CheckF.fusedK` (with 5.3) |
| Proposition 5.3 (exclusions, cores) | `lean6`, F34S and the 1,928 cofactor certificates | `diagExcluded_of_mem` (`Exclusion.lean`) | `L6CheckF.fusedK` |
| Table 1 (the seven classes with open cells) | `lean6`, and `native_decide` in the composition | `open_specials` (`Final.lean`) | `OpenCheck` by `decide +kernel` |
| Lemma 6.13 | `lean6_special` | `heavyFact`, `heavyFact3` (`Heavy.lean`) | the same (no computation) |
| Lemma 6.19(a), with Lemma 6.18 | `lean6_special` (tropical certificates) | `d88Int`, `d94Int` (`Integrality.lean`) | `TropK.n4_units_ok`, `kc_units_ok`, `n4_G_mem`, `kc_G_mem`, `n4_torus_gamma`, `kc_torus_gamma` |
| Lemma 6.19(b) | `lean6_special` (`count_S12`, `count_KC`: Gröbner bases computed in Lean by F4) | `d88Dim`, `d94Dim` (`Dims.lean`) | none: `count_S12`, `count_KC` (`native_decide`) |
| Lemma 6.19(c), (d) | `lean6_special` (boxes) | `d88Box`, `d94Box` (`Boxes.lean`) | `BoxesK.lemma_6_19_c`, `lemma_6_19_d` |
| §7.2: `E₄` at `(3, 5, 7, 11)` | `lean6_special` | `e4NoZero` (`E4.lean`) | `E4K.check_3_5_7_11` |
| Lemma 7.9 | `lean6_special` | `c4Cert` (`C4.lean`) | `L6CheckC4.lemma_7_9_32003` (over `𝔽_32003`) |

The kernel versions of version 3 are assembled in `V3/Kernel.lean` and `V3/Release.lean` (`TropK` is
`Lean6.Special.Comp.D88.TropK` for the coefficient checks and `Lean6.Special.D88.TropK` otherwise, `BoxesK` is
`Lean6.Special.D88.BoxesK`, `E4K` is `Lean6.Special.K4.E4K`). Those of `lean6_special` have the statements of the
theorems they replace (`lemma_7_9_32003` that of the first half of `lemma_7_9`); `F1_main_k`, `fusedK` and the check of
the open classes give the string-free statements `F1Cover`, `FusedExclusion` and `OpenCheck` (`V3/Interface.lean`). All
of them depend on the three standard axioms only.

## Layout

* `CC6Full/Statement.lean`: the statement (`IsCC`, `Similar`, `FinitelyManyCC`, `GenericFiniteness n`,
  `MainTheorem := GenericFiniteness 6`); `CC6Full/Sanity.lean`: the statement is not vacuous.
* `CC6Full/Curve/`: Part I, for any number of bodies: the variety of normalized central configurations, slice points,
  Corollary 2.4, function fields of curves, places, expansions, balancing, `U` constant on curves, and
  `exists_germ`: infinitely many central configurations give a germ (the rotated expansions at a singular place) with
  `ℓ(x) ≤ 0`.
* `CC6Full/Germ/`: Part II, for germs and any number of bodies: the identities of §2.3, Lemma 2.10, (O1)–(O6), the
  rules of Lemma 2.11, trees and cells (Lemmas 4.2, 4.3), identities as data, initial forms, Lemmas 5.1 and 5.2.
* `CC6Full/Six/`: Sections 6 and 7 for six bodies: the leading systems, Lemmas 6.1–6.3, 6.9–6.11, 6.16–6.18, 7.1–7.6,
  Theorem 6.5, and Theorems 6.12, 6.15, 6.20, 7.12, 7.13 from the computations at one mass point.
* `CC6Full/Algebra/`: the integral elimination lemma, the Macaulay transfers, Lemma 6.18 with exact certificates over
  an arbitrary ordered value group, and the point count from a finite module.
* `CC6Full/Main.lean`, `Classes.lean`, `Interface.lean`: Section 8, the reduction to the classes of diagrams.
* `Compose/`: a separate Lake package that requires this project, `lean6` and `lean6_special` (as path dependencies
  `..`, `../../sections6-9`, `../../sections3-5` in this supplement), proves the bridges between their checked statements and the theory
  here, and the main theorems. Version 3: the string-free statements over literal data (`V3/Interface.lean`, with the
  modules `EnumCore`, `CellsCore`, `ClaimCore`, `SpecialCore`, `OpenCore`, `ClassesLit`), Theorem 1.1 from them
  (`V3/Main.lean`, `V3/Special.lean`), and the kernel versions assembled (`V3/Kernel.lean`, `V3/Release.lean`, which
  import the modules compiled outside Lake and are compiled by `check_v3.sh`).
* `check.sh`, `check_v3.sh`: the checks of versions 2 and 3 (below).
* `FULL_PLAN.md`: the plan and its updates; `PROGRESS.md`: the record of what is proved.

## Building and checking

Toolchain `leanprover/lean4:v4.35.0-rc3` and Mathlib `c55e6e7` (`lean-toolchain`, `lake-manifest.json`), the same in
all four packages. For both versions:
1. In this supplement `lean6` is `../sections3-5` and `lean6_special` is `../sections6-9` (`Compose/` requires them as
   `../../sections3-5` and `../../sections6-9`). `bash scripts/fetch_data.sh` in `../sections3-5` puts the certificate
   files into its `data/f4/certs` and checks them (`scripts/poly/verify_certs.sh`); unpack them with
   `bash scripts/poly/unpack_certs.sh` there.
2. Run `lake exe cache get` here, then make the packages of `.lake/packages` available in `Compose/.lake/packages`
   (the checks below used symbolic links), or run `lake exe cache get` in `Compose/` as well.

### Version 3

Versions: `lean6` at `17f8b22` and `lean6_special` at `3bb1297`, with this project at its final commit.

The kernel checks of `lean6_special` also read 16 input files, distributed separately and listed with the SHA-256 sums
of their uncompressed contents in `lean6_special/data/kern/SHA256SUMS`; they go into `lean6_special/data/kern/cert`:
`c4_3_5_7_11_<chart>.cert.xz` (Lemma 7.9 on the fourteen charts), `esc_kc_0.cert.xz` (the escape-ray system of
`KC`) and `trace_hypN4.txt.xz` (a Buchberger trace of the escape-ray system of `N4`, which the kernel checks as a chain
of identities).

`./check.sh v3` (it runs `check_v3.sh`):
* scans the sources for forbidden keywords, `native_decide` included in the modules of the kernel route of the
  composition (`lean6`'s tools that write data and measurements use `unsafe` and `implemented_by`: the scan skips
  them and fails if a module imports them), and again after the next step for the generated modules;
* builds the kernel checks of `lean6` and of `lean6_special` with their drivers `scripts/kern/build.sh`, which compile
  the check modules with `lean` directly into the project's `out/` under a memory budget, compare the generated files
  with the project's SHA-256 lists and print the axioms of the final theorems;
* builds `CC6Full` and the composition and prints the axioms of the 47 theorems of `Check.lean`, which must be among
  `propext`, `Classical.choice` and `Quot.sound`;
* compiles `Compose/CC6Compose/V3/Kernel.lean` and `Release.lean` against the kernel checks and prints the axioms of
  `CC6Compose.V3.main_theorem_v3`, which must be exactly the five above.

It ends with `check_v3.sh: OK`. Environment: `JOBS` (Lean processes run by Lake at once, default 40), `BUDGET_GB`
(the drivers' memory budget, default 600 GB), `L6_STAGES`, `SP_STAGES` (the drivers' stages; set to the empty string,
the project's `out/` is used as built before).

Check of 2026-10-18, of this project at `027dfd1` (later commits change only documentation), with `lean6` at `17f8b22`
and `lean6_special` at `3bb1297` from git archives, the input files checked against their SHA-256 lists and Mathlib from
the cache (times UTC; machines with 384 hardware threads and 708 GiB of memory; all numbers are those of this check
unless marked otherwise):
* The kernel stages of `lean6`, from a git archive of `17f8b22`, 06:27–12:44 (6 h 18 min). On one machine: the libraries
  (4 min), F1 (22 min; 327 modules, 25.4 CPU-hours), the generator of F4 (2 min), F4 (25 min; 830 modules, 23.3
  CPU-hours), the export and the generator of F2–F4 (12 min). The fused check of F2–F4 (31,324 modules) ran on that
  machine from 07:32; at 10:43 its remaining modules were split over that machine and two more (the driver's
  multi-machine mode, by class and export run; the parts took 78 minutes on each added machine and 110 minutes on the
  first), and `build.sh f34k` completed it on the first machine at 12:42–12:44, after the parts' outputs were gathered:
  894 CPU-hours of module time. All stages of `lean6` took about 963 CPU-hours (the time totals of the stage runs and
  the per-module records of the schedulers, including about 2 CPU-hours of jobs that finished outside a scheduler when
  the run was split). Largest single process: 26.7 GiB (`L6CheckF.Final`).
* Before they were used, a script checked `lean6`'s sources against `17f8b22` (4,920 files, against a manifest written
  from `git archive`), the certificates against `data/f4/certs/SHA256SUMS`, the generated files against the committed
  hash lists (4,687 and 31,880 files, the exported data of 184 classes), and `out/` (33,641 files) against the SHA-256
  sums recorded when the last stage ended.
* The kernel stages of `lean6_special`, from a git archive of `3bb1297`, on the first machine, 11:36–13:57 (2 h 21 min,
  45.0 CPU-hours with the libraries), at a memory budget of 300 GB, since the machine also ran `lean6`'s fused check
  until 12:44: libraries 13 min, boxes 11 min, D98 6 s, E4 14 min, C4 73 min and Trop 28 min (each with its generator),
  TropMem 2 min. Largest single process 40.7 GiB (`L6CheckTrop.N4.Cover`), largest module of C4 33.1 GiB. Memory in use
  on the machine, sampled every 10 s: peak 376.6 GiB at 11:50 (with `lean6`'s fused check running), 245.9 GiB after
  12:45.
* `L6_STAGES= SP_STAGES= JOBS=40 ./check.sh v3`, on the first machine with the kernel checks of both projects as built
  above, 13:57–14:13: 15 min 33 s, 8.1 CPU-hours (`CC6Full` and the composition built in 890 s), peak memory in use 31.2
  GiB. It ended with `check_v3.sh: OK`.
* For reference (other runs, not this check): earlier runs of identical sources of `lean6_special`'s kernel stages on
  one machine at the default budget took about 40 CPU-hours and 85 minutes, summed over the stages after the libraries,
  with a peak of 464 GB in use during C4.

### Version 2

Versions: `lean6` at `d593063` and `lean6_special` at `ef35952`. `./check.sh` without argument is the check of
version 2 and expects these versions.

What a rebuild needs (measured in the check below, on a machine with 384 hardware threads and 708 GiB of memory):
* Mathlib from the cache (`lake exe cache get`): 7.5 GiB in `.lake/packages`.
* The certificate files of `lean6`: 1,928 files, 1.2 GiB, distributed separately and listed with their SHA-256 sums in
  `lean6/data/f4/certs/SHA256SUMS`. Their plain-text copies, which the certificate modules read with `include_str`,
  take another 3.2 GiB.
* Disk for the build outputs: 7.9 GiB for `lean6`, 0.54 GiB for `lean6_special`, 0.32 GiB for this project. With the
  sources and the certificates, about 14 GiB besides Mathlib.
* Memory: Lake runs one Lean process per hardware thread (up to 384 here). The peak was 85 GiB above the idle machine,
  sampled every 5 s. The largest single process, the F4 run of `lean6_special`
  (`Lean6/Special/Comp/D88/Count/RunS12.lean`), reached 14 GiB. On a machine with fewer threads fewer processes run at
  once, but that module alone needs about 14 GiB.
* Time: `CC6Full` builds in 41–78 s (78 s with a cold file cache), the composition in about 33 minutes (1,953–1,965 s).
  In total the build took about 1,550 CPU-minutes. The slowest modules, `lean6`'s checks `L6Check.F2.C3.K13`, `K19`
  and `K31`, take about 31 minutes each on one thread and set the wall time. With `k` threads the composition needs at
  least the larger of 31 minutes and about 1,550/`k` minutes. (The checks `L6Check.F2.*` of the first cell search are
  built because `L6Check.F2S.All` imports them; the main theorem does not depend on their axioms.)

After steps 1 and 2 above, `./check.sh` scans the sources of all four packages for forbidden keywords, builds
`CC6Full` and the composition, and prints the axioms. Those of the 47 theorems of `Check.lean` must be among
`propext`, `Classical.choice` and `Quot.sound`, and those of `CC6Compose.main_theorem` among these three and the
auxiliary axioms of `native_decide`. It ends with `check.sh: OK`.

Check of 2026-10-17: `check.sh` passed (exit status 0, 34 minutes) on a fresh build from git archives of this project
at `c29be82` (later commits change only documentation), `lean6` at `d593063` and `lean6_special` at `ef35952`, with the
certificates checked against `SHA256SUMS` and Mathlib from the cache. It also passed with `lean6` at `69a5dc7`, which
adds modules for a kernel-only version.
