# Referee report: hand mechanisms for the 91,273 nonpositive cells (MECHANISMS.md, RESIDUAL.md)

Independent referee pass, 2026-10-17 (PDT). Objects refereed: `hand_explanations/refereed/MECHANISMS.md`
(last modified 2026-10-17 03:01 UTC) and `hand_explanations/refereed/RESIDUAL.md` (08:48 UTC). Neither file
changed during the review. Nothing outside `hand_explanations/independent` was written. All my code is in
`scripts/` and `sing/`, all outputs are `scripts/*.out`, `scripts/*.jsonl` and `sing/*.out`, and every number below
comes from one of these files (§8). I read the authors' scripts only to learn the data format and, after my own
implementation was finished, to explain one difference (W3, §3.3).

## 0. Verdict in brief

1. **Lemmas.** Every lemma that the coverage uses is correct. I re-derived each proof and redid each elimination
   in Singular with `LIB "elim.lib"; ideal S = sat(I,J);` in characteristic 0. No lemma is wrong. Some statements
   need small precision fixes (§6): a sign typo in Lemma B, an unstated `X ≠ ∅` in Lemma C, an unstated "O lies
   below v" in Lemma L, and an imprecise case (β) in Lemma R1\*. Two variants are correct but never needed: E1
   with U_T, and R1 with one balance plus U_T. R5 and B are also never needed.
2. **Coverage.** I wrote my own checkers from the statements and ran them on all 91,273 stored cells.
   - They agree with the authors' flags **cell by cell** for T, P, C, B, E1, R1, R5, R6 and Q.
   - They also agree, globally, for B0, K, L, R1\*(α/β) and EQ2.
   - W3 agrees on the 15 cells where it is used. My W3 flag is more permissive elsewhere, which is harmless (§3.3).
   - On my own cell polyhedra, built from Definition 4.3 of the paper, an LP check confirms the conclusions of T, P,
     C and B on every cell where they apply, with 0 failures.
   - I re-certified exactly (Lemma 4.4 of the paper, rational arithmetic) the five secondary-identity claims of
     RESIDUAL and every secondary identity in the 551 template cores.
3. **Combined claim.** I endorse it in the tiered form of §5. **At every positive mass, 70,406 cells are excluded:**
   - 70,233 by cell-level hand lemmas;
   - 172 by the P4/LIN templates, whose hypotheses are secondary initial forms (exact LP certificates);
   - 1 by an exact torque certificate (TD).

   **At generic masses, all 91,273 cells are excluded:**
   - 90,919 by cell-level hand lemmas;
   - 311 by lemmas whose hypotheses include initial forms of secondary identities (exact LP certificates);
   - 43 only by the theorems of §§6–7 of the paper (d64/d88/d98), which are partly computer-assisted.

   Everything rests on the engine's cell list. So RESIDUAL's sentence "all 91,273 nonpositive cells now have a hand
   explanation at generic masses" is correct only with these qualifications.

## 1. What was checked, and how

| task | method | output |
|---|---|---|
| proofs | re-derived by hand for every lemma (statement → hypotheses → conclusion) | §2 |
| algebra | own Singular systems in role variables, masses as variables, saturation by all nonvanishing leading coefficients | `sing/*.sing`, `sing/*.out` |
| hypothesis checks, MECHANISMS | `scripts/refkit.py` (own tree/cell reader), `scripts/ref_lemmas.py` (E, E1, R1, R5, R6, Q, T literal, T by tree domination, P, C, B) on all cells | `scripts/ref_cover.jsonl`, `compare_cov.out` |
| hypothesis checks, RESIDUAL | `scripts/ref_resid.py` (B0, K, L, R1\*, W3, EQ2, TQ) on all cells | `scripts/ref_resid_cover.jsonl`, `cmp_resid.out`, `cmp_global_resid.out` |
| conclusions on the polyhedra | `scripts/ref_lp.py`: my own cell polyhedra (tree order, root ≥ −2, (O1)/(O2), circles, argmin rows of the 14 base identities, common slack); HiGHS | `scripts/ref_lp.jsonl` |
| exact certificates | `scripts/ref_exact.py`: float multipliers, exact re-solve on the support over Q, conditions of Lemma 4.4 checked in Fractions | `resid_certs.out`, `exact_templates_all.out` |
| generic polynomials of the residual cells | `scripts/resid_polys.py` (SymPy): instantiate N, H_W, EQ2, TQ on my own witnesses | `resid_polys.out` |
| coverage accounting | `scripts/cumul_ref.py`, `final_partition.py`, `single_acct.py`, `table21.py`, `misc_counts.py` | `*.out`, `final_classification.jsonl` |

**Validation of my polyhedra.** In all 91,273 cells the stored interior point (`hz`, `hw`) satisfies every row of my
polyhedron with common slack ≥ 0.0345. Every cell is feasible, with largest slack ≥ 0.0714 (`ref_lp.jsonl`; the
slack is capped at 1). This confirms that I read the argmin labels and exponent conventions of `cells.jsonl` as the
engine wrote them. My code reads the same stored data as the authors' code: the implementations are independent,
the data are not.

## 2. Verdict per lemma

### 2.1 MECHANISMS.md

| lemma | claimed generality | verdict | my checks |
|---|---|---|---|
| Principle 0, (x1)–(x4) | — | **CORRECT** | Re-derived. (x2) uses ζ ≥ min(a_k,a_l) > −2; (x3) uses E ∉ A_U, so the minimum −x_kl < 0; (x4) uses e(Z_kl) < a_k = ζ_kl, so x_kl > 0. |
| **T** (torque, deepest cross pair) | every positive mass (m_p m_q ≠ 0) | **CORRECT** | Proof re-derived: cases (i)/(ii) in each tree, strictness from the strict tree order, and (S). Implemented twice: literally ((Z), (W), (S)), and as tree domination. The second shows that exponent(t) − exponent(t₀) is a nonnegative combination of internal edge increments, not identically 0, which is itself a proof of the conclusion. Both select the same **40,084** cells, and every literal witness is a domination witness (`compare_cov.out`). LP check 40,084/40,084. |
| **P** (positive I′) | every positive mass (E ≠ 0) | **CORRECT** | 13,293 cells, identical; LP check (a_k + b_k > 0 on the whole cell) 13,293/13,293. P is needed: 5,355 cells have no other every-mass cell-level lemma (`final_partition.out`). |
| **C** (cluster sum) | every positive mass | **CORRECT WITH FIX** | 46,289 cells, identical; LP check 46,289/46,289. The statement must require X ≠ ∅ (fix M2). Both checkers do. |
| **B** (binary) | every positive mass | **CORRECT WITH FIX** | Sign typo in the proof (fix M1), harmless. 184 cells, identical; LP 184/184. Never needed: all 184 cells are in T ∪ C (`misc_counts.out`). |
| **E** (class level) | generic, Q_T | **CORRECT** | Classes recomputed from `enum/n6.json`: {3, 40, 148, 149, 150, 183}, the authors' ECLS. E1's hypotheses hold on all 50,399 of their cells. |
| **E1** (balanced triangle) | generic | **CORRECT** | `sing/E1.out`: the elimination ideal is exactly ⟨Q_T·Q′_T·Q″_T·Q‴_T⟩, both when the w-balance is at a z-balanced vertex and when it is at the third vertex. The hand claim that the Q′ are positive at positive masses holds (m_am_b + m_c(√m_a − √m_b)² > 0). 86,875 cells, identical. The U_T variant is never needed: 0 cells (`compare_cov.out`). |
| **R1** | generic | **CORRECT WITH FIX** | `sing/R156.out`: the elimination ideal is ⟨R(ab;s)·(deg-12 factor)⟩, and the one-balance + U_T variant gives the same ideal. 57,183 cells, identical; the variant is never needed (0 cells). Fix M3: define "balanced", and say that "c-centred" forces v to be the root with exactly three children. |
| **R5** | generic | **CORRECT** (never needed) | `sing/R156.out`: the ideal is generated by m_s²(m_a+m_b)³(m_a⁵+m_b⁵) − m_a⁵m_b⁵. 35,572 cells, identical; adds no cell beyond E ∪ E1. |
| **R6** | generic | **CORRECT** | `sing/R156.out`: ⟨(m_s²(m_a+m_b)⁴ − m_a m_b⁵)·(deg-12 factor)⟩. 54,208 cells, identical; adds 456. |
| **Q** | generic | **CORRECT** | Trivial algebra. 2,105 cells, identical; first applicable on 2. |
| **LIN** | as label | **CORRECT as algebra; not cell-level** | Its hypotheses are initial forms of secondary subset sums (engine LPs). I closed this computationally (§4.3): all secondary identities of all 368 LIN cores re-certified exactly on my polyhedra, and the maximal minors recomputed from my own initial forms equal the authors' labels in 368/368. |
| **P4** | every positive mass | **CORRECT; same caveat** | Algebra re-derived. All 183 P4 cores have the structure of the lemma on my trees: 76 via the balance of s, 67 via a torque with terms z_s w_a, z_s w_b (or z_a w_s, z_b w_s) matching the centre colour, 40 via a subset sum with the two forces of s in the centre colour. Their secondary identities are re-certified exactly (`p4_check_all.out`, `exact_templates_all.out`). |

§3.8 of MECHANISMS (core-level label table) is not needed for any cell claim. I checked it only where it
coincides with the above: label types 0, 1, 3, 4 via my eliminations, and the LIN/P4/B templates. I did not referee
LABELS.md.

### 2.2 RESIDUAL.md

| lemma | claimed generality | verdict | my checks |
|---|---|---|---|
| Fact O, Lemma S, full centre of mass | — | **CORRECT** | Re-derived. In Lemma S the partner force is minimal in the partner's equation because e(Y_kj) = e(Y_jk). |
| **B0** | every nonzero mass | **CORRECT** | 38 residual cells, with the same pairs as §2.1 (64: pair 23 ×16; 4: 01 ×8; 23 and 25: 14, 23, 05 ×2 each; 116: 05 ×2). Globally 7,684 non-residual cells, identical. |
| **K** | every nonzero mass | **CORRECT** | Class 4, cells 23, 24, 43, 44 (binary 01, Kepler in w, extra force from 3 or 4). Globally identical (528 non-residual). |
| **L** | every positive mass | **CORRECT WITH FIX** | Steps 1–8 re-derived. The norm identity ∏(A − Bε₂ − Cε₃) = (A³−B³−C³)³ − 27A³B³C³ = −H_L and the absence of positive roots of the quartics are checked in SymPy (`L_identity.out`). The saturated system is the unit ideal at 7 positive mass points, including (1,1,1) and (3,3,1), and is nonempty at m_a = 1, m_b = ω (`sing/L.out`). 12 residual cells and 2,099 others, identical. Fix R2: (L1) must say that O lies below v. |
| **R1\*** | generic | **CORRECT WITH FIX** | `sing/R1star.out`: the elimination ideal equals ⟨N⟩; N is irreducible over Q, of degree 18; the specialisation is R(ab;s)·(deg-12). 43 residual cells: (α) 39, (β) 1 (class 4 cell 8, Lemma-S set {0,1}), (γ) 3 (class 4 cell 58, class 28 cell 0, class 53 cell 1). Every instantiated N is a nonzero polynomial, with the M_A, M_B of RESIDUAL §4.1 (`resid_polys.out`). (γ) is certified exactly (§4.4). Fix R3: state case (β) precisely. |
| **W3** | generic | **CORRECT** | `sing/W3EQ2TQ.out`: the elimination ideal is exactly ⟨H_W⟩ for both choices of the balanced pair. My shape vectors on the 15 residual cells equal RESIDUAL §5's up to scale. H_W is a nonzero polynomial in all 15 cells, of degree 24 after clearing denominators of e (`resid_polys.out`). |
| **EQ2** | generic | **CORRECT** | `sing/W3EQ2TQ.out`: the ideal is ⟨m_a²M_A⁴ − m_b²M_B⁴⟩. Cells 15/30 and 15/0: the relation m₃ŷ₃ + m₄ŷ₄ = 0 gives m₃⁶ − m₄⁶ ≠ 0. |
| **TQ** | generic | **CORRECT** | `sing/W3EQ2TQ.out`: E[1] = (n₁²−n₁n₂+n₂²)(M₁²−M₁M₂+M₂²)·S, with S = (A+B)²(C+D)² − 16ABCD (A = n₁³, …). S ≥ 0 by AM–GM, with equality only for n₁ = n₂, M₁ = M₂, which proves the positive-mass statement. (T3) is certified exactly (§4.4). |
| **TD** | every mass | **CORRECT as an exact certificate, not a hand lemma** | T_{0,3,4} in cell 15/0 has the single minimal term δ₀₂³ z₂ w₀: all 14 other terms are certified strictly larger, exactly, on my polyhedron. |
| families A, B, C (§10.1) | core level | **not needed** | These are statements about engine cores, not cells. Family A is necessity only, as the note says. At cell level the cells are covered by L (92/92 family-A cells), W3 (15/15) and R1\* with E1 (19/19). The 48 N1 cells have E1, C or E (`scripts/families_check.out`). |

## 3. Coverage comparison

### 3.1 MECHANISMS lemmas, all 91,273 cells (`scripts/compare_cov.out`)

| lemma | cells (mine) | cells (theirs) | cell-by-cell agreement |
|---|---|---|---|
| T | 40,084 | 40,084 | 91,273/91,273 |
| P | 13,293 | 13,293 | 91,273/91,273 |
| C | 46,289 | 46,289 | 91,273/91,273 |
| B | 184 | 184 | 91,273/91,273 |
| E1 | 86,875 (main hypothesis alone) | 86,875 | 91,273/91,273 |
| R1 | 57,183 (main hypothesis alone) | 57,183 | 91,273/91,273 |
| R5 | 35,572 | 35,572 | 91,273/91,273 |
| R6 | 54,208 | 54,208 | 91,273/91,273 |
| Q | 2,105 | 2,105 | 91,273/91,273 |

Cumulative counts reproduced exactly (`cumul_ref.out`):
- **Generic first:** E 50,399 → E1 86,875 → R1 88,738 → R6 89,194 → Q 89,256 → T 89,714 → C 90,407 → templates
  90,958 → d-folders 91,158. The residue is 115 cells.
- **Every positive mass:** T 40,084 → P 45,439 → C 68,312 → all-mass templates 68,496.
- **Single-term cells:** 51,330 of 52,432 are in T ∪ P ∪ C ∪ B. Of the other 1,102, 1,059 are covered by
  E/E1/R1/R5/R6/Q and 43 are residual (`single_acct.out`).

### 3.2 Residual cells (`scripts/cmp_resid.out`, `cumul_ref.out`)

My list of the 115 cells whose first entry in `coverage.jsonl` is `comp` equals RESIDUAL's. My first applicable
lemmas, taken in the order B0, K, L, R1\*(α/β), W3, EQ2, cover 38, 4, 12, 40, 15 and 2 cells. Together with the 3
(γ) cells and the TQ cell this makes 115. The per-cell lemma sets agree with `resid_cover.jsonl`, with two kinds of
difference:
- **TD.** The authors' `TD` flag is a re-certification of the engine's single-term identity. Their global summary
  credits it to all 43 single-term residual cells (`allmass_gain_TD: 43`); 42 of these have B0 or K anyway.
- **TQ in class 15.** My checker finds the combinatorial part of TQ also in cells 15/0 and 15/30. That is not
  needed, since EQ2 covers both cells.

### 3.3 Residual lemmas, all cells (`scripts/cmp_global_resid.out`)

On the 91,158 non-residual cells:
- **Identical:** B0 (7,684), K (528), L (2,099), R1\*(α/β) (79,254), EQ2 (2,644).
- **W3:** both flag the same 635 cells, and mine flags 1,591 more. The authors' checker also requires the whole
  solution space to be one-dimensional and all e_k ≠ 0. Neither condition is in the lemma, and W3 is used only on
  the 15 residual cells, where both checkers agree. No claim depends on this.

### 3.4 Every-mass recount (`cumul_ref.out`, `final_partition.out`)

Starting from 68,496, B0 adds 254, K adds 76 and L adds 1,579, for 70,405; TD on cell 15/0 makes **70,406**, as
RESIDUAL claims. Without the templates (cell-level lemmas only) the total is 70,233, and 70,234 with TD.

## 4. Exact and LP certificates

### 4.1 Conclusions of T, P, C, B
On my own polyhedra, every claimed minimal term is strictly below every other term of its identity on the open cell
(max slack ≤ 1e-9 for the negation), in 40,084 / 13,293 / 46,289 / 184 cells, with 0 failures (`ref_lp.jsonl`).
This is a floating-point cross-check. For T the conclusion is moreover proved exactly by tree domination (§2.1).

### 4.2 The 115 residual cells
The generic polynomials are nonzero in all 61 residual cells whose first lemma is generic: R1\* 43, W3 15,
EQ2 2, TQ 1 (`resid_polys.out`).

### 4.3 The 551 template cores (`exact_templates_all.out`, `p4_check_all.out`)
- The template cores contain 960 subset sums and 67 torques. For each of them, the argmin on my polyhedra is
  constant on the cell and equals the terms of the engine's initial form. All 1,111 equalities are between identical
  exponent forms, and all 9,246 strict inequalities are certified exactly by Lemma 4.4.
- LIN: the minors recomputed from my initial forms equal the labels in 368/368 cells.
- P4: the structure of the lemma holds in 183/183 cells.

### 4.4 The five secondary-identity claims of RESIDUAL (`resid_certs.out`)
Each is certified exactly, with my own multipliers on my own polyhedra:
- the subset sums S_w(3,4,5) in 4/58, S_w(2,3,4) in 28/0 and S_z(1,4,5) in 53/1 (10 inequalities each);
- the torque T_{3,4} in 0/0 (12 inequalities);
- the torque T_{0,3,4} in 15/0 (14 inequalities).

## 5. The combined statement I endorse

**Assumptions.**
- (A) The engine's cell list: Proposition 4.4 of the paper, with the trees and the exact argmin sets of the 14
  base identities of each of the 91,273 nonpositive cells.
- (B) The theorems of §§6–7 of the paper (d64, d88, d98, refereed) for the diagrams CC64, 66, 88, 89, 93, 94 and 98.
  These are partly computer-assisted: Lemma C4cert for 66, the Krawczyk boxes of Lemma d88comp for 88 and 94, and
  the † checks of Theorems d93/d98.

**Statement.** Under (A) and (B), each of the 91,273 nonpositive cells is excluded at generic positive masses as
follows (`final_classification.jsonl`).

| tier | cells | lemmas | masses | inputs beyond (A) |
|---|---|---|---|---|
| A1 | 70,233 | T, P, C, B (MECHANISMS); B0, K, L (RESIDUAL) | every positive mass | none |
| A2 | 172 | P4 (m_a³+m_b³ = 0) 171, LIN with a one-signed minor 1 | every positive mass | initial forms of secondary subset sums/torques (exact LP; engine and here) |
| A3 | 1 (15/0) | TD | every positive mass | one exact torque certificate |
| G1 | 20,683 | E/E1, R1, R6, Q; R1\*(α/β), W3, EQ2 | generic | none |
| G2 | 4 | R1\*(γ) ×3, TQ ×1 | generic | one secondary identity each (exact certificate) |
| G3 | 137 | LIN (maximal minors, e.g. AK's H) | generic | secondary subset sums (exact LP; engine and here) |
| D | 43 | §§6–7 of the paper only | generic | (B) |

- **Every positive mass:** A1 + A2 + A3 = **70,406** cells.
- **Cell-level hand lemmas:** they cover A1 + G1 = 90,916 cells, and generically also 3 cells of A2/A3: the P4
  cells 15/1 and 15/31 and the TD cell 15/0, all three covered by EQ2. That is **90,919** cells in all.
- **Secondary-identity lemmas:** tiers A2 + A3 + G2 + G3 contain 314 cells. 311 of them have no cell-level lemma at
  all, so 90,919 + 311 + 43 = 91,273.
- **Tier D by class:** 124 (CC64) 10, 143 (CC66) 11, 127 (CC88) 9, 147 (CC94) 9, 132 (CC93) 2, 31 (CC89) 1,
  133 (CC98) 1.
- **Tier A2:** 128 of its cells are class-124 P4 cells, which the d64 theorem also covers, but only generically.

**Polynomials of the generic tiers (nonzero).**
- E/E1: Q_T = m_a²m_b² + m_b²m_c² + m_c²m_a² − 2m_am_bm_c(m_a+m_b+m_c). At positive masses it vanishes exactly
  when one m^{−1/2} is the sum of the other two; the full elimination ideal is ⟨Q_TQ′_TQ″_TQ‴_T⟩.
- R1: R(ab;s) = m_s²(m_a+m_b)⁴ − m_a³m_b³, times a degree-12 factor.
- R6: (m_s²(m_a+m_b)⁴ − m_a m_b⁵), times a degree-12 factor.
- Q: ∏_ε Σ_{k∈K} ε_k m_k.
- R1\*: N(m_a, m_b, m_s, M_A, M_B), degree 18, irreducible, with M_A, M_B partial sums of masses.
- W3: H_W, degree 24 after clearing denominators.
- EQ2: m_a²M_A⁴ − m_b²M_B⁴ (here m₃⁶ − m₄⁶).
- TQ: (n₁²−n₁n₂+n₂²)(M₁²−M₁M₂+M₂²)S.
- LIN: the maximal minors.

These polynomials are taken over all triangles and relabellings, and together with those of (B) they give the
exceptional set.

**What remains computational.**
1. The cell list (A), including the exact argmin sets.
2. The secondary-identity hypotheses of tiers A2, A3, G2 and G3. These involve 314 cells for the stated claims, and
   311 cells for the generic claim alone. All have exact LP certificates (the engine's `tsec_exact`, and
   independently mine: §4.3 and §4.4).
3. The computer-assisted parts of (B), for 43 cells.
4. The bridge from data to lemmas: the checker programs. These are now two independent implementations that agree
   cell by cell.

## 6. Fixes

**MECHANISMS.md**
- M1. §2.5, proof of Lemma B: the difference of the equations is z_kl = **+**(m_k+m_l)Z_kl + Σ_{j∉{k,l}} m_j(Z_kj − Z_lj).
- M2. §2.4, Lemma C (C2): require X ≠ ∅. The empty set would give an empty mass sum; the checker requires X ≠ ∅.
- M3. §3.2–3.4: define "balanced in colour c" once (A_k^c is exactly the two internal forces). Note that
  "c-centred" forces v to be the root, with exactly the three children {a}, {b} and the rest, so that the centre
  relation is the full centre of mass.
- M4. §3.5/3.7: LIN and P4 are templates on engine cores, and their hypotheses are initial forms of secondary
  identities. For the paper, either restate them at cell level with these argmins as certified hypotheses (I have
  exact certificates for all 551 cores), or list the 314 cells of tiers A2, A3, G2 and G3 as computational.
- M5. §2.1 table: the row "torque, |J| = 3, δ³ z_k w_l" has 5,630 cells under E/E1/R1/R5/R6/Q, not 5,628
  (`data/tables.md` says 5,630). The δ³ z_k w_l / δ³ w_k z_l labels of the one-body and pair torques are as recorded
  with 0 ∈ J, not normalised to the smaller of J and J^c. Say so.
- M6. §0 and §5.2: the residue of 115 cells lies in **16** classes, not 17.
- M7. §3.3 Remark (2): 65,920 is the number of cells whose *first witness* triangle is balanced at all three
  vertices in both colours. With any triangle the number is 74,920.
- M8. §2.6 is superseded by RESIDUAL (B0, K, TD/EQ2). The variants of E1 (U_T) and R1 (one balance + U_T) and the
  lemmas R5 and B are never needed and can be dropped or kept as remarks.

**RESIDUAL.md**
- R1. TD is an exact LP certificate, not a hand lemma. Write "every positive mass: 54 by hand (B0 38, K 4, L 12)
  and 1 by an exact certificate (TD)". In `global_cover_summary.json`, `allmass_gain_TD: 43` credits TD to 42 cells
  that have B0 or K.
- R2. Lemma L (L1): add "O lies below v". The proof uses ŷ_k = X_k, and the checker requires it.
- R3. Lemma R1\* (β): state "every body below a non-O child of the root other than A and B has a minimal position
  and lies in a Lemma-S set contained in these children". This is what the checker implements, and it is what makes
  Lemma S cancel the full positions.
- R4. Lemma W3: record per cell that H_W ≢ 0 (15/15, degree 24). Note that e_a, e_b, e_c are pairwise distinct at
  a place, because ŷ_kl ≠ 0.
- R5. §0 headline: qualify "all 91,273 cells have a hand explanation at generic masses" as in §5. 43 cells rest only
  on §§6–7 of the paper, which are partly computer-assisted. For the generic claim, 311 cells rest only on lemmas
  with secondary-identity hypotheses (exact LP). Everything rests on (A).
- R6. §10.1, families A, B and C are core-level statements and are not needed for the cell claims; say so where
  they are introduced.

**For the paper (suggestion).** E/E1 and the three-body clique census of §5.2 overlap in 84,155 cells. Each covers
cells the other does not (2,720 E/E1 only, 2,783 clique only), and the union has 89,658 cells
(`scripts/clique_overlap.out`). If the hand explanation enters the paper, E1 can complement Corollary 5.6: it
needs no strokes, only one node per tree and balance at three of the six vertex–colour slots.

## 7. Minor observations
- **Unsaturated Singular runs.** The authors' Singular scripts assign `sat` to an ideal; they never use `sat(...)[1]`.
- **Unchecked descriptive counts.** The splits "outer–outer / far cluster" and "J is the w-triangle" in MECHANISMS
  §2.2 Remark (2) depend on which witness is chosen, and I did not check them.
- **Time zone.** MECHANISMS' status line gives 2026-10-17 (PDT), but the file was written at 2026-10-16 20:01 PDT.

## 8. Files (all under `hand_explanations/independent/`)
- `REFEREE_REPORT.md`: this report.
- `final_classification.jsonl`: one line per cell, with its tier (§5), lemmas, template and d-class.
- `sing/E1.sing`, `R156.sing`, `R1star.sing`, `W3EQ2TQ.sing`, `L.sing`, with outputs `*.out`.
- `scripts/refkit.py`, `ref_lemmas.py`, `run_ref.py` → `ref_cover.jsonl`.
- `scripts/ref_resid.py`, `run_resid.py` → `ref_resid_cover.jsonl`.
- `scripts/ref_lp.py` → `ref_lp.jsonl`.
- `scripts/ref_exact.py`, `resid_certs.py` → `resid_certs.out`.
- `scripts/verify_templates.py`, `exact_templates.py` (`ALL_TEMPLATES=1`), `p4_check.py` → `exact_templates_all.out`, `p4_check_all.out`.
- `scripts/resid_polys.py`, `L_identity*.py` → `resid_polys.out`, `L_identity.out`.
- `scripts/compare_cov.py`, `cmp_resid.py`, `cmp_global_resid.py`, `cumul_ref.py`, `single_acct.py`, `table21.py`,
  `misc_counts.py`, `final_partition.py`, `clique_overlap.py`, `families_check.py` → the corresponding `.out` files.
- **Run.** Use a Python with highspy and python-flint; the SymPy scripts also need SymPy. Singular is run as `Singular -q sing/X.sing`. The
  whole verification takes under 10 minutes on 12 cores (`run_ref.py` 92 s, `ref_lp.py` 88 s).
