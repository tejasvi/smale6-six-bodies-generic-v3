# Why the nonpositive cells of the six-body engine are empty: hand lemmas (v2)

*In this supplement: this note is `hand_explanations/MECHANISMS.md` (version 2, corrected); the version reviewed in `hand_explanations/independent/REFEREE_REPORT.md` is `hand_explanations/refereed/MECHANISMS.md`. Paths of programs and data in this note (`scripts/`, `data/`, `checks/`) are relative to `hand_explanations/mechanisms/`.*

Status: v2, 2026-10-17 (PDT), revised after the referee report `hand_explanations/independent/REFEREE_REPORT.md`
(2026-10-17 PDT). The refereed text is `hand_explanations/refereed/MECHANISMS.md` (written 2026-10-16, 20:01 PDT; its status line gave
2026-10-17), and it is left unchanged. The lemmas of §§2–4 are proved here by hand; the algebra of the triangle
lemmas is also checked symbolically (`checks/*.sing`). Every coverage number is produced by `scripts/coverage.py`
(combinatorial checks of the hypotheses on the stored cell data) and `scripts/tables.py`; the numbers that are new
or corrected in v2 come from `scripts/counts_v2.py` (→ `data/counts_v2.json`) and
`../residual/scripts/tiers_v2.py` (→ `../residual/data/tiers_v2_summary.json`, `../residual/data/tiers_v2.jsonl`),
which read the same stored data. The single-monomial lemmas are cross-checked cell by cell by an independent LP
computation (`scripts/lpcheck.py`). Nothing under `engine/` was modified, and no existing script or data
file of this folder was changed.

## Changes from the refereed version

Item labels are those of the referee report (§6 "Fixes", §7 "Minor observations"). Each change can be found by its
label in the text.

1. **Headline (report §5; M4, M6).** §0 now keeps three kinds of input apart: cell-level hand lemmas, core templates
   whose hypotheses are initial forms of secondary identities (LIN, P4), and the theorems of d64/d88/d98 (§§6–7 of
   the paper). This note alone: 90,407 cells by cell-level hand lemmas, 551 more by the templates, 200 more by
   d64/d88/d98, residue 115. Together with `hand_explanations/RESIDUAL.md`: 90,919 cells by cell-level hand lemmas, 311
   only by lemmas with secondary-identity hypotheses, 43 only by §§6–7 of the paper; at every positive mass 70,406
   (70,233 by cell-level lemmas, 172 by templates, 1 by an exact certificate). The sentence "a short list of local
   lemmas explains all but 315 of the 91,273 cells" is withdrawn: the 90,958 cells it counted include the 551
   template cells.
2. **M1** (§2.5, proof of Lemma B). Sign corrected: z_kl = **+**(m_k+m_l)Z_kl + Σ_{j∉{k,l}} m_j(Z_kj − Z_lj).
3. **M2** (§2.4, Lemma C). (C2) now requires X ≠ ∅, as the checker does.
4. **M3** (§§3.1, 3.4). "Balanced in colour c" is defined once, in §3.1: the minimal terms are exactly the two
   internal forces. After the definition of "c-centred" (§3.4) the note now says that v is then the root of the
   c-tree, with exactly three children ({a}, {b} and the child of s), so that the centre relation is the initial form
   of the full centre of mass.
5. **M4** (§§3.5, 3.7, 5.1). LIN and P4 are stated as templates on engine cores whose hypotheses are initial forms
   of secondary identities, not as cell-level lemmas. The 314 cells that need secondary-identity hypotheses after
   RESIDUAL.md (tiers A2, A3, G2 and G3 of the report; 311 of them have no cell-level lemma) are listed in §5.1
   and counted as computational.
6. **M5** (§2.1). Row "torque, |J| = 3, δ³ z_k w_l": 5,630 cells under E/E1/R1/R5/R6/Q, not 5,628
   (`data/tables.md` and `data/counts_v2.json` both give 5,630; the other entries of the table are unchanged). The
   caption now says that the minimal-term labels are as the engine records them, with k in the side J that
   contains body 0, not normalised to the smaller of J and J^c.
7. **M6** (§0, §5.2). The residue of 115 cells lies in 16 classes, not 17.
8. **M7** (§3.3, Remark (2)). 65,920 is the number of cells whose first witness triangle (in the checker's order) is
   balanced at all three vertices in both colours; with any triangle the number is 74,920 (`data/counts_v2.json`).
9. **M8** (§§2.5, 2.6, 3.3, 3.4). §2.6 is marked as superseded by RESIDUAL.md (B0 38 cells, K 4, and cell 15/0 by
   EQ2 and the certificate TD). The U_T variant of E1, the one-balance + U_T variant of R1, Lemma R5 and Lemma B are
   kept as remarks and marked as never needed: no cell needs them (`data/counts_v2.json`).
10. **Report §7, unchecked descriptive counts** (§2.2, Remark (2)). The shape splits of the Lemma T witnesses are
    now said to depend on the witness the checker finds first; they were not checked independently.
11. **Report §7, time zone** (status line). The dates are now given in Pacific time.

Further documentation fixes from the release re-run of the scripts (2026-10-17 PDT; labels RR1–RR5, as numbered by
the release check; RR2 and RR3 concern RESIDUAL.md only):

12. **RR1** (§3.6, §4, §6). The Q in-situ check ("300 of 300"; 3,800 sampled cells in all) had no stored log:
    `data/insitu.log` holds only the 3,500 checks of E1, R1, R6 and R5. The Q log is now archived as
    `data/insitu_Q.log`, from a re-run of `insitu.py Q 300` on the stored data (300 of 300, as claimed; the release
    re-run printed the same line). The text now cites both logs.
13. **RR4** (§4, §6). `data/per_class_table.md` had no producer script. The new `scripts/per_class_table.py` writes
    it; its output is byte-identical to the stored table (checked with `cmp`), which is unchanged.
14. **RR5** (§6). The "Run" line now says from which folder each command is run (the Python scripts from
    `scripts/`, the Singular checks from the note's folder) and lists the commands of the release re-run, including
    the checks and the v2 scripts.

## 0. Summary

The engine excludes 91,273 nonpositive cells (exponent data with Σx ≤ 0) in 69 diagram classes: 52,432 by a
secondary identity with a single minimal term, 38,841 by an inconsistent subset ("core") of initial forms
certified over Q(m) (37,808 first pass, 990 alternative cores, 43 by the hand proofs of d64/d88/d98).

**Three kinds of input (Headline, M4).** The counts below keep them apart.
- *Cell-level hand lemmas* (all lemmas of §§2–3 except LIN and P4). Their hypotheses are statements about the two
  trees and the argmin sets of the base identities of one cell.
- *Core templates* LIN and P4 (§3.5, §3.7). Their hypotheses are initial forms of secondary identities (subset sums,
  torques), taken from the engine's certified LPs; only the final algebra is by hand.
- *The theorems of d64, d88 and d98* (§§6–7 of the paper, refereed), which are partly computer-assisted.

**This note alone.** The cell-level hand lemmas exclude **90,407** of the 91,273 cells at generic masses, 68,312 of
them at every positive mass (by T, P and C). The templates exclude 551 further cells (184 of them at every positive
mass), and d64/d88/d98 another 200. **115 cells in 16 classes** remain (§5.2; M6: the refereed text said 17).

**Together with `hand_explanations/RESIDUAL.md`** (Lemmas B0, K, L, R1\*, W3, EQ2, TQ and the certificate TD), every
cell is excluded at generic positive masses, under the engine's cell list (§5.1). The tiers are those of the referee
report, §5, recomputed from the notes' own data by `../residual/scripts/tiers_v2.py`:
- **90,919** cells by cell-level hand lemmas;
- **311** cells only by lemmas whose hypotheses include initial forms of secondary identities, all with exact LP
  certificates: the templates P4 and LIN (307 cells), R1\*(γ) (3) and TQ (1);
- **43** cells only by the theorems of §§6–7 of the paper (d64/d88/d98).

At every positive mass **70,406** cells are excluded: 70,233 by cell-level hand lemmas (T, P, C here; B0, K, L in
RESIDUAL.md), 172 by templates (P4 171, LIN with a one-signed minor 1) and 1 (class 15, cell 0) by an exact
torque certificate (TD).

| lemma | mechanism (one line) | masses | cells where it applies |
|---|---|---|---|
| **E** (§3.2) | a zw-triangle with no circle and no other stroke at its vertices forces AK's E(T) (class-level) | generic | 50,399 (6 classes) |
| **E1** (§3.3) | a triangle balanced in one colour at two vertices and in the other colour at one vertex forces E(T) | generic | 86,875 |
| **R1** (§3.4) | a triangle balanced at two vertices with the third at the centre of mass forces AK's R(ab;s) | generic | 57,183 |
| **R5**, **R6** (§3.4) | two further centred-triangle systems; new conditions m_s²(m_a+m_b)³(m_a⁵+m_b⁵) = m_a⁵m_b⁵, m_s²(m_a+m_b)⁴ = m_a m_b⁵ | generic | 35,572 (R5: never needed); 54,208 |
| **T** (§2.2) | the torque T_J is dominated by its deepest cross pair (tree-only) | all positive | 40,084 |
| **P** (§2.3) | every body has a positive partner pair below the origin, so Σ m_k z_k w_k = E has the single minimal term E | all positive | 13,293 |
| **C** (§2.4) | the subset sum of a cluster has one minimal monomial (a force, or positions with one leading coefficient) | all positive | 46,289 |
| **B** (§2.5) | an isolated binary with x > 0: the relative equation has the single minimal monomial −(m_k+m_l)Z_kl | all positive | 184 (never needed: all in T ∪ C) |
| **Q** (§3.6) | a body balanced by forces of equal leading coefficients: Σ ε_k m_k = 0 (EQ, "m_a = m_b + m_c") | generic | 2,105 |
| **LIN**, **P4** (§3.5, §3.7) | templates on engine cores, *not cell-level*: their hypotheses are initial forms of secondary identities. Centre-of-mass relations (Σm, H and bilinear labels); the binary torque m_a³+m_b³ (AK Prop. 4) | LIN: as label; P4: all positive | 368 + 183 (beyond the above) |

Coverage (all 91,273 cells; `data/coverage_summary.json`):
- E or E1 alone: **86,875** cells (95.2%). Adding R1, R6 and Q: 89,256. Adding T and C: **90,407**; this is the
  union of all cell-level lemmas of this note (P, B and R5 add nothing more). Adding the core templates LIN and P4:
  90,958. Adding the whole-class hand proofs of d64, d88 and d98: 91,158. Residue: **115 cells** (16 classes, §5.2),
  resting here on the engine's certified cores; RESIDUAL.md treats them.
- At every positive mass (not only generically): the cell-level lemmas T, P and C exclude 68,312 cells (B adds
  none), and the all-mass templates (P4 183, LIN 1) 184 more, for 68,496. These include **51,330 of the 52,432
  single-term cells** (97.9%), all by cell-level lemmas.
- Single-term exclusions (task 1): T explains 40,084, P 13,293 (5,355 beyond T), C 29,307 (5,891 beyond T ∪ P); the 1,102
  single-term cells outside T ∪ P ∪ C ∪ B are explained generically by E/E1/R1/R6/Q (1,059) or are in the residue
  (43; RESIDUAL.md excludes them by B0, K and, for cell 15/0, EQ2 and TD).
- Cores (task 2): every certified label type of `label_types.json` is accounted for in §3.8. Hand derivations are
  given for E(T), R(ab;s), H and its bilinear relatives, the partial mass sums, m_a³+m_b³, AK's EQ and
  "m_a = m_b + m_c" from equidistant forces, and the two new conditions R5, R6; the cores carrying these labels are
  35,866 of the 37,808 certified first-pass cores (§3.8).
  The cells of the other label types are, with 72 exceptions, also covered by the cell-level lemmas.

What remains computational (§5): the completeness of the cell enumeration and the exact argmin data of each cell
(the engine's certified LPs); the initial forms of secondary identities used by the templates LIN and P4 (551 cells
in this note; after RESIDUAL.md, 314 cells use a secondary identity, 311 of them have no cell-level lemma, and
§5.1 lists them); the computer-assisted parts of d64/d88/d98 (43 cells after RESIDUAL.md); and, in this note,
the 115 residual cells.

## 1. Framework and notation

We use the six-body versions of §§2.1–2.5 and 3.1 of the five-body paper (their proofs do not use n = 5),
exactly as in d98/DERIVATION.md A.1.

- The AK system on X_m: z_k = Σ_{l≠k} m_l Z_kl, w_k = Σ_{l≠k} m_l W_kl, δ_kl² z_kl w_kl = 1, with z_kl = z_k − z_l,
  Z_kl = δ_kl³ z_kl, W_kl = δ_kl³ w_kl, Σ m_k z_k = Σ m_k w_k = 0, and U = Σ m_k m_l δ_kl = Σ m_k z_k w_k = I
  (Lemma U(a)); on a curve C ⊂ Y_m with U ≢ 0, U ≡ E is a nonzero constant.
- **Place lemma.** At a singular place, every function f of z-, w- or neutral type is ϑ^{d e(f)}(f̂ + o(1)) with a
  leading coefficient f̂ ≠ 0. Every component of 𝒵 = (z_k, Z_kl) and 𝒲 has exponent ≥ −2; circles and strokes are the
  components of exponent −2. For f, g of exponents ≥ e: [fg]_{e+e'} = [f]_e[g]_{e'}, [f+g]_e = [f]_e + [g]_e.
- Exponents: a_k = e(z_k), b_k = e(w_k) (+∞ if z_k ≡ 0: the body sits at the origin O in that colour; the engine
  allows this), ζ_kl = e(z_kl), ω_kl = e(w_kl), x_kl = (ζ_kl + ω_kl)/2, e(δ_kl) = −x_kl,
  e(Z_kl) = −(ζ_kl + 3ω_kl)/2, e(W_kl) = −(3ζ_kl + ω_kl)/2. (O1)–(O6) of the five-body Lemma "orders".
- **Trees.** The z-exponents of the bodies and of O form an ultrametric: a rooted tree on the bodies and O whose internal
  nodes carry heights h, strictly increasing from a node to each internal child; ζ_kl = h(meet(k,l)),
  a_k = h(meet(k,O)). The leading coefficient ẑ_kl is X_{v,c(k)} − X_{v,c(l)}, the difference of the coordinates of
  the children of v = meet(k,l) containing k and l; ẑ_k = ẑ_{kO}. In particular, if three bodies lie in three distinct
  children of one node v, their leading coefficients at exponent h(v) satisfy ẑ_ab + ẑ_bc + ẑ_ca = 0 ("closure").
  The same holds for w. A **cell** of the engine is a pair of trees together with the exact sets of minimal terms of
  the base identities; on the open cell all heights are free subject to strict linear inequalities, so an inequality
  between two heights that holds by the tree order (an ancestor is lower) is strict on the whole cell.
- **Cell data used by the lemmas.** A_k^z (resp. A_k^w): the set of minimal terms of body k's equation
  z_k − Σ_l m_l Z_kl = 0 (terms: the position z_k and the forces Z_kl); A_U: the minimal terms of U − E = 0
  (terms E and δ_kl). For a body with a stroke or circle the set is forced by the diagram (the terms of exponent −2).
- **(D_kl)** δ̂_kl² ẑ_kl ŵ_kl = 1 for every pair (exponent −2x + ζ + ω = 0).

**Principle 0 (one minimal monomial).** Let Σ_t c_t(m) f_t ≡ 0 on C, with monomials f_t in units of C[C] and
c_t ∈ Q[m]. On a cell, if all terms of least exponent have the same leading monomial up to sign, the initial form is
(Σ_{t minimal} ±c_t(m)) · (nonzero monomial), so Σ ±c_t(m) = 0. A single minimal term is impossible; so is a set of
minimal terms whose coefficients add up to a partial mass sum (positive masses) — this is the content of the
engine's single-term test and of the 'none' cores.

Positivity of x on a pair. We say **x_kl > 0 is forced** on a cell if one of the following holds:
- (x1) kl is a zw-edge (x = 1 by (O4));
- (x2) kl is a z-stroke whose ends are not z-circled, or a w-stroke whose ends are not w-circled: ζ = 3x − 2 by (O3)
  and ζ_kl ≥ min(a_k, a_l) > −2;
- (x3) δ_kl ∈ A_U and E ∉ A_U: −x_kl is the minimum of the exponents of U − E, which is < 0;
- (x4) Z_kl ∈ A_k^z, z_k ∉ A_k^z and meet_z(k,O) = meet_z(k,l) (so a_k = ζ_kl): then −(ζ+3ω)/2 < ζ, i.e. x_kl > 0;
  the same with the colours exchanged, or with k and l exchanged.

## 2. Single-term exclusions (52,432 cells)

### 2.1 What the engine recorded

`tsec_exact.py` tries the secondary identities in a fixed order (torques T_J with 0 ∈ J and sub-virials, by |J|;
then differences of body equations; subset sums S_J, 2 ≤ |J| ≤ 4; I'; U − I) and records the first with a single
minimal term on the whole cell. Only three identity types ever occur:

| identity | minimal term | cells | T | P | C | B | T, P, C or B | E/E1/R1/R5/R6/Q | residue |
|---|---|---|---|---|---|---|---|---|---|
| torque, \|J\| = 3 | δ³ w_k z_l | 25,689 | 25,646 | 7,056 | 15,962 | 0 | 25,649 | 25,620 | 1 |
| subset sum, \|J\| = 3 | a force Z_ij | 5,784 | 0 | 0 | 5,280 | 0 | 5,280 | 5,784 | 0 |
| torque, \|J\| = 3 | δ³ z_k w_l | 5,638 | 5,596 | 882 | 1,995 | 0 | 5,602 | 5,630 | 0 |
| I' = Σ m z w | E | 5,355 | 0 | 5,355 | 0 | 0 | 5,355 | 5,355 | 0 |
| torque of one body | δ³ z_k w_l | 2,723 | 2,419 | 0 | 1,492 | 72 | 2,635 | 2,505 | 28 |
| torque of one body | δ³ w_k z_l | 2,619 | 2,319 | 0 | 1,490 | 22 | 2,553 | 2,497 | 6 |
| torque, \|J\| = 2 | δ³ w_k z_l | 2,320 | 2,156 | 0 | 1,612 | 0 | 2,228 | 2,220 | 8 |
| torque, \|J\| = 2 | δ³ z_k w_l | 2,112 | 1,948 | 0 | 1,476 | 0 | 2,028 | 2,102 | 0 |
| subset sum, \|J\| = 4 | a position | 192 | 0 | 0 | 0 | 0 | 0 | 192 | 0 |

(|J| is min(|J|, 6 − |J|); T_{J^c} = −T_J. The torque of one body is w_k·(z-equation of k) − z_k·(w-equation of k).
The columns give the number of these cells on which each lemma's hypotheses hold; a lemma may use a different identity
than the one the engine recorded first. **M5:** the labels of the column "minimal term" are as the engine records
them: k ∈ J and l ∉ J for the set J that contains body 0 (`engine/tsec.py`, function `secondary`:
T1 = δ_kl³ z_k w_l, T2 = δ_kl³ w_k z_l). They are not normalised to the smaller of J and J^c, so for the torques of
one body and of pairs, k may lie on the larger side. The entry 5,630 in the row "torque, |J| = 3, δ³ z_k w_l" was
misprinted as 5,628 in the refereed text; `data/tables.md` and `data/counts_v2.json` give 5,630.) The 192 subset
sums of four bodies are a triangle plus one body whose position is balanced by the three forces of the triangle; they are covered generically (E, E1) but by no all-mass
lemma here.

### 2.2 Lemma T (the torque and its deepest cross pair)

For a nonempty proper set J of bodies the torque
  T_J = Σ_{k∈J, l∉J} m_k m_l δ_kl³ (z_k w_l − w_k z_l)
vanishes on X_m: it equals Σ_{k∈J} m_k(w_k F_k − z_k G_k) with F_k, G_k the total z- and w-force on k from outside
J, and by the body equations and antisymmetry this is Σ_{k∈J} m_k(w_k z_k − z_k w_k) = 0. Its terms are indexed by
the **ordered cross pairs** (p, q) (p and q on different sides of J): ±m_p m_q δ_pq³ z_p w_q, of exponent
  E(p,q) = A(p;q) + B(q;p),  A(p;q) := a_p − (3/2)ζ_pq,  B(q;p) := b_q − (3/2)ω_pq,
a z-tree quantity plus a w-tree quantity. (A term is absent if z_p ≡ 0 or w_q ≡ 0.)

**Lemma T.** Let J be as above and (p, q) an ordered cross pair with a_p, b_q < ∞ such that
- (Z) every cross pair {k, l} meets in the z-tree at an ancestor of (or at) meet_z(p,q), and meet_z(p,O) is an
  ancestor of (or equal to) meet_z(p,q), i.e. a_p ≤ ζ_pq;
- (W) every cross pair meets in the w-tree at an ancestor of (or at) meet_w(p,q), and b_q ≤ ω_pq;
- (S) no other ordered cross pair (k, l) has the same four nodes meet_z(k,l), meet_z(k,O), meet_w(k,l), meet_w(l,O).

Then the term of (p, q) is the only term of T_J of least exponent on the whole cell. Hence no place has these exponent
data, at any masses with m_p m_q ≠ 0.

*Proof.* Let (k, l) be an ordered cross pair with a_k < ∞, t = meet_z(p,q), t' = meet_z(k,l). By (Z), t' is an
ancestor of t or equal to it, so ζ_kl ≤ ζ_pq.
(i) If O lies below t', then a_k ≥ ζ_kl (meet_z(k,O) lies below t' or is t'), so
A(k;l) ≥ −ζ_kl/2 ≥ −ζ_pq/2 ≥ a_p − (3/2)ζ_pq = A(p;q), using a_p ≤ ζ_pq.
(ii) If O does not lie below t', it does not lie below t either. Both p and k lie below t', so
meet_z(p,O) = meet_z(k,O) = meet_z(t',O); hence a_k = a_p and A(k;l) = a_p − (3/2)ζ_kl ≥ A(p;q).
In both cases each inequality used is either an identity of nodes or a strict tree inequality, which is strict on the
whole open cell. Equality throughout forces t' = t and meet_z(k,O) = meet_z(p,O) (in case (i): a_k = ζ_kl and
a_p = ζ_pq say that both positions meet O at t). The same argument in the w-tree gives B(l;k) ≥ B(q;p), with
equality only if meet_w(k,l) = meet_w(p,q) and meet_w(l,O) = meet_w(q,O). So E(k,l) ≥ E(p,q) for every term, with
equality only for the excluded coincidence (S). The leading coefficient of the term of (p,q) is
±m_p m_q δ̂_pq³ ẑ_p ŵ_q ≠ 0, so the initial form of T_J is a nonzero monomial (Principle 0). ∎

*Remarks.* (1) The criterion is exactly "tree domination": for each competitor, A(k;l) − A(p;q) and B(l;k) − B(q;p) are
nonnegative combinations of edge increments of the two trees. `scripts/explore7.py` tests that property directly
(subtree sums) and finds the same 40,084 cells as `lemmas.lemma_T`.
(2) Shapes of the witnesses (`data/tables.md`; these splits depend on which witness `lemmas.lemma_T` finds first,
in its order of J and of the cross pairs, and they were not checked independently; report §7): **outer–outer** (a_p = ζ_pq, b_q = ω_pq; the term is ≈ δ_pq, so
the torque is dominated by the potential of the closest cross pair) in 25,912 cells; **far cluster**
(a_p < ζ_pq: p and q form a z-cluster away from O, b_q = ω_pq) in 14,172 cells. J (or J^c) is the w-triangle of the
diagram in 17,644 cells (class 128 and its relatives: the torque between the two triangles), a z-triangle in 2,850,
another 3-set in 10,264, a single body in 4,982, a pair in 4,344.
(3) d98 Theorem 2 (diagram 90) and Lemma 2 of d64 are instances of the same mechanism (d98 (F4) is the outer–outer
case).

### 2.3 Lemma P (positive I')

**Lemma P.** Suppose every body k with a_k, b_k < ∞ has a partner l such that O lies below meet_z(k,l) and below
meet_w(k,l), and x_kl > 0 is forced ((x1)–(x4)). Then the identity Σ_k m_k z_k w_k − E = 0 has E as its only
minimal term; so no place has these data (E ≠ 0).

*Proof.* O below meet_z(k,l) means a_k ≥ ζ_kl; likewise b_k ≥ ω_kl. So a_k + b_k ≥ 2x_kl > 0 for every term
m_k z_k w_k, while E has exponent 0. ∎

This is Lemma 3.3 of the five-body paper (min x ≤ 0) read through I' instead of I: I has its minimum attained twice
on every cell (the engine imposes it), but I' = Σ m_k z_k w_k has a different term structure. Coverage: 13,293 cells,
including all 5,355 cells recorded with I'. In class 128 (z-triangle Z, w-triangle W) the typical witness is: O lies
inside the w-cluster of Z and inside the z-cluster of W, the partners are the strokes, and a_k + b_k ≥ 2x > 0.

### 2.4 Lemma C (cluster sum)

For a set J of bodies, S_J := Σ_{i∈J} m_i·(z-equation of i): Σ_{i∈J} m_i z_i − Σ_{i∈J, j∉J} m_i m_j Z_ij = 0 (the
internal forces cancel in pairs, m_i m_l (Z_il + Z_li) = 0). Let μ_i be the least exponent in body i's equation.

**Lemma C.** Let J (|J| ≥ 2) and a colour (say z) satisfy:
- (C1) the graph on J with an edge {i,l} whenever Z_il ∈ A_i^z and Z_li ∈ A_l^z, or z_i ∈ A_i^z, z_l ∈ A_l^z and
  meet_z(i,O) = meet_z(l,O), is connected;
- (C2) the set X of non-internal minimal terms (positions z_i and forces Z_ij, j ∉ J, lying in some A_i^z, i ∈ J) is
  **nonempty** (M2) and is a single term, or consists of positions z_i (i ∈ I) with one common leading coefficient:
  all i ∈ I have the same node v = meet_z(i,O) and lie in one child of v.

Then the initial form of S_J is a nonzero monomial times a positive mass sum; no place has these data (any positive
masses).

*Proof.* Along an edge of (C1), μ_i = e(Z_il) = e(Z_li) = μ_l, resp. μ_i = a_i = a_l = μ_l; so all μ_i equal some
μ. Every term of S_J is a term of exactly one equation of J, so it has exponent ≥ μ, with equality exactly for the
elements of X. (If X were empty, every term of S_J would have exponent > μ and nothing would follow; this is why
(C2) asks for X ≠ ∅, and the checker `lemmas.lemma_C_witness` requires it.) If X is one term, Principle 0 applies.
Otherwise all z_i, i ∈ I, have the same leading coefficient ẑ ≠ 0 (the difference of the coordinates of the child
containing I and of the child containing O), and the initial form is (Σ_{i∈I} m_i) ẑ ≠ 0. ∎

The merged case is the "cluster far from the origin must be pulled by an outside force" mechanism; it is also the
content of the engine's most frequent 'none' cores (partial mass sums, §3.5).

### 2.5 Lemma B (binary)

**Lemma B.** Let {k, l} and a colour (z) satisfy A_k^z ⊆ {Z_kl, z_k} with Z_kl ∈ A_k^z, A_l^z ⊆ {Z_lk, z_l} with
Z_lk ∈ A_l^z, and let x_kl > 0 be forced. Then no place has these data (m_k + m_l ≠ 0).

*Proof.* The difference of the two equations reads (**M1**: the sign of the first term is +; z_k = m_l Z_kl + …,
z_l = m_k Z_lk + … = −m_k Z_kl + …)
  z_kl = (m_k+m_l) Z_kl + Σ_{j∉{k,l}} m_j (Z_kj − Z_lj),
i.e. z_kl − (m_k+m_l) Z_kl − Σ_{j∉{k,l}} m_j (Z_kj − Z_lj) = 0. Here e(Z_kl) = μ_k = μ_l, e(Z_kj) > μ_k and
e(Z_lj) > μ_l for j ∉ {k,l}, and e(z_kl) = ζ_kl > e(Z_kl) = ζ_kl − 3x_kl because x_kl > 0. So the only minimal
monomial of this identity is −(m_k+m_l) δ̂_kl³ ẑ_kl ≠ 0. ∎

An isolated binary must have x = 0 (Kepler: δ̂³ = 1/(m_k+m_l)). Lemma B covers 184 cells, all also covered by T or C
(`data/counts_v2.json`), so it is **never needed** for coverage (M8); it is kept because it is the hand form of the
4,699 'binary' cores (§3.8).

### 2.6 Single-term residue (superseded, M8)

*Superseded by `hand_explanations/RESIDUAL.md`.* It excludes 42 of the 43 cells below by hand at every nonzero mass,
by Lemma B0 (38 cells) and Lemma K (4 cells). The remaining cell, class 15 cell 0, is excluded generically by Lemma
EQ2 and at every positive mass by an exact torque certificate (TD; an LP certificate, not a hand lemma). The
refereed text of this section follows.

43 single-term cells are covered neither by T, P, C, B nor by the generic triangle lemmas: torques in the fully or
partly circled classes 4 (12), 15 (1), 23 (6), 25 (6), 64 (16), 116 (2). Their exclusions use (O1), the circles
(a root at −2), the stroke parametrizations and argmin data of U and of body equations (LP certificates printed by
`scripts/explain_resid.py`); no uniform hand statement is given here.

## 3. Cores and the triangle lemmas (38,841 cells)

### 3.1 How the cores look

`tcore.py` finds, per cell, a minimal inconsistent subset of the initial forms (QuickXplain, local equations first).
`scripts/coreparse.py` reads each initial form as a physical relation: a **balance** (a body equation whose minimal
terms are forces only), a balance with the position (a three-body central-configuration equation), a
**centre relation** (a subset sum whose minimal terms are positions only), the potential U_T of a triangle (from U or
from a sub-virial V_T), I' restricted to some bodies, a torque, a **binary** relation (difference of two body
equations), and distance equations. Up to relabelling bodies and exchanging colours there are 1,038 relation patterns
(`data/core_patterns.json`); grouped by the multiset of relation kinds there are 757 (`scripts/core_sigs.py`). The
largest groups, with the engine's label (§3.8 gives the label table):

| relations in the core (besides distance equations) | label | cores |
|---|---|---|
| one centre relation of 2 bodies with one leading coefficient: (m_a + m_b) Ŷ = 0 | m_a + m_b | 5,856 |
| one centre relation of 3 bodies with one leading coefficient | m_a + m_b + m_c | 5,446 |
| binary: −(m_k + m_l) Ẑ_kl = 0 | m_k + m_l | 4,699 |
| triangle: U_T, two w-balances, one z-balance | E(T) | 2,860 |
| triangle: U_T, one w-balance, one z-balance | E(T) | 1,969 |
| triangle: two w-balances, one z-balance | E(T) | 1,939 |
| triangle: V_T, one w-balance, one z-balance | E(T) | 1,851 |
| two centre relations sharing two leading coefficients | H: m_a m_b = m_c m_d | 1,617 |
| triangle: V_T, one w-balance, two z-balances | E(T) | 1,254 |
| triangle: U_T, one w-balance, a w-centre relation (third vertex at the centre) | R(ab;s) | 1,172 |
| triangle: U_T, two w-balances, a w-centre relation | R(ab;s) | 1,001 |
| triangle: two w-balances, a w-centre relation | R(ab;s) | 722 |
| triangle: I' on two bodies, U_T, one w-balance | R(ab;s) or R5 | 480 |
| triangle: V_T, a z-balance, a z-centre relation | R(ab;s) | 448 |
| two centre relations of 3 bodies, one coefficient each | Σ of three masses (twice) | 444 |
| triangle: one w-balance, a w-centre and a z-centre relation | type 5 / type 10 | 420 |
| triangle: U_T, one w-balance, a z-centre relation | R5 | 394 |

So the cores are of four kinds: partial mass sums (cluster centres of mass and binaries), the binary torque
(m_a³ + m_b³), linear relations between centres of mass (H and its relatives), and the leading systems of one
triangle (§3.2–3.4), plus single balances by equidistant forces (§3.6). The first three are §2.4–2.5, §3.5 and §3.7.

**Balanced vertices (M3).** Let T be three bodies, k ∈ T and {l, l'} = T ∖ k. The vertex k is **balanced in colour
c** (with respect to T) if the minimal terms of k's c-equation are exactly the two internal forces of T at k:
A_k^z = {Z_kl, Z_kl'} for c = z, A_k^w = {W_kl, W_kl'} for c = w. The initial form of k's c-equation is then
m_l F_kl + m_l' F_kl' = 0 (resp. the same with G; notation of §3.3): the position and all other forces have larger
exponent. This is the notion used in Lemmas E, E1, R1, R5 and R6 and in the checker (`lemmas.balanced`). A
"balance" in a core (above) is more generally any body equation whose minimal terms are forces only.

### 3.2 Lemma E (zw-triangle; class-level; AK's (23))

**Lemma E.** Let T = {a, b, c} be a zw-triangle of the diagram (three zw-edges) whose vertices carry no circle and
no stroke other than those of T. At every singular place with this diagram the masses satisfy
  Q_T(m) := m_a²m_b² + m_b²m_c² + m_c²m_a² − 2 m_a m_b m_c (m_a + m_b + m_c) = 0,
i.e. one of m_a^{−1/2}, m_b^{−1/2}, m_c^{−1/2} is the sum of the other two (AK's E(T)).

*Proof.* (O4) gives ζ = ω = 1 on the three pairs; three equal ζ put a, b, c in three distinct children of one node
of the z-tree (if two were in one child their ζ would be larger), and likewise in the w-tree. The six strokes give
e(Z_kl) = e(W_kl) = −2 for kl ⊂ T. At a vertex k, a_k > −2 (no circle) and e(Z_kj) > −2 for j ∉ T (no other
stroke). So A_k^z and A_k^w are the two internal forces at every vertex, and Lemma E1 below (with B_z = B_w = T)
gives the claim. ∎

The six classes with such a triangle are 3, 148, 149, 40, 150, 183 (`scripts/classes_overview.py`): **50,399
cells**, among them all 44,247 cells of class 3 (the analogue of the five-body diagram 5) and all 4,777 of
class 148. The script checks that E1's hypotheses hold on every one of these cells. In the five-body paper diagram 5
needed the hulls of its §3.4 because it settles every mass; at generic masses E(T) alone suffices.

### 3.3 Lemma E1 (balanced triangle)

**Lemma E1.** Let T = {a, b, c} be three bodies such that
- (H1) the three pairs of T meet at one node of the z-tree and at one node of the w-tree;
- (H2) B_z := {k ∈ T : A_k^z = {Z_kl, Z_kl'}, {l, l'} = T∖k} (the vertices balanced in z, §3.1) and B_w (the same
  in w) satisfy (|B_z| ≥ 2 and |B_w| ≥ 1) or (|B_w| ≥ 2 and |B_z| ≥ 1).

Then x_c + u x_b + v x_a = 0 for some u, v ∈ {±1, ±i}, where x_k = m_k^{−1/2}; at positive masses this says
Q_T(m) = 0 (E(T)). The elimination ideal of the system is generated by Q_T·Q'_T·Q''_T·Q'''_T, where
Q'_T = (m_a m_b + m_b m_c + m_c m_a)² − 4 m_a m_b m_c² and its two permutations are positive at positive masses
(Q'_T = 0 would give m_a m_b + m_c(√m_a − √m_b)² = 0).

*Proof.* Write ξ_kl = ẑ_kl, η_kl = ŵ_kl (the coefficients at the common exponents ζ_T, ω_T), P_kl = δ̂_kl, and
F_kl = P_kl³ ξ_kl, G_kl = P_kl³ η_kl (antisymmetric in kl). By (H1), ξ_ab + ξ_bc + ξ_ca = 0 and the same for η
(closure); by (D_kl), F_kl G_kl = P_kl⁴. By (H2) the initial form of the z-equation of k ∈ B_z is
m_l F_kl + m_l' F_kl' = 0, and the same in w. Orient the pairs cyclically (ab, bc, ca) and let m̄_kl denote the
mass of the third vertex. Assume |B_z| ≥ 2 (the other case is the colour exchange). Balance at a gives
m_b F_ab = m_c F_ca, balance at b gives m_a F_ab = m_c F_bc, so F_kl = λ m̄_kl with λ ≠ 0. Hence
ξ_kl = λ m̄_kl / P_kl³ and, by (D_kl), η_kl = P_kl / (λ m̄_kl). Put p_kl = P_kl / m̄_kl^{1/2}. The two closures
become
  (Ξ) x_c p_ab^{−3} + x_a p_bc^{−3} + x_b p_ca^{−3} = 0,   (Η) x_c p_ab + x_a p_bc + x_b p_ca = 0.
A w-balance at a reads m_b G_ab = m_c G_ca with G_kl = P_kl⁴ / (λ m̄_kl), i.e. m_b² P_ab⁴ = m_c² P_ca⁴, i.e.
p_ca = u p_ab with u⁴ = 1 (at b or c: the same with the letters permuted). Since u^{−3} = u, (Ξ) and (Η) give
(x_c + u x_b) p_ab^{−3} = −x_a p_bc^{−3} and (x_c + u x_b) p_ab = −x_a p_bc. Here x_c + u x_b ≠ 0 (else
x_a p_bc = 0), so dividing, p_bc⁴ = p_ab⁴, p_bc = v p_ab with v⁴ = 1, and (Η) becomes x_c + u x_b + v x_a = 0.
For positive x the imaginary part forces u, v real or u = −v = ±i with x_a = x_b and then x_c = 0; so u, v ∈ {±1},
not both 1: one of the x's is the sum of the other two. ∎

*Remarks.* (1) Eliminating with Singular (`checks/tri_E1.sing`) gives exactly the product of the four quartics
(label type 0 of `label_types.json`). (2) Variant (**never needed**, M8): if B_z and B_w are nonempty and
A_U = {δ_ab, δ_bc, δ_ca}, the same conclusion holds (`checks/tri_E1b.sing`, `checks/tri_variants.sing` (a)); by
hand: with p as above and the three closures/U_T written as (Ξ), (Η), (U): x_c p_ab + x_a p_bc + x_b p_ca = 0, the
differences (Ξ) − (U) and (Η) − (U) force p_ca⁴ = p_bc⁴ = p_ab⁴. The variant is never needed for coverage: on every
one of the 86,875 cells where E1 holds, the main hypothesis (H2) holds for some triangle (the variant's hypotheses
hold on 71,461 cells, but on none of them alone; `data/counts_v2.json`). **M7:** on 74,920 of these cells some
triangle is balanced at all three vertices in both colours. (The refereed text gave 65,920, which is the number of
cells whose *first* witness triangle, in the checker's order, has this property.)
(3) Given z-balance at two vertices, U_T is equivalent to (Η); this is why U appears in many E(T) cores in place of a
distance equation. (4) E1 holds on 86,875 cells, including all 50,399 cells of Lemma E.

### 3.4 Centred triangles: Lemmas R1, R5, R6

Say that s ∈ T is **c-centred** (c a colour) if, at the common node v of T in the c-tree, the two other vertices a, b
lie in children of v that contain no other body and not O, while s, O and all bodies outside T lie in one further
child. Then the positions of a, b have exponent h(v) and leading coefficients Y_a, Y_b, every other position has a
larger exponent, so the centre of mass gives **m_a Y_a + m_b Y_b = 0**, and the c-separations of s from a, b have
leading coefficients Y_a, Y_b (the coordinate of the child of s is that of O).

**(M3)** A c-centred vertex forces v to be the **root** of the c-tree, with **exactly three children**: {a}, {b} and
the child of s. Indeed every body and O lie below v, and a further child would have to contain a body or O. So the
centre relation is the initial form of the *full* centre of mass Σ_k m_k z_k = 0 (resp. Σ_k m_k w_k = 0) at exponent
h(v): the positions of the bodies in the child of s have larger exponent, or vanish for bodies at O. "Balanced" is
meant in the sense of §3.1.

**Lemma R1 (AK's R(ab;s)).** Let T = {a, b, s} satisfy (H1), let a and b be balanced in colour c, and let s be
c-centred. Then Π_{ω³ = 1} [m_s²(m_a+m_b)(m_b + ω m_a)³ − m_a³m_b³] = 0; the factor ω = 1 is
  R(ab;s): m_s² (m_a + m_b)⁴ = m_a³ m_b³.

*Proof (c = w).* Balance at a and b: G_kl = μ m̄_kl, so η_kl = μ m̄_kl / P_kl³ and ξ_kl = P_kl / (μ m̄_kl). Centre:
η_as = Y_a, η_bs = Y_b with m_a Y_a + m_b Y_b = 0, i.e. m_a m_b μ (1/P_bs³ − 1/P_sa³) = 0, so P_sa = ω P_bs,
ω³ = 1. The w-closure m_s/P_ab³ + m_a/P_bs³ + m_b/P_sa³ = 0 gives P_bs³ = −(m_a+m_b) P_ab³ / m_s; write P_bs = κ P_ab
with κ³ = −(m_a+m_b)/m_s. The z-closure P_ab/m_s + P_bs/m_a + P_sa/m_b = 0 (it is U_T) gives
κ(m_b + ω m_a) = −m_a m_b / m_s; cubing, m_s²(m_a+m_b)(m_b + ω m_a)³ = m_a³ m_b³. ∎
Variant (**never needed**, M8): balance at only one of a, b, together with U_T, gives the same polynomial
(`checks/tri_variants.sing` (b); by hand as above: balance at a gives P_as³ = −(m_a+m_b)P_ab³/m_s, then U_T and the
z-closure give the cube). Its hypotheses hold on no cell (`data/counts_v2.json`); all 57,183 R1 cells have two
balances.

**Lemma R5 (new; never needed for coverage, M8).** Let T = {a, b, s} satisfy (H1), let a be balanced in colour c, let s be c'-centred in the other
colour c', and let A_U = {δ_ab, δ_bs, δ_sa}. Then
  R5(ab;s): m_s² (m_a + m_b)³ (m_a⁵ + m_b⁵) = m_a⁵ m_b⁵.

*Proof (c = z, c' = w).* Centre: η_as = Y_a, η_bs = −(m_a/m_b) Y_a, η_ab = (m_a+m_b) Y_a / m_b; ξ_kl = 1/(P_kl² η_kl).
The z-balance at a, m_b P_ab³ ξ_ab + m_s P_as³ ξ_as = 0, becomes P_as = −m_b² P_ab / (m_s M), M = m_a + m_b.
U_T then gives P_bs = −m_a² P_ab / (m_s M). The z-closure ξ_ab + ξ_bs + ξ_sa = 0 reads
m_b/(M P_ab²) − m_b/(m_a P_bs²) − 1/P_as² = 0; substituting, m_a⁵ m_b⁵ = m_s² M³ (m_a⁵ + m_b⁵). ∎ (`checks/tri_R5.sing`:
the elimination ideal is generated by this one polynomial; label type 3.)

**Lemma R6 (new).** Let T = {a, b, s} satisfy (H1), let s be c-centred and balanced in colour c, and let a be
balanced in the other colour. Then the masses satisfy m_s²(m_a+m_b)⁴ = m_a m_b⁵ or a second (degree-12) factor
(`checks/tri_R6.sing`; label type 4).

*Proof (c = w).* Centre and balance at s: m_a P_sa³ Y_a + m_b P_sb³ Y_b = 0 with Y_b = −(m_a/m_b) Y_a gives
P_sa³ = P_sb³. The z-balance at a gives, as in R5, P_as = −m_b² P_ab/(m_s M). With P_bs = P_sa (the real branch), the
z-closure m_b/(M P_ab²) − m_b/(m_a P_bs²) − 1/P_as² = 0 becomes m_a m_b⁵ = m_s² M⁴; the other cube roots give the
second factor. ∎

Each of E1, R1, R5, R6 was also checked in situ (`scripts/insitu.py`): on random samples of the cells where the
lemma applies (1,000 each for E1, R1, R6; 500 for R5), the lemma's relations written in the cell's own leading
coefficients (tinit's variables) are inconsistent at random masses mod 32003 (Singular). All 3,500 checks passed
(`data/insitu.log`).

The hypotheses of R1/R5/R6 hold on 57,183 / 35,572 / 54,208 cells; beyond E and E1 they add 1,863 (R1) and 456
(R6) cells. R5 adds no cell: each of its 35,572 cells is covered by E or E1 (`data/counts_v2.json`). It is therefore
never needed for coverage (M8), and it is kept because its polynomial is label type 3 (895 cores).

### 3.5 Lemma LIN (relations between centres of mass)

**Lemma LIN.** Suppose the initial forms of some subset sums on a cell consist of positions only. Each is a linear
form Σ_v M_v Y_v in the leading coefficients Y_v of the positions (bodies with the same coefficient grouped; M_v a
partial sum of masses). If r of these forms involve at most r distinct coefficients Y_v (which are independent tree
coordinates and nonzero) and their matrix has full column rank, all Y_v vanish, a contradiction. Hence the maximal
minors of the matrix vanish.

One form, one coefficient: M_v = 0 — impossible at positive masses (label types Σ of 2, 3 or 4 masses; the cell-level
version is Lemma C). Two forms in two coefficients: M_1 M_4 = M_2 M_3, which is AK's **H** (m_a m_b = m_c m_d) when
every M is one mass, and label types 9, 12–14, 19–21 (e.g. m_a(m_b+m_c+m_d) = m_e m_f) when some M are sums.
`corefam.fam_lin` recognises the pattern in the engine's cores and recomputes the minors. `scripts/check_labels.py`
compares the hand conditions of all template cores with the engine's eliminations (labels_all.jsonl): LIN 15,171
cores agree (14,727 with the same generator set, 444 with one of two generators; the other generator is the second
centre relation), 48 more LIN cores have no engine label (elimination timeout); B 4,699 and P4 405 cores agree. No
disagreement.

The cores of type LIN use the engine's identification of the initial forms of the secondary subset sums (exact LP
certificates in tsec_exact); only the final algebra is by hand. As the first applicable lemma, LIN is needed for 368
cells (367 generic, 1 at every positive mass).

**Status (M4).** LIN is a *template on engine cores*, not a cell-level lemma. Its hypotheses are initial forms of
secondary identities (subset sums), and the cell data used by the cell-level lemmas (trees and argmin sets of the
base identities) do not contain them. The cells that need LIN are therefore counted as computational: they are
listed in §5.1. After RESIDUAL.md, 230 of the 367 generic LIN cells have a cell-level hand lemma (R1\*, W3 or
EQ2), 137 rest on LIN (tier G3 of the report), and the one every-mass LIN cell (class 122, cell 1) rests on LIN
(tier A2). The referee re-certified exactly, on independently built cell polyhedra, all secondary identities of
the 368 LIN cores and recomputed the minors (report §4.3).

### 3.6 Lemma Q (equidistant forces)

**Lemma Q.** Suppose body s's equation in a colour has as minimal terms exactly the forces Z_sk, k ∈ K, |K| ≥ 2, and
all bodies of K lie in one child of one node in each tree, that node being meet(s, k). Then Σ_{k∈K} ε_k m_k = 0 for
some signs ε_k = ±1. For |K| = 2 this is AK's EQ, m_a = m_b at positive masses (label type 18); for |K| = 3, one mass
of K is the sum of the other two (label type 17).

*Proof.* The separations of s from the bodies of K have one common leading coefficient in each colour, ẑ_sk = ẑ,
ŵ_sk = ŵ. By (D_sk), δ̂_sk² = 1/(ẑŵ) for all k, so δ̂_sk = ε_k δ̂. The initial form of the balance is
Σ_k m_k δ̂_sk³ ẑ = δ̂³ ẑ Σ_k ε_k m_k = 0. ∎

Seen from s, the cluster K is a single point; for real configurations all ε_k = 1 and the balance is impossible, but
complex places allow signs. Q holds on 2,105 cells (first applicable on 2); in-situ check: 300 of 300 samples
(`data/insitu_Q.log`, RR1: the output of the original run was not kept, and `data/insitu.log` has only the E1, R1,
R5 and R6 runs; the log is a re-run of `insitu.py Q 300` on 2026-10-17, whose sample and masses depend only on the
stored `data/coverage.jsonl` and the fixed seed; the release re-run printed the same line).

### 3.7 Lemma P4 (binary torque; AK Proposition 4, d64 Lemma 2)

**Lemma P4.** Suppose a cell carries: a centre relation m_a Y_a + m_b Y_b = 0 of a pair in colour c (with a third body
s at the c-origin relative to a, b: η_sa = −Y_a, η_sb = −Y_b); a relation κ·(m_a P_sa³ η_sa + m_b P_sb³ η_sb) = 0 with
κ ≠ 0 (the balance of s, or a torque or subset sum with this initial form); and the distance equations of sa and sb
with one common coefficient ξ of the other colour. Then m_a³ + m_b³ = 0, impossible at positive masses.

*Proof.* By (D), P_sk² = −1/(ξ Y_k). So P_sk³ Y_k = −P_sk / ξ and the second relation is m_a P_sa + m_b P_sb = 0.
Squaring, m_a²/Y_a = m_b²/Y_b; with m_a Y_a = −m_b Y_b this gives m_a³ = −m_b³. ∎

All 405 cores of the label m_a³ + m_b³ match this template (`corefam.fam_p4`); as first applicable lemma it is needed
for 183 cells (classes 124, 126, 16, 0, 15).

**Status (M4).** Like LIN, P4 is a *template on engine cores*: the second relation is the initial form of a balance
or of a secondary identity (a torque or a subset sum), and the cells that need it are counted as computational
(§5.1). After RESIDUAL.md, 12 of the 183 P4 cells (class 16) are excluded at every positive mass by the
cell-level Lemma L; the other 171 rest on P4 at every positive mass (tier A2), and 2 of these (class 15, cells 1
and 31) are also excluded generically by the cell-level Lemma EQ2. In 128 of the 171 (class 124) the d64 theorem
also applies, but only generically. The referee checked the structure of the template on all 183 cores and
re-certified their secondary identities exactly (report §2.1, §4.3).

### 3.8 Label types

Label types of `label_types.json` (positive status) and of the 'none' cores (no positive zero), with the hand
derivation (if any) and the cell-level coverage of the cells that carry them. This table is about cores, not cells:
no cell claim of this note depends on it (report §2.1). In the last column, "by LIN" and "by P4" mean the core
templates of §3.5 and §3.7, which are not cell-level (M4).

| label (masses renamed) | json index | cores (cells) | hand derivation | cells also covered by a cell-level lemma |
|---|---|---|---|---|
| m_a + m_b | none | 10,695 | Lemma C / LIN (5,996 cores), Lemma B (4,699 cores) | 10,695 |
| E(T): Q_T · (three positive quartics) | 0 | 9,836 | Lemma E1 | 9,836 |
| m_a + m_b + m_c | none | 6,075 | Lemma C / LIN | 6,075 |
| R(ab;s) · (degree-12 factor) | 1 | 4,102 | Lemma R1 | 4,098 |
| H: m_a m_b − m_c m_d | 2 | 1,799 | Lemma LIN | 1,476 (+323 by LIN) |
| R5(ab;s) | 3 | 895 | Lemma R5 | 895 |
| R6: m_s²(m_a+m_b)⁴ − m_a m_b⁵, · second factor | 4 | 722 | Lemma R6 | 722 |
| (m_a+m_b+m_c), (m_d+m_e+m_f) | none | 444 | LIN | 444 |
| m_a³ + m_b³ | none | 405 | Lemma P4 | 222 (+183 by P4) |
| m_a² + m_a m_b + m_b m_c, quartic | 5 (undec) | 360 | — | 360 |
| Σ of four masses | none | 350 | Lemma C / LIN | 350 |
| (m_a − m_b)(m_a² ± m_a m_b + m_b²) (EQ) | 6 | 327 | — | 250 (+76 by d64/d88/d98) |
| 5-mass polynomial | 7 | 324 | — | 324 |
| m_s²(m_a+m_b)⁴ − m_a⁵ m_b, · other factor | 8 | 286 | first factor as R6 (a↔b); not derived | 286 |
| m_a(m_b+m_c+m_d) − m_e m_f | 9 | 223 | LIN | 198 (+25 by LIN) |
| m_a⁶ − m_b⁶ (EQ) | 10 | 180 | — | 166 (+14 by d98) |
| none computed (Singular timeout) | — | 174 | — (48 match LIN) | 107 (+44 d98) |
| 4-mass polynomial | 11 | 169 | — | 130 |
| m_c(m_d+m_e+m_f) − m_a m_b | 12 | 99 | LIN | 98 (+1) |
| m_c(m_d+m_e) − m_a m_b | 13 | 96 | LIN | 96 |
| m_a(m_b+m_c) − m_d m_e | 14 | 72 | LIN | 68 (+4) |
| quartic family | none | 51 | — | 24 (+23 d98) |
| 4-mass polynomial | 15 | 38 | — | 38 |
| m_c(m_b+m_c)² ± m_a³ | 16 | 32 | — | 32 |
| ±m_a ± m_b ± m_c | 17 | 18 | Lemma Q | 18 |
| m_a² − m_b² (EQ) | 18 | 18 | Lemma Q | 18 |
| m_a(m_b+m_c) − m_d(m_e+m_f) | 19 | 13 | LIN | 13 by LIN |
| (m_c+m_f)(m_d+m_e) − m_a m_b | 20 | 2 | LIN | 2 by LIN |
| m_e m_f − (m_a+m_d)(m_b+m_c) | 21 | 1 | LIN | 1 by LIN |
| m_a m_b m_c + m_d m_e m_f | none | 1 | LIN (3×3) | 1 by LIN |
| (m_a+m_b)(…)(m_c+m_d)(…) | 22 (undec) | 1 | — | 0 |
| alternative cores (talt) | — | 990 | — | 989 (+1 d98) |
| no core (d64/d88/d98 cells) | — | 43 | — | 1 (+42 d64/d88/d98) |

The hand-derived label types carry 35,866 of the 37,808 certified first-pass cores. The engine's cores are minimal
subsets of the complete triangle systems of §3.3–3.4 (U_T or a centre relation often replaces a distance equation);
their eliminations (labels_all.jsonl) coincide with the polynomials derived here. Label types 6 and 10 are again AK's
EQ (m_a = m_b at positive masses), but from triangle systems whose balances contain positions (circled or x = 0
triangles: three-body central configurations at leading order) or that carry centre relations in both colours; they
and types 5, 7, 8, 11, 15, 16, 22 are not derived here.

## 4. Coverage

`scripts/coverage.py` reads every one of the 91,273 cells (trees and argmin sets from `cells.jsonl`; the engine's
core from the `sec/p*.cores.jsonl` files or the alternative cores) and checks the hypotheses of the lemmas. Order of
the "first applicable" column: E, T, P, C, B, E1, R1, R5, R6, Q, the core templates (B, LIN, P4), the whole-class proofs
(d64: classes 124, 143; d88: 127, 147; d98: 31, 131, 132, 133), else "comp".

| first applicable | single-term cells | core cells | total |
|---|---|---|---|
| E (class-level) | 26,775 | 23,624 | 50,399 |
| T | 18,475 | 0 | 18,475 |
| P | 3,444 | 0 | 3,444 |
| C | 3,155 | 5,856 | 9,011 |
| E1 | 540 | 8,141 | 8,681 |
| R1 | 0 | 175 | 175 |
| R6 | 0 | 220 | 220 |
| Q | 0 | 2 | 2 |
| core template LIN | 0 | 368 | 368 |
| core template P4 | 0 | 183 | 183 |
| d64 / d88 / d98 | 0 | 43 / 36 / 121 | 200 |
| residue (comp) | 43 | 72 | 115 |
| **total** | 52,432 | 38,841 | **91,273** |

The rows "core template LIN" and "core template P4" are not cell-level lemmas (M4): their hypotheses are initial
forms of secondary identities (§3.5, §3.7).

Cumulative, generic-first: E 50,399 → +E1 86,875 → +R1 88,738 → +R6 89,194 → +Q 89,256 → +T 89,714 → +C 90,407 →
+templates 90,958 → +d-folders 91,158. All-mass-first: T 40,084 → +P 45,439 → +C 68,312 → +templates 68,863 → +E
81,880 → +E1 90,561 → +R1, R6, Q 90,958 → +d-folders 91,158. (In the second chain "+templates" adds all 551
template cells, including the 367 generic LIN cells; at every positive mass the count is 68,312 + 184 = 68,496.)

**Coverage after RESIDUAL.md, by tier (Headline, M4).** Each cell is put in the first tier that excludes it, by
the weakest input it needs (referee report §5; `../residual/scripts/tiers_v2.py` → `../residual/data/tiers_v2.jsonl`,
which reproduces the referee's counts from the notes' own data).

| tier | cells | lemmas | masses | inputs beyond the engine's cell list |
|---|---|---|---|---|
| A1 | 70,233 | T, P, C (this note; B adds none); B0, K, L (RESIDUAL_v2) | every positive mass | none |
| A2 | 172 | templates P4 (171) and LIN with a one-signed minor (1) | every positive mass | initial forms of secondary identities (exact LP) |
| A3 | 1 (class 15, cell 0) | TD | every positive mass | one exact torque certificate |
| G1 | 20,683 | E/E1, R1, R6, Q (this note); R1\*(α/β), W3, EQ2 (RESIDUAL_v2) | generic | none |
| G2 | 4 | R1\*(γ) (3), TQ (1) | generic | one secondary identity each (exact certificate) |
| G3 | 137 | template LIN (maximal minors) | generic | initial forms of secondary subset sums (exact LP) |
| D | 43 | the theorems of d64/d88/d98 only | generic | §§6–7 of the paper (partly computer-assisted) |

So 70,233 + 172 + 1 = 70,406 cells are excluded at every positive mass. The cell-level hand lemmas cover
A1 + G1 = 90,916 cells, and generically also 3 cells of A2/A3 (class 15, cells 0, 1 and 31, by EQ2): **90,919** in
all. Tiers A2, A3, G2 and G3 contain 314 cells; 311 of them have no cell-level lemma, and 90,919 + 311 + 43 =
91,273. Tier D by class: 124 (CC64) 10, 143 (CC66) 11, 127 (CC88) 9, 147 (CC94) 9, 132 (CC93) 2, 31 (CC89) 1,
133 (CC98) 1.

Independent checks:
- `scripts/lpcheck.py 0`: for every cell where T, P, C or B holds (40,084 + 13,293 + 46,289 + 184 checks), a
  floating-point LP over the full cell polyhedron (trees, (O1)–(O2), circles, argmin rows) confirms that the claimed
  monomial is strictly below every other term of the identity. All passed.
- `scripts/explore7.py`: the tree-domination criterion (subtree sums) and Lemma T select the same 40,084 cells.
- `scripts/insitu.py`: 3,800 sampled cells for E1, R1, R5, R6, Q (see §3.4, §3.6); all inconsistent mod p. These are
  the 3,500 checks of E1, R1, R6 (1,000 each) and R5 (500) in `data/insitu.log` and the 300 checks of Q in
  `data/insitu_Q.log` (RR1).
- `checks/*.sing`: the eliminations of E1 (two variants), R1 (two variants), R5, R6 give exactly the stated
  polynomials (and, for E1, R1, R5, R6, the engine's label types 0, 1, 3, 4).
- Referee report §§2–4 (2026-10-17): checkers written independently from the statements agree with `lemmas.py`
  cell by cell on all 91,273 cells for T, P, C, B, E1, R1, R5, R6 and Q; an LP check on independently built cell
  polyhedra confirms the conclusions of T, P, C and B with no failure; the eliminations of E1, R1, R5 and R6 were
  redone with saturation in characteristic 0. The data are the same stored cell data.

Per class (`data/per_class_table.md`, written by `scripts/per_class_table.py`; CC = Chang–Chen's label from the
engine's `cc_compare.json`; LIN* = the one all-mass LIN cell). RR4: the table had no producer script; the one added
in v2 reproduces the stored table byte for byte.

| class | CC | diagram (1 z-, 2 w-, 3 zw-edge; circles) | cells | E | T | P | C | E1 | R1 | R6 | Q | LIN | LIN* | P4 | d64 | d88 | d98 | comp |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 3 | 7 | 34:3 35:3 45:3 | 44247 | 44247 |  |  |  |  |  |  |  |  |  |  |  |  |  |  |
| 128 | 11 | 12:1 13:1 23:1 04:2 05:2 45:2 | 32864 |  | 16524 | 2793 | 8170 | 5350 | 27 |  |  |  |  |  |  |  |  |  |
| 148 | 12 | 12:1 13:1 23:1 04:3 05:3 45:3 | 4777 | 4777 |  |  |  |  |  |  |  |  |  |  |  |  |  |  |
| 29 | 8 | 23:1 14:2 15:2 25:1 35:1 45:2 | 1866 |  | 108 | 462 |  | 1278 | 18 |  |  |  |  |  |  |  |  |  |
| 129 | 18 | 12:1 13:1 23:1 04:2 05:2 45:2 wc45 | 1449 |  | 924 |  | 189 | 336 |  |  |  |  |  |  |  |  |  |  |
| 14 | 14 | 23:1 24:1 34:1 15:2 wc15 | 865 |  | 204 |  | 87 | 553 | 9 |  |  |  |  |  |  |  |  | 12 |
| 149 | 19 | 12:1 13:1 23:1 04:3 05:3 45:3 zc23 | 756 | 756 |  |  |  |  |  |  |  |  |  |  |  |  |  |  |
| 130 | 27 | 12:1 13:1 23:1 04:2 05:2 45:2 wc045 | 630 |  |  |  | 28 | 560 | 42 |  |  |  |  |  |  |  |  |  |
| 47 | 48 | 23:1 14:3 05:1 15:3 45:3 zc012345 | 497 |  | 104 |  | 367 |  | 2 |  | 2 | 22 |  |  |  |  |  |  |
| 40 | 15 | 23:1 14:3 15:3 45:3 zc23 | 394 | 394 |  |  |  |  |  |  |  |  |  |  |  |  |  |  |
| 142 | 13 | 12:1 13:1 23:1 04:2 05:2 15:1 25:1 35:1 45:2 | 297 |  |  | 189 |  | 75 | 33 |  |  |  |  |  |  |  |  |  |
| 30 | 16 | 23:1 14:2 15:2 25:1 35:1 45:2 wc14 | 273 |  | 14 |  |  | 238 | 7 | 8 |  |  |  |  |  |  |  | 6 |
| 23 | 46 | 23:1 14:1 34:2 05:1 35:2 45:2 zc012345 | 239 |  | 96 |  | 57 |  |  |  |  | 80 |  |  |  |  |  | 6 |
| 150 | 28 | 12:1 13:1 23:1 04:3 05:3 45:3 zc123 | 224 | 224 |  |  |  |  |  |  |  |  |  |  |  |  |  |  |
| 131 | 90 | 12:1 13:1 23:1 04:2 05:2 45:2 zc23 wc45 | 196 |  | 196 |  |  |  |  |  |  |  |  |  |  |  |  |  |
| 4 | 31 | 34:3 25:1 35:3 45:3 zc2345 | 177 |  | 142 |  | 6 |  | 1 |  |  | 14 |  |  |  |  |  | 14 |
| 64 | 100 | 23:1 04:1 14:2 05:2 15:1 zc012345 wc0145 | 162 |  | 48 |  | 27 |  |  |  |  | 71 |  |  |  |  |  | 16 |
| 44 | 17 | 23:1 14:3 15:3 25:1 35:1 45:3 zc23 | 154 |  | 7 |  |  | 147 |  |  |  |  |  |  |  |  |  |  |
| 132 | 93 | 12:1 13:1 23:1 04:2 05:2 45:2 zc23 wc045 | 147 |  |  |  |  |  |  | 84 |  |  |  |  |  |  | 63 |  |
| 124 | 64 | 12:1 13:1 23:1 14:1 24:1 34:1 05:2 wc05 | 143 |  |  |  | 5 |  |  |  |  |  |  | 128 | 10 |  |  |  |
| 25 | 47 | 23:1 14:1 34:3 05:1 35:3 45:3 zc012345 | 88 |  | 12 |  |  |  |  |  |  | 66 |  |  |  |  |  | 10 |
| 146 | 29 | 12:1 13:1 23:1 04:2 05:2 15:1 25:1 35:1 45:2 zc123 | 81 |  |  |  |  | 72 | 9 |  |  |  |  |  |  |  |  |  |
| 143 | 66 | 12:1 13:1 23:1 04:2 05:2 15:1 25:1 35:1 45:2 wc04 | 77 |  |  |  |  |  |  | 44 |  |  |  |  | 33 |  |  |  |
| 167 | 30 | 12:1 13:1 23:1 04:3 05:3 15:1 25:1 35:1 45:3 zc123 | 72 |  |  |  |  | 72 |  |  |  |  |  |  |  |  |  |  |
| 24 | 20 | 23:1 14:1 34:3 05:1 35:3 45:3 zc012 | 72 |  | 24 |  |  |  |  |  |  | 48 |  |  |  |  |  |  |
| 147 | 94 | 12:1 13:1 23:1 04:2 05:2 15:1 25:1 35:1 45:2 zc123 wc04 | 63 |  |  |  |  |  |  | 36 |  |  |  |  |  | 27 |  |  |
| 31 | 89 | 23:1 14:2 15:2 25:1 35:1 45:2 zc23 wc14 | 49 |  |  |  |  |  |  | 40 |  |  |  |  |  |  | 9 |  |
| 133 | 98 | 12:1 13:1 23:1 04:2 05:2 45:2 zc123 wc045 | 49 |  |  |  |  |  |  |  |  |  |  |  |  |  | 49 |  |
| 15 | 82 | 23:1 24:1 34:1 15:2 zc34 wc15 | 42 |  | 28 |  |  |  |  | 8 |  |  |  | 4 |  |  |  | 2 |
| 56 | 50 | 23:1 14:3 34:1 05:1 15:3 45:3 zc012345 | 37 |  | 4 |  | 27 |  |  |  |  | 4 |  |  |  |  |  | 2 |
| 16 | – | 23:1 24:1 34:1 15:2 zc234 wc15 | 28 |  |  |  |  |  |  |  |  |  |  | 16 |  |  |  | 12 |
| 126 | – | 12:1 13:1 23:1 14:1 24:1 34:1 05:2 zc234 wc05 | 27 |  |  |  |  |  |  |  |  |  |  | 27 |  |  |  |  |
| 55 | 21 | 23:1 14:3 34:1 05:1 15:3 45:3 zc023 | 24 |  | 24 |  |  |  |  |  |  |  |  |  |  |  |  |  |
| 116 | 101 | 13:1 23:2 14:2 24:1 05:1 25:2 35:2 zc012345 wc1234 | 21 |  | 4 |  | 1 |  |  |  |  | 14 |  |  |  |  |  | 2 |
| 42 | 37 | 23:1 14:3 15:3 35:1 45:3 zc12345 | 20 |  |  |  | 20 |  |  |  |  |  |  |  |  |  |  |  |
| 171 | 77 | 12:1 03:1 23:2 04:1 14:2 34:1 05:2 15:1 25:1 wc012345 | 19 |  |  |  |  |  |  |  |  | 19 |  |  |  |  |  |  |
| 169 | 43 | 12:1 13:1 23:1 04:3 05:3 15:1 25:1 35:1 45:3 zc02345 | 18 |  |  |  |  |  | 18 |  |  |  |  |  |  |  |  |  |
| 0 | 81 | 34:1 25:2 zc34 wc25 | 17 |  | 8 |  |  |  |  |  |  |  |  | 8 |  |  |  | 1 |
| 62 | 40 | 23:1 14:3 24:1 34:1 05:1 15:3 45:3 zc01345 | 14 |  |  |  |  |  |  |  |  |  |  |  |  |  |  | 14 |
| 20 | 84 | 23:1 14:1 05:2 zc1234 wc05 | 13 |  |  |  | 11 |  |  |  |  | 2 |  |  |  |  |  |  |
| 122 | 116 | 13:1 23:2 04:1 14:2 05:2 25:1 zc012345 wc012345 | 10 |  |  |  | 9 |  |  |  |  |  | 1 |  |  |  |  |  |
| 10 | 36 | 24:1 34:3 15:1 35:3 45:3 zc12345 | 10 |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  | 9 |
| 170 | 58 | 12:1 13:1 23:1 04:3 05:3 15:1 25:1 35:1 45:3 zc012345 | 9 |  |  |  |  |  | 9 |  |  |  |  |  |  |  |  |  |
| 127 | 88 | 12:1 13:1 23:1 14:1 24:1 34:1 05:2 zc1234 wc05 | 9 |  |  |  |  |  |  |  |  |  |  |  |  | 9 |  |  |
| 63 | 52 | 23:1 14:3 24:1 34:1 05:1 15:3 45:3 zc012345 | 7 |  |  |  |  |  |  |  |  |  |  |  |  |  |  | 7 |
| 172 | 102 | 12:1 03:1 23:2 04:1 14:2 34:1 05:2 15:1 25:1 zc1234 wc012345 | 6 |  |  |  |  |  |  |  |  | 6 |  |  |  |  |  |  |
| 28 | 86 | 23:1 14:1 24:1 34:1 05:2 zc1234 wc05 | 3 |  | 2 |  |  |  |  |  |  |  |  |  |  |  |  | 1 |
| 53 | 95 | 23:1 14:3 05:2 15:3 45:3 zc23 wc0145 | 3 |  | 2 |  |  |  |  |  |  |  |  |  |  |  |  | 1 |
| 58 | 107 | 23:1 14:3 34:2 05:3 15:1 25:2 zc012345 wc012345 | 2 |  |  |  |  |  |  |  |  | 2 |  |  |  |  |  |  |
| 117 | 109 | 13:1 23:2 04:1 24:2 05:2 15:2 25:1 zc012345 wc012345 | 2 |  |  |  |  |  |  |  |  | 2 |  |  |  |  |  |  |
| 120 | 111 | 13:1 23:2 04:1 24:3 05:3 15:2 zc012345 wc012345 | 2 |  |  |  |  |  |  |  |  | 2 |  |  |  |  |  |  |
| 69 | 87 | 23:1 04:2 14:2 05:2 15:2 zc23 wc0145 | 2 |  |  |  | 2 |  |  |  |  |  |  |  |  |  |  |  |
| 22 | 85 | 23:1 14:1 34:1 05:2 zc1234 wc05 | 2 |  |  |  | 2 |  |  |  |  |  |  |  |  |  |  |  |
| 67 | 59 | 23:1 04:2 14:2 05:2 15:2 zc23 | 2 |  |  |  | 2 |  |  |  |  |  |  |  |  |  |  |  |
| 57 | 106 | 23:1 14:3 34:2 05:3 25:2 45:1 zc012345 wc012345 | 2 |  |  |  |  |  |  |  |  | 2 |  |  |  |  |  |  |
| 183 | 76 | 12:3 13:3 23:3 04:3 05:3 45:3 | 1 | 1 |  |  |  |  |  |  |  |  |  |  |  |  |  |  |
| 65 | 104 | 23:1 04:1 14:2 34:2 05:2 15:1 25:2 zc012345 wc012345 | 1 |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  |
| 110 | 114 | 23:3 04:1 14:2 05:2 15:1 25:3 35:3 zc012345 wc012345 | 1 |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  |
| 12 | 62 | 14:1 24:2 34:3 05:1 25:3 35:2 zc012345 | 1 |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  |
| 119 | 110 | 13:1 23:2 04:1 24:3 05:2 15:3 zc012345 wc012345 | 1 |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  |
| 121 | 112 | 13:1 23:2 04:1 24:3 05:3 15:2 25:1 zc012345 wc012345 | 1 |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  |
| 66 | 108 | 23:1 04:1 14:3 34:2 05:3 15:1 25:2 zc012345 wc012345 | 1 |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  |
| 123 | 115 | 13:1 23:2 04:3 24:1 05:3 15:2 45:3 zc012345 wc012345 | 1 |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  |
| 34 | 61 | 23:1 14:2 34:3 05:1 15:3 35:2 zc012345 | 1 |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  |
| 8 | 99 | 24:1 34:2 25:2 35:1 zc2345 wc2345 | 1 |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  |
| 84 | 63 | 23:3 24:3 34:3 25:3 35:3 45:3 | 1 |  |  |  | 1 |  |  |  |  |  |  |  |  |  |  |  |
| 13 | 103 | 14:1 24:2 34:3 05:3 15:2 25:1 zc012345 wc012345 | 1 |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  |
| 173 | 117 | 12:1 03:1 23:2 04:1 14:2 34:1 05:2 15:1 25:1 zc012345 wc012345 | 1 |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  |
| 35 | 105 | 23:1 14:2 34:3 05:3 15:1 25:2 zc012345 wc012345 | 1 |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  |

## 5. What remains computational, and gaps

### 5.1 Inputs taken from the engine (not replaced)

1. **Completeness of the cell decomposition** (treplay.py: every LP prune carries an exact Motzkin certificate) and the
   correctness of each cell's data: the trees and the exact argmin sets of the base identities (body equations, U, I).
   All lemmas take these as hypotheses; their verification is combinatorial (`lemmas.py`).
2. **Initial forms of secondary identities (M4).** The templates LIN and P4 (551 cells as first applicable in this
   note) take the constant argmin sets of secondary subset sums and torques from tsec_exact's certified LPs. The
   cell-level lemmas T, P, C, B, E1, R1, R5, R6, Q do not use them. RESIDUAL.md adds R1\*(γ) and TQ (one secondary
   identity each) and the certificate TD. After it, the cells whose exclusion uses a secondary identity are the 314
   cells of tiers A2, A3, G2 and G3 (§4), listed in the table below; for the 311 of them that have no cell-level
   lemma, the secondary identities are part of the computational input. All of them have exact LP certificates: the
   engine's (tsec_exact), RESIDUAL's for R1\*(γ), TQ and TD (`../residual/data/certificates.txt`), and,
   independently, the referee's (report §§4.3–4.4).
3. **The theorems of d64, d88 and d98** (§§6–7 of the paper, refereed) for the diagrams CC64, 66, 88, 89, 93, 94 and
   98. They are partly computer-assisted: Lemma C4cert for 66, the Krawczyk boxes of Lemma d88comp for 88 and 94, and
   the † checks of Theorems d93/d98. After RESIDUAL.md, 43 cells rest on them alone (tier D; by class in §4).
4. The theory inputs listed in GENERIC.md §"Trusted computing base" (the five-body setup at n = 6, the okR rules,
   Lemma U(a), (O1)–(O6)); AK Rule 2e is not needed by these lemmas (E and E1 use the trees directly).

**The 314 cells that use a secondary identity** (tiers A2, A3, G2, G3 after RESIDUAL.md; from
`../residual/data/tiers_v2.jsonl`). A star marks the 3 cells that the cell-level Lemma EQ2 also excludes generically;
the other 311 have no cell-level lemma.

| class | tier | input | cells | cell indices |
|---|---|---|---|---|
| 0 | A2 | P4 | 8 | 1–4, 13–16 |
| 0 | G2 | TQ (torque T_{3,4}) | 1 | 0 |
| 4 | G2 | R1\*(γ) (subset sum S_w(3,4,5)) | 1 | 58 |
| 8 | G3 | LIN | 1 | 0 |
| 12 | G3 | LIN | 1 | 0 |
| 13 | G3 | LIN | 1 | 0 |
| 15 | A2 | P4 | 4 | 1\*, 18, 19, 31\* |
| 15 | A3 | TD (torque T_{0,3,4}) | 1 | 0\* |
| 16 | A2 | P4 | 4 | 20–23 |
| 20 | G3 | LIN | 2 | 0, 2 |
| 23 | G3 | LIN | 1 | 157 |
| 28 | G2 | R1\*(γ) (subset sum S_w(2,3,4)) | 1 | 0 |
| 34 | G3 | LIN | 1 | 0 |
| 35 | G3 | LIN | 1 | 0 |
| 47 | G3 | LIN | 22 | 0–1, 32–35, 37–42, 44–45, 323–324, 342–343, 361–362, 405–406 |
| 53 | G2 | R1\*(γ) (subset sum S_z(1,4,5)) | 1 | 1 |
| 57 | G3 | LIN | 2 | 0–1 |
| 58 | G3 | LIN | 2 | 0–1 |
| 64 | G3 | LIN | 71 | 0, 3–5, 10–12, 17, 19–20, 22–25, 28–29, 32–44, 47–49, 51–52, 54–58, 61, 63–64, 66–69, 72–73, 76–88, 91–93, 95–96, 98–102 |
| 65 | G3 | LIN | 1 | 0 |
| 66 | G3 | LIN | 1 | 0 |
| 110 | G3 | LIN | 1 | 0 |
| 116 | G3 | LIN | 14 | 1, 3, 5, 7–14, 16–18 |
| 117 | G3 | LIN | 2 | 0–1 |
| 119 | G3 | LIN | 1 | 0 |
| 120 | G3 | LIN | 2 | 0–1 |
| 121 | G3 | LIN | 1 | 0 |
| 122 | A2 | LIN (one-signed minor) | 1 | 1 |
| 123 | G3 | LIN | 1 | 0 |
| 124 | A2 | P4 | 128 | 1–10, 12–15, 18, 20–24, 26–29, 31–37, 39–45, 47–82, 84–104, 106–108, 112–120, 122–142 |
| 126 | A2 | P4 | 27 | 0–26 |
| 171 | G3 | LIN | 1 | 13 |
| 172 | G3 | LIN | 6 | 0–5 |
| 173 | G3 | LIN | 1 | 0 |

### 5.2 Residue: 115 cells in 16 classes (M6)

| class (CC) | cells | kind | engine certificate |
|---|---|---|---|
| 62 (40), 63 (52), 14 (14), 30 (16) | 14, 7, 12, 6 | core | label type 11 (4-mass polynomial) |
| 10 (36), 16 (–), 25 (47), 56 (50) | 9, 8, 4, 2 | core | no label (elimination timeout); unit ideal over Q(m) |
| 16 (–) | 4 | core | quartic family without positive zero |
| 4 (31), 28 (86), 53 (95) | 2, 1, 1 | core | R(ab;s); no cell-level hypothesis holds |
| 15 (82) | 1 | core | EQ (type 6) |
| 0 (81) | 1 | core | type 22 (positivity undecided) |
| 64 (100), 4 (31), 23 (46), 25 (47), 116 (101), 15 (82) | 16, 12, 6, 6, 2, 1 | single-term | torques in circled diagrams (§2.6, superseded) |

(Exact list: `data/tables.md`, section "computational residue"; CC labels in `data/per_class_table.md`. The 115
cells lie in 16 classes: 0, 4, 10, 14, 15, 16, 23, 25, 28, 30, 53, 56, 62, 63, 64, 116; `data/counts_v2.json`. The
refereed text said 17.) In this note these cells remain excluded by the engine's certified cores and single-term
certificates. `hand_explanations/RESIDUAL.md` excludes them by hand lemmas as follows: 54 at every positive mass by
cell-level lemmas (B0 38, K 4, L 12); 56 generically by cell-level lemmas (R1\*(α/β) 40, W3 15, EQ2 1); 4
generically by lemmas with one secondary identity each (R1\*(γ) 3, TQ 1); and class 15 cell 0 generically by EQ2
and at every positive mass by the exact certificate TD.

### 5.3 Gaps and limits of this note

- The 1,942 certified cores with label types 5, 6, 7, 8, 10, 11, 15, 16, 22 and the 'no label' / quartic 'none' types
  are not derived by hand (§3.8; 48 of the no-label cores match LIN). All but 72 of their cells are covered by the cell-level lemmas (generic E/E1/R
  lemmas), so the gap concerns the explanation of those particular cores, not the exclusion of the cells.
- Lemma E1, R1, R5, R6 give generic statements: the exceptional set is the union over the 20 triangles T of the zero
  sets of Q_T, R(ab;s)·(second factor), R5, R6·(second factor) and of the signed sums of Lemma Q; these are nonzero
  polynomials, so the exceptional set is a proper real algebraic subset of the positive masses. Within these sets the cells need the finer analysis of
  the five-body paper (Table 1 and §§3.4–8), which is not attempted here.
- The single-term lemmas T, P, C, B hold at every positive mass (they need m_k ≠ 0 and positive partial sums only), but
  the 1,102 single-term cells outside T ∪ P ∪ C ∪ B are explained only generically or are in the residue (of the 43
  residual ones, RESIDUAL.md excludes 42 at every nonzero mass by B0 and K).
- LIN and P4 are templates on engine cores (M4). They are not restated here at the cell level with the secondary
  argmins as certified hypotheses; instead the cells that need them are counted as computational and listed in §5.1.
- Lemma T, P, C, B are statements about one cell at a time, whose hypotheses are checked by script for all cells; they
  are not reduced to a short list of diagrams. Lemma E is the only class-level statement proved here (6 classes).
- The coverage script trusts the parsing of the stored files (`collect_single.py`, `collect_cores.py`); its totals
  agree with GENERIC.md (91,273 cells: 52,432 single-term, 38,841 system cells; 37,808 certified first-pass cores by
  label count, 990 alternative cores, 43 cells without core).

## 6. Files

- `MECHANISMS.md` — this note (v2). `hand_explanations/refereed/MECHANISMS.md` — the refereed version, unchanged.
- Referee report: `hand_explanations/independent/REFEREE_REPORT.md` (its scripts and outputs are in that folder).
- New in v2: `scripts/counts_v2.py` → `data/counts_v2.json`, `data/counts_v2.log` (the classes of the residue, the
  table of §2.1, the never-needed variants and lemmas, the E1 counts of §3.3); `../residual/scripts/tiers_v2.py` →
  `../residual/data/tiers_v2.jsonl`, `../residual/data/tiers_v2_summary.json` (the tiers of §0, §4 and the list of
  §5.1). Both only read stored data.
- `scripts/cellkit.py`, `treeform.py` — cell trees, exponents, tree-only sign test.
- `scripts/lemmas.py` — the combinatorial checkers of Lemmas T, P (`lemma_P2`), C, B, E1, R1, R5, R6, Q.
- `scripts/coreparse.py`, `corefam.py` — parsing of core equations into relations; templates B, LIN, P4 and the
  triangle templates.
- `scripts/coverage.py` → `data/coverage.jsonl`, `data/coverage_summary.json`; `scripts/tables.py` → `data/tables.md`;
  `scripts/cumul.py`; `scripts/per_class_table.py` → `data/per_class_table.md` (the producer was added in v2, RR4;
  the table itself is unchanged).
- `scripts/lpcheck.py` (LP cross-check) → `data/lpcheck_full.log`; `scripts/insitu.py` (Singular in-situ check) →
  `data/insitu.log` (E1, R1, R6, R5) and `data/insitu_Q.log` (Q; RR1); `scripts/check_labels.py` (template labels
  against the engine's labels); `checks/*.sing` (eliminations of the triangle systems).
- Exploration: `explore*.py`, `levels.py` (L1/L2 classification of the first residue), `explain*.py` (LP certificate
  supports), `core_patterns.py`, `core_sigs.py`, `cores_types.py`, `run_*.py`.
- **Run (RR5).** PY = `python3 -I -B` (numpy, highspy, python-flint); PYS = the same
  with a Python that has SymPy, numpy and python-flint.
  Singular must be on the PATH. The commands below are those of the release re-run of 2026-10-17, which reproduced
  the stored outputs byte for byte or up to line order and elapsed-time columns, except where the release notes say
  otherwise; `per_class_table.py` and the log file of the Q run were added after it (RR1, RR4).
  - From the folder `hand_explanations/mechanisms/scripts/` (all Python scripts): `PY collect_single.py`,
    `PY collect_cores.py`, `PY cores_classify1.py`, `PYS cores_types.py`, `PY core_patterns.py`,
    `PYS coverage.py > ../data/coverage.log` (about 5 min), `PY tables.py`,
    `PY per_class_table.py > ../data/per_class_table.md`, `PY counts_v2.py > ../data/counts_v2.log`,
    `PY lpcheck.py 0 > ../data/lpcheck_full.log`,
    `for L in "E1 1000" "R1 1000" "R6 1000" "R5 500"; do PY insitu.py $L; done > ../data/insitu.log`,
    `PY insitu.py Q 300 > ../data/insitu_Q.log`, `PYS check_labels.py`.
  - From the folder `hand_explanations/mechanisms/`: `Singular -q checks/NAME.sing > checks/NAME.out` for NAME =
    factor_E, tri_E1, tri_E1b, tri_R1, tri_R5, tri_R6, tri_variants.
  - `../residual/scripts/tiers_v2.py` is run from `hand_explanations/residual/scripts/` (RESIDUAL.md §12).
