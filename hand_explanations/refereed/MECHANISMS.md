# Why the nonpositive cells of the six-body engine are empty: hand lemmas

*In this supplement: this is the version reviewed in `hand_explanations/independent/REFEREE_REPORT.md`; the corrected note is `hand_explanations/MECHANISMS.md`. Paths of programs and data in this note are relative to `hand_explanations/mechanisms/`.*

Status: 2026-10-17 (PDT). Not refereed. The lemmas of §§2–4 are proved here by hand; the algebra of the triangle
lemmas is also checked symbolically (`checks/*.sing`). Every coverage number is produced by
`scripts/coverage.py` (combinatorial checks of the hypotheses on the stored cell data) and `scripts/tables.py`,
and the single-monomial lemmas are cross-checked cell by cell by an independent LP computation (`scripts/lpcheck.py`).
Nothing under `engine/` was modified.

## 0. Summary

The engine excludes 91,273 nonpositive cells (exponent data with Σx ≤ 0) in 69 diagram classes: 52,432 by a
secondary identity with a single minimal term, 38,841 by an inconsistent subset ("core") of initial forms
certified over Q(m) (37,808 first pass, 990 alternative cores, 43 by the hand proofs of d64/d88/d98).

A short list of local lemmas explains all but 315 of the 91,273 cells; with the whole-class hand proofs of d64, d88
and d98 (refereed), all but 115.

| lemma | mechanism (one line) | masses | cells where it applies |
|---|---|---|---|
| **E** (§3.2) | a zw-triangle with no circle and no other stroke at its vertices forces AK's E(T) (class-level) | generic | 50,399 (6 classes) |
| **E1** (§3.3) | a triangle balanced in one colour at two vertices and in the other colour at one vertex forces E(T) | generic | 86,875 |
| **R1** (§3.4) | a triangle balanced at two vertices with the third at the centre of mass forces AK's R(ab;s) | generic | 57,183 |
| **R5**, **R6** (§3.4) | two further centred-triangle systems; new conditions m_s²(m_a+m_b)³(m_a⁵+m_b⁵) = m_a⁵m_b⁵, m_s²(m_a+m_b)⁴ = m_a m_b⁵ | generic | 35,572; 54,208 |
| **T** (§2.2) | the torque T_J is dominated by its deepest cross pair (tree-only) | all positive | 40,084 |
| **P** (§2.3) | every body has a positive partner pair below the origin, so Σ m_k z_k w_k = E has the single minimal term E | all positive | 13,293 |
| **C** (§2.4) | the subset sum of a cluster has one minimal monomial (a force, or positions with one leading coefficient) | all positive | 46,289 |
| **B** (§2.5) | an isolated binary with x > 0: the relative equation has the single minimal monomial −(m_k+m_l)Z_kl | all positive | 184 |
| **Q** (§3.6) | a body balanced by forces of equal leading coefficients: Σ ε_k m_k = 0 (EQ, "m_a = m_b + m_c") | generic | 2,105 |
| **LIN**, **P4** (§3.5, §3.7) | templates for engine cores: centre-of-mass relations (Σm, H and bilinear labels); the binary torque m_a³+m_b³ (AK Prop. 4) | as label | 368 + 183 (beyond the above) |

Coverage (all 91,273 cells; `data/coverage_summary.json`):
- E or E1 alone: **86,875** cells (95.2%). Adding R1, R6 and Q: 89,256. Adding T and C: 90,407. Adding the core
  templates LIN and P4: 90,958. Adding the whole-class hand proofs of d64, d88 and d98: **91,158**. Residue:
  **115 cells** (17 classes, §5), still resting on the engine's certified cores.
- At every positive mass (not only generically): T, P, C, B and the all-mass templates exclude 68,496 cells,
  including **51,330 of the 52,432 single-term cells** (97.9%).
- Single-term exclusions (task 1): T explains 40,084, P 13,293 (5,355 beyond T), C 29,307 (5,891 beyond T ∪ P); the 1,102
  single-term cells outside T ∪ P ∪ C ∪ B are explained generically by E/E1/R1/R6/Q (1,059) or are in the residue (43).
- Cores (task 2): every certified label type of `label_types.json` is accounted for in §3.8. Hand derivations are
  given for E(T), R(ab;s), H and its bilinear relatives, the partial mass sums, m_a³+m_b³, AK's EQ and
  "m_a = m_b + m_c" from equidistant forces, and the two new conditions R5, R6; the cores carrying these labels are
  35,866 of the 37,808 certified first-pass cores (§3.8).
  The cells of the other label types are, with 72 exceptions, also covered by the cell-level lemmas.

What remains computational (§5): the completeness of the cell enumeration and the exact argmin data of each cell
(the engine's certified LPs), the identification of initial forms of secondary identities for the template lemmas
LIN and P4 (551 cells), and the 115 residual cells.

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
| torque, \|J\| = 3 | δ³ z_k w_l | 5,638 | 5,596 | 882 | 1,995 | 0 | 5,602 | 5,628 | 0 |
| I' = Σ m z w | E | 5,355 | 0 | 5,355 | 0 | 0 | 5,355 | 5,355 | 0 |
| torque of one body | δ³ z_k w_l | 2,723 | 2,419 | 0 | 1,492 | 72 | 2,635 | 2,505 | 28 |
| torque of one body | δ³ w_k z_l | 2,619 | 2,319 | 0 | 1,490 | 22 | 2,553 | 2,497 | 6 |
| torque, \|J\| = 2 | δ³ w_k z_l | 2,320 | 2,156 | 0 | 1,612 | 0 | 2,228 | 2,220 | 8 |
| torque, \|J\| = 2 | δ³ z_k w_l | 2,112 | 1,948 | 0 | 1,476 | 0 | 2,028 | 2,102 | 0 |
| subset sum, \|J\| = 4 | a position | 192 | 0 | 0 | 0 | 0 | 0 | 192 | 0 |

(|J| is min(|J|, 6 − |J|); T_{J^c} = −T_J. The torque of one body is w_k·(z-equation of k) − z_k·(w-equation of k).
The columns give the number of these cells on which each lemma's hypotheses hold; a lemma may use a different identity
than the one the engine recorded first.) The 192 subset sums of four bodies are a triangle plus one body whose
position is balanced by the three forces of the triangle; they are covered generically (E, E1) but by no all-mass
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
(2) Shapes of the witnesses (`data/tables.md`): **outer–outer** (a_p = ζ_pq, b_q = ω_pq; the term is ≈ δ_pq, so
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
  a single term, or consists of positions z_i (i ∈ I) with one common leading coefficient: all i ∈ I have the same
  node v = meet_z(i,O) and lie in one child of v.

Then the initial form of S_J is a nonzero monomial times a positive mass sum; no place has these data (any positive
masses).

*Proof.* Along an edge of (C1), μ_i = e(Z_il) = e(Z_li) = μ_l, resp. μ_i = a_i = a_l = μ_l; so all μ_i equal some
μ. Every term of S_J is a term of exactly one equation of J, so it has exponent ≥ μ, with equality exactly for the
elements of X. If X is one term, Principle 0 applies. Otherwise all z_i, i ∈ I, have the same leading coefficient
ẑ ≠ 0 (the difference of the coordinates of the child containing I and of the child containing O), and the initial
form is (Σ_{i∈I} m_i) ẑ ≠ 0. ∎

The merged case is the "cluster far from the origin must be pulled by an outside force" mechanism; it is also the
content of the engine's most frequent 'none' cores (partial mass sums, §3.5).

### 2.5 Lemma B (binary)

**Lemma B.** Let {k, l} and a colour (z) satisfy A_k^z ⊆ {Z_kl, z_k} with Z_kl ∈ A_k^z, A_l^z ⊆ {Z_lk, z_l} with
Z_lk ∈ A_l^z, and let x_kl > 0 be forced. Then no place has these data (m_k + m_l ≠ 0).

*Proof.* The difference of the two equations reads z_kl = −(m_k+m_l) Z_kl + Σ_{j∉{k,l}} m_j (Z_kj − Z_lj). Here
e(Z_kl) = μ_k = μ_l, e(Z_kj) > μ_k and e(Z_lj) > μ_l for j ∉ {k,l}, and e(z_kl) = ζ_kl > e(Z_kl) because
x_kl > 0. So the only minimal monomial is −(m_k+m_l) δ̂_kl³ ẑ_kl ≠ 0. ∎

An isolated binary must have x = 0 (Kepler: δ̂³ = 1/(m_k+m_l)). Lemma B covers 184 cells, all also covered by T or C;
it is the hand form of the 4,699 'binary' cores (§3.8).

### 2.6 Single-term residue

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
- (H2) B_z := {k ∈ T : A_k^z = {Z_kl, Z_kl'}, {l, l'} = T∖k} and B_w (the same in w) satisfy
  (|B_z| ≥ 2 and |B_w| ≥ 1) or (|B_w| ≥ 2 and |B_z| ≥ 1).

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
(label type 0 of `label_types.json`). (2) Variant: if B_z and B_w are nonempty and A_U = {δ_ab, δ_bc, δ_ca}, the
same conclusion holds (`checks/tri_E1b.sing`, `checks/tri_variants.sing` (a)); by hand: with p as above and the
three closures/U_T written as (Ξ), (Η), (U): x_c p_ab + x_a p_bc + x_b p_ca = 0, the differences (Ξ) − (U) and
(Η) − (U) force p_ca⁴ = p_bc⁴ = p_ab⁴. The variant is never needed for coverage: on every one of the 86,875 cells
where E1 holds, the main hypothesis (H2) holds, and on 65,920 of them all three vertices are balanced in both colours.
(3) Given z-balance at two vertices, U_T is equivalent to (Η); this is why U appears in many E(T) cores in place of a
distance equation. (4) E1 holds on 86,875 cells, including all 50,399 cells of Lemma E.

### 3.4 Centred triangles: Lemmas R1, R5, R6

Say that s ∈ T is **c-centred** (c a colour) if, at the common node v of T in the c-tree, the two other vertices a, b
lie in children of v that contain no other body and not O, while s, O and all bodies outside T lie in one further
child. Then the positions of a, b have exponent h(v) and leading coefficients Y_a, Y_b, every other position has a
larger exponent, so the centre of mass gives **m_a Y_a + m_b Y_b = 0**, and the c-separations of s from a, b have
leading coefficients Y_a, Y_b (the coordinate of the child of s is that of O).

**Lemma R1 (AK's R(ab;s)).** Let T = {a, b, s} satisfy (H1), let a and b be balanced in colour c, and let s be
c-centred. Then Π_{ω³ = 1} [m_s²(m_a+m_b)(m_b + ω m_a)³ − m_a³m_b³] = 0; the factor ω = 1 is
  R(ab;s): m_s² (m_a + m_b)⁴ = m_a³ m_b³.

*Proof (c = w).* Balance at a and b: G_kl = μ m̄_kl, so η_kl = μ m̄_kl / P_kl³ and ξ_kl = P_kl / (μ m̄_kl). Centre:
η_as = Y_a, η_bs = Y_b with m_a Y_a + m_b Y_b = 0, i.e. m_a m_b μ (1/P_bs³ − 1/P_sa³) = 0, so P_sa = ω P_bs,
ω³ = 1. The w-closure m_s/P_ab³ + m_a/P_bs³ + m_b/P_sa³ = 0 gives P_bs³ = −(m_a+m_b) P_ab³ / m_s; write P_bs = κ P_ab
with κ³ = −(m_a+m_b)/m_s. The z-closure P_ab/m_s + P_bs/m_a + P_sa/m_b = 0 (it is U_T) gives
κ(m_b + ω m_a) = −m_a m_b / m_s; cubing, m_s²(m_a+m_b)(m_b + ω m_a)³ = m_a³ m_b³. ∎
Variant: balance at only one of a, b, together with U_T, gives the same polynomial (`checks/tri_variants.sing` (b);
by hand as above: balance at a gives P_as³ = −(m_a+m_b)P_ab³/m_s, then U_T and the z-closure give the cube).

**Lemma R5 (new).** Let T = {a, b, s} satisfy (H1), let a be balanced in colour c, let s be c'-centred in the other
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
coefficients (tinit's variables) are inconsistent at random masses mod 32003 (Singular). All 3,500 checks passed.

The hypotheses of R1/R5/R6 hold on 57,183 / 35,572 / 54,208 cells; beyond E and E1 they add 1,863 (R1) and 456
(R6) cells; R5 adds no cell, but its polynomial is label type 3 (895 cores).

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

### 3.6 Lemma Q (equidistant forces)

**Lemma Q.** Suppose body s's equation in a colour has as minimal terms exactly the forces Z_sk, k ∈ K, |K| ≥ 2, and
all bodies of K lie in one child of one node in each tree, that node being meet(s, k). Then Σ_{k∈K} ε_k m_k = 0 for
some signs ε_k = ±1. For |K| = 2 this is AK's EQ, m_a = m_b at positive masses (label type 18); for |K| = 3, one mass
of K is the sum of the other two (label type 17).

*Proof.* The separations of s from the bodies of K have one common leading coefficient in each colour, ẑ_sk = ẑ,
ŵ_sk = ŵ. By (D_sk), δ̂_sk² = 1/(ẑŵ) for all k, so δ̂_sk = ε_k δ̂. The initial form of the balance is
Σ_k m_k δ̂_sk³ ẑ = δ̂³ ẑ Σ_k ε_k m_k = 0. ∎

Seen from s, the cluster K is a single point; for real configurations all ε_k = 1 and the balance is impossible, but
complex places allow signs. Q holds on 2,105 cells (first applicable on 2); in-situ check: 300 of 300 samples.

### 3.7 Lemma P4 (binary torque; AK Proposition 4, d64 Lemma 2)

**Lemma P4.** Suppose a cell carries: a centre relation m_a Y_a + m_b Y_b = 0 of a pair in colour c (with a third body
s at the c-origin relative to a, b: η_sa = −Y_a, η_sb = −Y_b); a relation κ·(m_a P_sa³ η_sa + m_b P_sb³ η_sb) = 0 with
κ ≠ 0 (the balance of s, or a torque or subset sum with this initial form); and the distance equations of sa and sb
with one common coefficient ξ of the other colour. Then m_a³ + m_b³ = 0, impossible at positive masses.

*Proof.* By (D), P_sk² = −1/(ξ Y_k). So P_sk³ Y_k = −P_sk / ξ and the second relation is m_a P_sa + m_b P_sb = 0.
Squaring, m_a²/Y_a = m_b²/Y_b; with m_a Y_a = −m_b Y_b this gives m_a³ = −m_b³. ∎

All 405 cores of the label m_a³ + m_b³ match this template (`corefam.fam_p4`); as first applicable lemma it is needed
for 183 cells (classes 124, 126, 16, 0, 15).

### 3.8 Label types

Label types of `label_types.json` (positive status) and of the 'none' cores (no positive zero), with the hand
derivation (if any) and the cell-level coverage of the cells that carry them.

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

Cumulative, generic-first: E 50,399 → +E1 86,875 → +R1 88,738 → +R6 89,194 → +Q 89,256 → +T 89,714 → +C 90,407 →
+templates 90,958 → +d-folders 91,158. All-mass-first: T 40,084 → +P 45,439 → +C 68,312 → +templates 68,863 → +E
81,880 → +E1 90,561 → +R1, R6, Q 90,958 → +d-folders 91,158.

Independent checks:
- `scripts/lpcheck.py 0`: for every cell where T, P, C or B holds (40,084 + 13,293 + 46,289 + 184 checks), a
  floating-point LP over the full cell polyhedron (trees, (O1)–(O2), circles, argmin rows) confirms that the claimed
  monomial is strictly below every other term of the identity. All passed.
- `scripts/explore7.py`: the tree-domination criterion (subtree sums) and Lemma T select the same 40,084 cells.
- `scripts/insitu.py`: 3,800 sampled cells for E1, R1, R5, R6, Q (see §3.4, §3.6); all inconsistent mod p.
- `checks/*.sing`: the eliminations of E1 (two variants), R1 (two variants), R5, R6 give exactly the stated
  polynomials (and, for E1, R1, R5, R6, the engine's label types 0, 1, 3, 4).

Per class (`data/per_class_table.md`; CC = Chang–Chen's label; LIN* = the one all-mass LIN cell):

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
2. **Initial forms of secondary identities** for the template lemmas LIN and P4 (551 cells as first applicable): the
   constant argmin sets of subset sums and torques come from tsec_exact's certified LPs. The cell-level lemmas T, P, C,
   B, E1, R1, R5, R6, Q do not use them.
3. The theory inputs listed in GENERIC.md §"Trusted computing base" (the five-body setup at n = 6, the okR rules,
   Lemma U(a), (O1)–(O6)); AK Rule 2e is not needed by these lemmas (E and E1 use the trees directly).

### 5.2 Residue: 115 cells

| class (CC) | cells | kind | engine certificate |
|---|---|---|---|
| 62 (40), 63 (52), 14 (14), 30 (16) | 14, 7, 12, 6 | core | label type 11 (4-mass polynomial) |
| 10 (36), 16 (–), 25 (47), 56 (50) | 9, 8, 4, 2 | core | no label (elimination timeout); unit ideal over Q(m) |
| 16 (–) | 4 | core | quartic family without positive zero |
| 4 (31), 28 (86), 53 (95) | 2, 1, 1 | core | R(ab;s); no cell-level hypothesis holds |
| 15 (82) | 1 | core | EQ (type 6) |
| 0 (81) | 1 | core | type 22 (positivity undecided) |
| 64 (100), 4 (31), 23 (46), 25 (47), 116 (101), 15 (82) | 16, 12, 6, 6, 2, 1 | single-term | torques in circled diagrams (§2.6) |

(Exact list: `data/tables.md`, section "computational residue"; CC labels in `data/per_class_table.md`.) These cells
remain excluded by the engine's certified cores and single-term certificates.

### 5.3 Gaps and limits of this note

- The 1,942 certified cores with label types 5, 6, 7, 8, 10, 11, 15, 16, 22 and the 'no label' / quartic 'none' types
  are not derived by hand (§3.8; 48 of the no-label cores match LIN). All but 72 of their cells are covered by the cell-level lemmas (generic E/E1/R
  lemmas), so the gap concerns the explanation of those particular cores, not the exclusion of the cells.
- Lemma E1, R1, R5, R6 give generic statements: the exceptional set is the union over the 20 triangles T of the zero
  sets of Q_T, R(ab;s)·(second factor), R5, R6·(second factor) and of the signed sums of Lemma Q; these are nonzero
  polynomials, so the exceptional set is a proper real algebraic subset of the positive masses. Within these sets the cells need the finer analysis of
  the five-body paper (Table 1 and §§3.4–8), which is not attempted here.
- The single-term lemmas T, P, C, B hold at every positive mass (they need m_k ≠ 0 and positive partial sums only), but
  the 1,102 single-term cells outside T ∪ P ∪ C ∪ B are explained only generically or are in the residue.
- Lemma T, P, C, B are statements about one cell at a time, whose hypotheses are checked by script for all cells; they
  are not reduced to a short list of diagrams. Lemma E is the only class-level statement proved here (6 classes).
- The coverage script trusts the parsing of the stored files (`collect_single.py`, `collect_cores.py`); its totals
  agree with GENERIC.md (91,273 cells: 52,432 single-term, 38,841 system cells; 37,808 certified first-pass cores by
  label count, 990 alternative cores, 43 cells without core).

## 6. Files

- `MECHANISMS.md` — this note.
- `scripts/cellkit.py`, `treeform.py` — cell trees, exponents, tree-only sign test.
- `scripts/lemmas.py` — the combinatorial checkers of Lemmas T, P (`lemma_P2`), C, B, E1, R1, R5, R6, Q.
- `scripts/coreparse.py`, `corefam.py` — parsing of core equations into relations; templates B, LIN, P4 and the
  triangle templates.
- `scripts/coverage.py` → `data/coverage.jsonl`, `data/coverage_summary.json`; `scripts/tables.py` → `data/tables.md`;
  `scripts/cumul.py`; `data/per_class_table.md`.
- `scripts/lpcheck.py` (LP cross-check), `scripts/insitu.py` (Singular in-situ check), `scripts/check_labels.py`
  (template labels against the engine's labels), `checks/*.sing` (eliminations of the triangle systems).
- Exploration: `explore*.py`, `levels.py` (L1/L2 classification of the first residue), `explain*.py` (LP certificate
  supports), `core_patterns.py`, `core_sigs.py`, `cores_types.py`, `run_*.py`.
- Run: `python3 -I scripts/collect_single.py` and `collect_cores.py`, then
  `cores_classify1.py`, `cores_types.py` (sympy venv), `core_patterns.py`, `coverage.py` (sympy venv: ~5 min), `tables.py`.
