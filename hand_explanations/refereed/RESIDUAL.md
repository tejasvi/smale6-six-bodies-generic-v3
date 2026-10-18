# Hand proofs for the residual nonpositive cells of the six-body engine

*In this supplement: this is the version reviewed in `hand_explanations/independent/REFEREE_REPORT.md`; the corrected note is `hand_explanations/RESIDUAL.md`. Paths of programs and data in this note are relative to `hand_explanations/residual/`.*

Status: 2026-10-16 (PDT). Not refereed. Every lemma below is proved by hand in this note. Scripts (Part 9) check, in
exact arithmetic, (i) that the hypotheses hold on the stored cell data, (ii) the algebra of the proofs, (iii) the
agreement with the engine's labels. Nothing under `engine/` was modified.

Starting point: `hand_explanations/refereed/MECHANISMS.md` explains 91,158 of the 91,273 nonpositive cells by hand lemmas and the
hand proofs of d64/d88/d98; 115 cells (§5.2 there) were left to the engine's certified cores and single-term
certificates. `../labels/LABELS.md` (written concurrently) derives the 23 label types and the 321 `none` cores by
hand; it leaves 25 of the 43 cores without a label (126 cells).

## 0. Summary

**The 115 residual cells are all excluded by hand lemmas.**

| lemma | mechanism (one line) | masses | residual cells |
|---|---|---|---|
| **B0** (§2.1) | a body's equation in one colour is "position = pull of k" with k at the origin's scale, so m_k δ̂³ = 1; the same body's equation in the other colour then puts k at the origin | every mass | 38 single-term |
| **K** (§2.2) | a Kepler binary (x = 0) in one colour forces (m_k + m_l) δ̂³ = 1 and the binary's centre at O in the other colour; a third force on one body cannot be balanced | every mass | 4 single-term |
| **L** (§3) | a three-body central configuration in one colour with one body at the origin's scale and balanced in the other colour: all δ̂³ = 1/M, and the closure m_a m_b ε₁ = m_b(m_a+m_b)ε₂ + m_a(m_a+m_b)ε₃ has no positive solution | every positive mass | 12 core (class 16) |
| **TD** (§8) | class 15 cell 0: the engine's torque T_{0,3,4} has one minimal term, re-certified by 15 explicit inequalities | every mass | 1 single-term |
| **R1\*** (§4) | AK's R(ab;s) for clusters: centre of mass of two clusters (or a subset sum) plus balance at a, b | generic | 43 core |
| **W3** (§5) | a triangle balanced at two vertices whose shape in that colour is fixed by two centre relations | generic | 15 core |
| **EQ2** (§6) | a centred triangle whose non-centre vertex has positions in both colours: m_a M_A² = ± m_b M_B² (AK's EQ) | generic | 1 core (+ class 15 cell 0) |
| **TQ** (§7) | torque of a centred pair against a Kepler pair (AK §5.1, (12)–(13)): positive zeros only on {m_k1 = m_k2, m_l1 = m_l2} | generic | 1 core |

- **Every positive mass: 55 of the 115 cells** (B0 38, K 4, L 12, TD 1). **Generic masses: 60** (R1\* 43, W3 15, EQ2 1,
  TQ 1), each with an explicit nonzero polynomial (Part 4–7 and `data/tables_resid.md`).
- With MECHANISMS.md, **all 91,273 nonpositive cells now have a hand explanation at generic masses.**
- Applied to all cells, the new every-mass lemmas raise the hand coverage **at every positive mass from 68,496 to
  70,406 cells** (+1,579 core cells by L, in classes 3, 129, 130, 132, 133, 149, 150, 16; +331 single-term cells by
  B0, K and TD). In particular 48 of the 49 cells of class 133 and 127 of the 147 cells of class 132 (d98's classes),
  192 of the 224 cells of class 150, 544 of the 630 cells of class 130 and all 28 cells of class 16 are now excluded
  at every positive mass.
- Agreement with the engine (core by core, `data/algebra_resid.jsonl`): the R1\* polynomial **equals** the engine's
  label in all 43 cells (label types 1 and 11); EQ2, TQ and L agree with the engine's labels up to factors without
  positive zeros (types 6, 22 and the quartic `none` family); for the 23 residual cells whose label computation timed
  out (classes 10, 16, 25, 56) W3 and L give the first explicit conditions — L shows that the 8 no-label cells of
  class 16 are excluded at every positive mass.
- Labels (task 2): LABELS.md already derives types 5, 6, 7, 8, 10, 11, 15, 16, 22 and the quartic family; nothing of
  it is repeated here (§10 lists the correspondences). The 25 no-label cores that LABELS.md leaves open (126 cells)
  are all explained here at the cell level: **L 92 cells (every positive mass), R1\* 19, W3 15 (generic)**. Together
  with LABELS.md's N1 (48 cells), all 174 no-label cells have a hand explanation. At the level of the cores themselves
  (§10.1): the 6 "Lagrange" cores force H_L (no positive zero), the 6 fixed-shape cores force H_W, and the 13 class-29
  cores split, through a factorisation of the moment of inertia I, into two LABELS.md K= configurations (types 1, 6,
  16).
- Side observation (found independently, already documented in GENERIC.md and fixed from tag generic-v2): Singular
  4.4.1 has no `sat` unless `elim.lib` is loaded, so the stored runs used unsaturated ideals; unit-ideal certificates
  stay valid. All Singular computations of this note load `elim.lib`.

What remains computational: the cell data (enumeration, trees, argmin sets — as in MECHANISMS.md §5.1) and, for 5
cells, the argmin of one secondary identity, certified here by exact Farkas certificates (§4.2, §7, §8); see §11.

## 1. Setting

Notation as in MECHANISMS.md §1. Colours y, x ∈ {z, w} (x the other one). For a body k, A_k^y is the set of minimal
terms of the y-equation of k on the cell: "pos" (the position y_k) and partners j (the force Y_kj = δ³ y_kj). These
sets are cell data. ŷ_k, ŷ_kl are leading coefficients (nonzero by the place lemma), P_kl = δ̂_kl, Q_kl = P_kl³.
The initial form of the y-equation of k (divided by m_k) is

  in_k^y = [pos ∈ A_k^y] ŷ_k − Σ_{j ∈ A_k^y} m_j Q_kj ŷ_kj = 0.

Trees: the coordinate of a child u of a node v is X_v(u); ŷ_kl = X_v(c(k)) − X_v(c(l)) at v = meet(k,l) and
ŷ_k = X_v(c(k)) − X_v(c(O)) at v = meet(k,O). The **O-child** of v is the child containing O. "k at O" means y_k ≡ 0
(the engine allows it; k then shares the leaf of O).

**Fact O.** Let v = meet_y(l,k) = meet_y(l,O). If k lies in the O-child of v or sits at O, then ŷ_lk = ŷ_l. If k lies
in a child of v other than the O-child, then ŷ_lk = ŷ_l − ŷ_k and ŷ_k ≠ 0.
*Proof.* Coordinates at v; a coordinate difference of two distinct children is nonzero. ∎

**Lemma S (sum of initial forms).** Let K be a set of bodies such that, in colour y, all bodies of K have the same
minimal exponent and every force term of A_k^y (k ∈ K) comes from a body of K. Then
Σ_{k ∈ K, pos ∈ A_k^y} m_k ŷ_k = 0.
*Proof.* Σ_{k∈K} m_k in_k^y = 0. A force term m_k m_j Q_kj ŷ_kj (j ∈ A_k^y, j ∈ K) has exponent e(Y_kj) = e(Y_jk), which is
the common minimal exponent, so k ∈ A_j^y and the partner term m_j m_k Q_jk ŷ_jk = −m_k m_j Q_kj ŷ_kj cancels it. ∎
(In the checker, K is a closed component of the force graph among bodies whose position is minimal and meets O at one
node; then the common exponent is that node's height.)

**Full centre of mass.** If v is the root of T_y, the initial form of Σ m_k y_k = 0 is Σ_u M_u X_v(u) = 0 over the
non-O children u of the root, M_u = total mass below u (the positions below the O-child have larger exponent).

## 2. Two lemmas valid at every mass (42 single-term cells)

### 2.1 Lemma B0

**Lemma B0.** Let k ≠ l and let y, x be the two colours. Suppose
- (i) A_l^y = {pos, k}, v = meet_y(l,k) = meet_y(l,O), and k lies in the O-child of v or sits at O in colour y;
- (ii) A_l^x = {pos, k}, u = meet_x(l,k) = meet_x(l,O), and k lies in a child of u other than the O-child.

Then no place has these data (any nonzero masses).

*Proof.* By (i) and Fact O, in_l^y = ŷ_l − m_k Q_kl ŷ_l = 0, so m_k Q_kl = 1. By (ii) and Fact O,
in_l^x = x̂_l − m_k Q_kl (x̂_l − x̂_k) = x̂_k = 0, against x̂_k ≠ 0. ∎

Physically: seen from l, body k sits at the centre of mass in colour y, so "acceleration = position" fixes
m_k δ̂³ = 1; in colour x the same identity is then violated by the offset of k. The engine excluded these cells by the
torque of the single body l (w_l·(z-equation) − z_l·(w-equation)), whose only minimal term is m_l m_k δ_kl³ times
the y-position of l and the x-position of k: the same computation.

Residual cells (38): class 64 (16; l, k = 2, 3 or 3, 2, the z-stroke 23), class 4 (8; the pair 01), class 25 (6) and
class 23 (6) (pairs 14, 23, 05), class 116 (2; pair 05).

### 2.2 Lemma K

**Lemma K.** Let k ≠ l and colours y, x. Suppose
- (i) A_k^y = {pos, l}, A_l^y = {pos, k}, and k, l, O lie in three distinct children of one node of T_y;
- (ii) k, l, O lie in three distinct children of one node of T_x; for {p,q} = {k,l}: A_p^x = {pos, q} and
  A_q^x = {pos, p, j} for one body j ∉ {k,l}.

Then no place has these data (any nonzero masses).

*Proof.* (i): Lemma S gives m_k ŷ_k + m_l ŷ_l = 0; then in_k^y = ŷ_k − m_l Q (ŷ_k − ŷ_l) = ŷ_k (1 − (m_k+m_l) Q), so
(m_k + m_l) Q = 1 (Kepler; Q = Q_kl). (ii): in_p^x = 0 gives x̂_p (1 − m_q Q) = −m_q Q x̂_q, i.e. (as 1 − m_q Q = m_p Q)
m_p x̂_p + m_q x̂_q = 0.
Then in_q^x = x̂_q (1 − (m_k + m_l) Q) − m_j Q_qj x̂_qj = −m_j Q_qj x̂_qj ≠ 0. ∎

Residual cells (4): class 4 cells 23, 24, 43, 44 (binary 01, Kepler in w; the extra force on 0 or 1 comes from 3 or 4).

## 3. Lemma L: Lagrange triangle (every positive mass; 12 core cells)

**Lemma L.** Let T = {a, b, s} and colours y, x. Suppose
- (L1) in T_y, a, b, s lie in three distinct children of one node v, none of them the O-child, and
  A_k^y = {pos} ∪ (T ∖ k) for k ∈ T (a three-body central configuration at leading order);
- (L2) in T_x, a, b, s lie in three distinct children of one node v̄; s lies in the O-child (or at O), a, b do not;
  meet_x(a,O) = meet_x(b,O) = v̄; A_s^x = {a, b}, A_a^x = {pos, s, b}, A_b^x = {pos, s, a}.

Then m_a m_b ε₁ − m_b(m_a+m_b) ε₂ − m_a(m_a+m_b) ε₃ = 0 for some cube roots of unity ε_i. This is impossible for
positive m_a, m_b. The product over the εs is
  H_L = (m_a² + m_a m_b + m_b²)³ (m_a⁴ − m_a³m_b + 2m_a m_b³ + m_b⁴)(m_a⁴ + 2m_a³m_b − m_a m_b³ + m_b⁴)
        (m_a⁴ + 5m_a³m_b + 9m_a²m_b² + 5m_a m_b³ + m_b⁴).

*Proof.* Write X_k = ŷ_k (k ∈ T), so ŷ_kl = X_k − X_l, X_k ≠ 0, X_k pairwise distinct; Y_a = x̂_a, Y_b = x̂_b, so by
Fact O x̂_as = Y_a, x̂_bs = Y_b, x̂_ab = Y_a − Y_b.
1. Lemma S in colour x on T (common exponent: the forces of the three pairs): m_a Y_a + m_b Y_b = 0.
2. in_s^x = m_a Q_as Y_a + m_b Q_bs Y_b = 0 and step 1 give m_a Y_a (Q_as − Q_bs) = 0: Q_as = Q_bs =: Q.
3. Lemma S in colour y on T: m_a X_a + m_b X_b + m_s X_s = 0.
4. in_s^y = X_s − Q(m_a(X_s − X_a) + m_b(X_s − X_b)) = X_s − Q (m_a+m_b+m_s) X_s by step 3; X_s ≠ 0, so Q = 1/M,
   M = m_a + m_b + m_s.
5. in_a^x = Y_a (1 − m_s Q) − m_b Q_ab (Y_a − Y_b) = Y_a (m_a+m_b)(1/M − Q_ab) by step 1: Q_ab = 1/M.
6. So P_kl = ε'_kl M^{-1/3} with ε'³ = 1 on all three sides, and P_kl^{-2} = ε'_kl M^{2/3}.
7. (D_kl) gives ŷ_kl = 1/(P_kl² x̂_kl). The y-closure ŷ_ab + ŷ_bs + ŷ_sa = 0, with x̂_ab = Y_a (m_a+m_b)/m_b,
   x̂_bs = −(m_a/m_b) Y_a, x̂_sa = −Y_a, multiplied by m_a (m_a+m_b) Y_a M^{-2/3}, is
   m_a m_b ε'_ab − m_b (m_a+m_b) ε'_bs − m_a (m_a+m_b) ε'_sa = 0.
8. Positive masses: put A = m_a m_b, B = m_b(m_a+m_b), C = m_a(m_a+m_b). Then A = |B ε₂ + C ε₃|. If ε₂ = ε₃ the
   right side is B + C = (m_a+m_b)² > A. If ε₂ ≠ ε₃ it is (B² + C² − BC)^{1/2} ≥ (BC)^{1/2} = (m_a+m_b)(m_a m_b)^{1/2} > A.
   The product over ε₂, ε₃ (ε₁ = 1 by homogeneity) is (A³ − B³ − C³)³ − 27A³B³C³ = −H_L; the quartic
   factors have no positive zero (t⁴ − t³ + 2t + 1 > 0 for t > 0, and its reverse; the third has positive
   coefficients). ∎

Each step is an exact identity checked in `checks/L_steps.py`. The blind elimination of the full system does not
finish in 20 minutes; the step-by-step check replaces it.

Residual cells: all 12 cells of class 16 (diagram 23:1 24:1 34:1 15:2 zc234 wc15; y = z, T = {2,3,4}, s = the vertex
in the O-child of the w-node: s = 3 in cells 0, 2, 12, 14; s = 4 in 16, 18, 24, 26; s = 2 in 4, 6, 8, 10). For cells
4–10 the engine's label (the quartic `none` family, LABELS.md N4) is H_L/(m_a²+m_am_b+m_b²)² with (a,b) = (3,4); for
the other 8 cells the label computation had timed out. All 12 are excluded at every positive mass.

Lemma L is the cell-level form of LABELS.md's core-level Lemma N4 (which uses a different subset of these equations).
It applies to 2,111 of the 91,273 cells (`data/global_cover.jsonl`), e.g. in class 3 to the triangle of the three
free bodies {0,1,2} at x = 0 (z-positions at the root, one of them at O in w), independently of the zw-triangle {3,4,5}
used by Lemma E; 1,579 of these cells were not excluded at every positive mass by the lemmas of MECHANISMS.md.

## 4. Lemma R1\*: centred triangle with clusters (generic; 43 core cells)

**Lemma R1\*.** Let T = {a, b, s} and colours y (centre and balance colour), x. Suppose
- (R1) a, b, s lie in three distinct children of one node v of T_y and of one node v̄ of T_x;
- (R2) s lies in the O-child of v (or at O); a, b lie in children A ≠ B of v other than the O-child;
- (R3) a and b are balanced in y: A_a^y = {s, b}, A_b^y = {s, a};
- (R4) a centre relation M_A X(A) + M_B X(B) = 0 holds between the coordinates of A and B (relative to the O-child),
  with M_A, M_B sums of masses, by one of
  - (α) v is the root of T_y and has exactly three children: the full centre of mass, M_A, M_B = masses below A, B;
  - (β) v is the root, and the bodies of its other non-O children form Lemma-S sets: full centre minus those sets;
  - (γ) a subset sum S_J^y whose minimal terms on the cell are exactly the positions of the bodies of J below A or B
    (exact certificate, §4.2): M_A = mass of J below A, M_B = mass of J below B.

Then N(m_a, m_b, m_s, M_A, M_B) = 0, where (with κ a new variable)

  N = Res_κ( M_A m_b κ³ − M_B m_a ,  m_s² (M_A + M_B)(m_a + m_b κ)³ − m_a³ m_b² M_B ) / (m_a³ m_b³),

an irreducible polynomial of degree 18. For M_A = m_a, M_B = m_b it is AK's R(ab;s) = m_s²(m_a+m_b)⁴ − m_a³m_b³ times the
degree-12 factor (label type 1); for M_B = m_b, M_A = m_a + m_p it is label type 11 ("kite with a rider").

*Proof (as R1 of MECHANISMS.md, with clusters).* Orient T cyclically (ab, bs, sa); m̄_kl is the mass of the third vertex.
Balance at a and b (R3) gives G_kl := Q_kl ŷ_kl = λ m̄_kl on the three sides (λ ≠ 0), so ŷ_kl = λ m̄_kl / Q_kl. By (R2)
and Fact O, ŷ_as = X(A), ŷ_bs = X(B). The centre relation −M_A λ m_b/Q_sa + M_B λ m_a/Q_bs = 0 gives
P_bs³ = (M_B m_a/(M_A m_b)) P_sa³; normalise P_sa = 1, P_bs = κ with M_A m_b κ³ = M_B m_a. The y-closure
Σ ŷ_kl = 0 reads m_s/Q_ab + m_a/κ³ + m_b = 0, i.e. m_s/P_ab³ = −m_b (M_A + M_B)/M_B. By (D_kl),
x̂_kl = 1/(P_kl² ŷ_kl) = P_kl/(λ m̄_kl), and the x-closure (R1) is P_ab/m_s + κ/m_a + 1/m_b = 0, so
P_ab = −m_s (m_a + m_b κ)/(m_a m_b). Cubing and comparing: m_a³ m_b² M_B = m_s² (M_A + M_B)(m_a + m_b κ)³. The norm over
the three κ is the resultant. ∎

`checks/R1star.sing`: the elimination ideal of this system (masses and M_A, M_B as variables, saturated by the
coordinates) is principal and generated by N; N·m_a³m_b³ is the hand resultant; the specialisation gives type 1.

Relation to LABELS.md: N is LABELS.md's Λ_κ-resultant (Lemma K=, conclusions (i)–(iii)) with riders on both a and b.
The difference here is the level: the hypotheses (R1)–(R4) are checked on the cell, not on the engine's core.

### 4.1 Residual cells

| class | cells | y | (a, b, s) | M_A, M_B | centre |
|---|---|---|---|---|---|
| 62 | 14 | w | (1, 5, 4) | m1, m0+m5 | (α) |
| 63 | 7 | w | (1, 5, 4) | m1, m0+m5 | (α) |
| 14 | 12 | z | the z-triangle {2,3,4}; the vertex paired with body 0 carries m0 | m_a+m0 or m_b+m0 | (α) |
| 30 | 6 | z | (2, 3, 5) | m2+m0 or m3+m0 | (α) |
| 4 | 1 (cell 8) | w | (3, 4, 5) | m3, m4 | (β), Lemma-S set {0,1} |
| 4, 28, 53 | 1+1+1 (cells 58, 0, 1) | w, w, z | (3,4,5), (2,3,4), (1,4,5) | single masses | (γ) |

In all 43 cells the instantiated N equals the engine's label of the cell's core (types 11 and 1).

### 4.2 The subset sums of (γ)

For class 4 cell 58 (S_w(3,4,5)), class 28 cell 0 (S_w(2,3,4)) and class 53 cell 1 (S_z(1,4,5)), the minimal terms of
the subset sum are exactly the positions of a and b on the whole cell. Reason, uniform in the three cells (the
certificates in `data/certificates.txt` are exactly this): every cross pair ij (i ∈ T, j ∉ T) meets at the root of the
other colour's tree, whose height is −2 (a circle in that colour); hence e(W_ij) = 3 − ω_ij/2 (resp. 3 − ζ_ij/2 for z);
(O1) on a pair meeting at v gives h(v) < 2, and the tree gives ω_ij ≤ h(v), so e(W_ij) ≥ 3 − h(v)/2 > h(v); the position
of s lies deeper than v (tree). Each of the 30 inequalities is certified by a combination of at most five cell
constraints, with nonnegative multipliers on the inequalities.

## 5. Lemma W3: balanced triangle with a fixed shape (generic; 15 core cells)

**Lemma W3.** Let T = {a, b, c} and colours y (balance and shape colour), x. Suppose
- (W1) a, b, c lie in three distinct children of one node v of T_y and of one node of T_x, none in the O-child of v;
- (W2) two vertices of T are balanced in y;
- (W3) the coordinates of the non-O children of v satisfy linear relations (the full centre of mass if v is the root,
  and Lemma S at v) whose solution space, restricted to the three children of T, is one-dimensional:
  (ŷ_a, ŷ_b, ŷ_c) = t (e_a, e_b, e_c), e_k ∈ Q[m].

Then, with u₁ = m_c² (e_a − e_b), u₂ = m_a² (e_b − e_c), u₃ = m_b² (e_c − e_a),

  H_W = (u₁u₂ + u₂u₃ + u₃u₁)³ − 27 (u₁u₂u₃)² = 0.

*Proof.* As in E1, two balances give G_kl = Q_kl ŷ_kl = λ m̄_kl on the cyclically oriented sides, so
Q_kl = λ m̄_kl/(t (e_k − e_l)). By (D_kl), x̂_kl = 1/(P_kl² ŷ_kl) = P_kl/(λ m̄_kl), and the x-closure (W1) is
Σ_cyc P_kl/m̄_kl = 0, a sum of three cube roots α + β + γ = 0 with α³ = λ/(t u₁), β³ = λ/(t u₂), γ³ = λ/(t u₃).
Then α³ + β³ + γ³ = 3αβγ, so (1/u₁ + 1/u₂ + 1/u₃)³ = 27/(u₁u₂u₃), which is H_W = 0. ∎

`checks/W3.sing`: with e_a, e_b, e_c as free parameters, the elimination ideal is exactly (H_W).

This is the analogue of LABELS.md's Lemma K= (centre of mass and equilibrium in one colour) when no vertex of T is at
the origin's scale, so that two centre relations are needed to fix the shape; it differs from LABELS.md's K≠ (centre in
one colour, equilibrium in the other).

Residual cells (no engine label; all three diagrams have a zw-triangle T with all vertices z-circled, balanced in w):

| class | cells | T | relations | shape (e_k for the three children of T) |
|---|---|---|---|---|
| 10 | 9 | {3,4,5} | full; Lemma S {1,2} | e₃ = m2m5 − m1m4, e₄ = m1m3, e₅ = −m2m3 |
| 25 | 4 | {3,4,5} | full; Lemma S {0,2}, {0,1,2}, {0,1}, {1,2} (one per cell) | e.g. e₃ = m0m4 − m1m5, e₄ = m2m5 − m0m3, e₅ = m1m3 − m2m4 |
| 56 | 2 | {1,4,5} | full; Lemma S {0,2,3} | e₁ = m5(m2+m3) − m0m4, e₄ = m0m1, e₅ = −m1(m2+m3) |

H_W has degree 24 and is nonzero in every cell; it changes sign on the positive orthant, so this is a generic exclusion.

## 6. Lemma EQ2 (AK's EQ; generic; class 15)

**Lemma EQ2.** Let T = {s, a, b} and colours y (centre colour), x. Suppose
- (E1) a, b, s lie in three distinct children of one node v of T_y and of one node v̄ of T_x; s lies in the O-child at
  v and at v̄ (or at O); a, b do not;
- (E2) a centre relation M_A ŷ_a + M_B ŷ_b = 0 at v (full centre of mass or Lemma S);
- (E3) s is balanced in y: A_s^y = {a, b};
- (E4) A_a^y = {pos, s, b} and A_a^x = {pos, s, b}, with meet_y(a,O) = v, meet_x(a,O) = v̄.

Then m_a² M_A⁴ = m_b² M_B⁴. For M_A = m_a, M_B = m_b: m_a⁶ = m_b⁶ with m_a + m_b ≠ 0, i.e. label type 6
(m_a⁶ − m_b⁶)/(m_a + m_b); at positive masses, m_a = m_b.

*Proof.* With Y_k = ŷ_k, X_k = x̂_k (k = a, b), Fact O gives ŷ_sa = −Y_a, ŷ_ab = Y_a − Y_b, and the same in x.
in_a^y: Y_a (1 − m_s Q_sa) = m_b Q_ab (Y_a − Y_b); in_a^x: X_a (1 − m_s Q_sa) = m_b Q_ab (X_a − X_b). If 1 − m_s Q_sa = 0,
then Y_a = Y_b; so dividing, X_b Y_a = X_a Y_b. With (E2), Y_b = −(M_A/M_B) Y_a and X_b = −(M_A/M_B) X_a. (E3):
m_a Q_sa Y_a + m_b Q_sb Y_b = 0 gives ρ³ = m_a M_B/(m_b M_A) for ρ = P_sb/P_sa; (D_sa), (D_sb): P_sa² X_a Y_a = 1 =
P_sb² X_b Y_b give ρ² = M_B²/M_A². Hence ρ = m_a M_A/(m_b M_B) and ρ² = M_B²/M_A², i.e. m_a² M_A⁴ = m_b² M_B⁴. If
M = m, the factor m_a + m_b = 0 would give X_a = X_b by (E2). ∎

`checks/EQ2.sing`: the elimination ideal is (m_a² M_A⁴ − m_b² M_B⁴). This is LABELS.md's Lemma X6 shape 6.1
(W_u, W_a, Z_a), with clusters allowed.

Residual cells: class 15 cell 30 (core; y = z, (s,a,b) = (2,3,4), centre m3 ŷ_3 + m4 ŷ_4 = 0 from the z-root): the
engine's label (type 6) divides m3⁶ − m4⁶. Class 15 cell 0 (single-term) satisfies the same hypotheses; it is also
excluded at every mass by TD (§8).

## 7. Lemma TQ: torque of a centred pair (generic; class 0 cell 0)

**Lemma TQ.** Bodies l₁, l₂, k₁, k₂ and colours y, x. Suppose
- (T1) the root of T_y has exactly three children: the O-child (containing k₁, k₂) and two children containing only
  l₁, resp. only l₂ — so m_{l₁} Y₁ + m_{l₂} Y₂ = 0 for Y_j = ŷ_{l_j};
- (T2) in T_x, k₁, k₂, O lie in three distinct children of v̄ = meet_x(k₁,k₂), {k₁,k₂} is a Lemma-S set
  (m_{k₁} X₁ + m_{k₂} X₂ = 0, X_i = x̂_{k_i}), and l₁, l₂ lie in the O-child of v̄;
- (T3) the torque T_{l₁,l₂} has as minimal terms on the cell exactly the four terms δ³ y_l x_k (l ∈ {l₁,l₂},
  k ∈ {k₁,k₂}) (exact certificate, `data/certificates.txt`).

Then ε₁₁ (m_{k₁}m_{l₁})^{3/2} + i ε₁₂ (m_{k₁}m_{l₂})^{3/2} + i ε₂₁ (m_{k₂}m_{l₁})^{3/2} + ε₂₂ (m_{k₂}m_{l₂})^{3/2} = 0 for
some signs; at positive masses m_{k₁} = m_{k₂} and m_{l₁} = m_{l₂}. The product over the signs is
(n₁² − n₁n₂ + n₂²)(M₁² − M₁M₂ + M₂²)·S(n, M), S the sextic of label type 22 (n = masses of k, M = masses of l).

*Proof.* By Fact O, ŷ_kl = −Y_l and x̂_kl = X_k, so (D_kl) gives P_kl² = −1/(X_k Y_l), and the initial form of the
torque Σ m_k m_l Q_kl Y_l X_k = −Σ m_k m_l P_kl = 0. Put u = −X₁Y₁; then P₁₁² = 1/u, P₁₂² = −m_{l₂}/(m_{l₁}u),
P₂₁² = −m_{k₂}/(m_{k₁}u), P₂₂² = m_{k₂}m_{l₂}/(m_{k₁}m_{l₁}u); multiply the torque by (u m_{k₁} m_{l₁})^{1/2}. For positive
masses the real and imaginary parts vanish separately: m_{k₁}m_{l₁} = m_{k₂}m_{l₂} and m_{k₁}m_{l₂} = m_{k₂}m_{l₁},
so m_{l₁} = m_{l₂} and m_{k₁} = m_{k₂}. ∎

`checks/TQ.sing` gives the product. It is LABELS.md's Lemma T (AK §5.1, (12)–(13)); the engine's label of the cell
(type 22, status `undec`) is this product times (n₁+n₂)(M₁+M₂). Class 0 cell 0: y = z, (l₁,l₂) = (3,4), (k₁,k₂) =
(0,1); excluded at every positive mass off the codimension-2 set {m0 = m1, m3 = m4}.

## 8. Class 15 cell 0 at every mass (TD)

The engine excluded this single-term cell by the torque T_{0,3,4} with the single minimal term δ_02³ w_0 z_2 (body 0
is a satellite of body 2, which sits at O in w). This is re-certified here in exact arithmetic: each of the 15 other
terms of T_{0,3,4} is strictly larger on the whole cell, by a combination of at most nine cell constraints (nonnegative
multipliers on the inequalities)
(`data/certificates.txt`; they use the argmin of the w-equation of 2, of the z-equation of 0, the circles of 1, 3,
the strokes 15, 23 and (O1)). The leading coefficient −m0 m2 P02³ ŵ_0 ẑ_2 is nonzero, so T_{0,3,4} ≢ 0: no place, at
any nonzero masses. No structural lemma is given for this cell; Lemma EQ2 gives an independent hand proof at generic
masses (m3 ≠ m4).

## 9. Verification (all exact; one CPU core)

1. **Hypotheses on the cell data** (`scripts/lemmas_resid.py`, driver `scripts/run_resid.py`): the argmin sets of the
   base identities and the trees are read from `cells.jsonl`; all checks are combinatorial, except the five
   secondary-identity claims (three subset sums, two torques), which are proved by exact Farkas certificates
   (`scripts/exactlp.py`: the cell polyhedron of tengine/texact rebuilt with Fractions, an exact simplex, and an exact
   re-verification of every certificate). Sanity: `scripts/test_exactlp.py` re-certifies the engine's single-term
   claim on all 43 residual single-term cells and checks that every stored interior point lies in its cell.
2. **In situ** (`scripts/insitu_resid.py`): for every residual cell and every lemma that applies to it, the relations
   used by the lemma, written in the cell's own variables (tinit.py conventions), are inconsistent at random masses
   mod 32003 (Singular, saturation by all separations and positions used): **294 of 294** (two mass seeds each).
   `scripts/insitu_sample.py`: 150 random cells each where B0, K, L, W3, EQ2, R1\* apply among all 91,273 cells:
   **900 of 900**.
3. **Algebra**: `checks/R1star.sing`, `W3.sing`, `EQ2.sing`, `TQ.sing` (eliminations in role variables, masses as
   variables: the elimination ideals are generated by the hand polynomials); `checks/L_steps.py` (each step of
   Lemma L as an exact identity, the norm identity, the factorisation of H_L, and the engine's label of class 16
   cell 4 dividing H_L).
4. **Agreement with the engine** (`scripts/algebra_resid.py`, sympy): per cell, the hand polynomial is nonzero, and is
   compared with the engine's label of the cell's core (labels_all.jsonl by core hash): R1\* equal in 43/43; EQ2 and
   L: the label divides ours (extra factors without positive zeros); TQ: ours divides the label; W3 and 8 L-cells:
   no engine label.
5. **No-label cores** (§10.1): `checks/coreA_steps.py` (family A, exact identities), `checks/coreA_num.sing` and
   `scripts/coreAB_num.py` (the 12 cores of families A and B on the engine's own equations at numeric masses, family A
   also at m_a = m_b: all unit ideals), `checks/coreB.sing` (family B: elimination ideal = (H_W)),
   `scripts/coreC.py` → `data/coreC_part1.txt`, `data/coreC_part2.txt` (family C: factorisation of I and one
   elimination per branch), summarised by `scripts/coreC_table.py` → `data/coreC_table.md`.

## 10. Coverage

| | cells | every positive mass | generic | lemmas |
|---|---|---|---|---|
| residual single-term (MECHANISMS §2.6) | 43 | 43 | — | B0 38, K 4, TD 1 |
| residual core (MECHANISMS §5.2) | 72 | 12 | 60 | L 12; R1\* 43, W3 15, EQ2 1, TQ 1 |
| all nonpositive cells | 91,273 | 70,406 (was 68,496) | 91,273 (was 91,158) | + MECHANISMS.md, d64/d88/d98 |

Per residual class and engine label: `data/tables_resid.md`. The 72 residual core cells by engine label: type 11
(L17, 39 cells: R1\*), no label (L16, 23 cells: W3 15, L 8), quartic `none` (L21, 4 cells: L), R(ab;s) (L3, 4 cells:
R1\*), type 6 (1: EQ2), type 22 (1: TQ).

**Label types (task 2).** LABELS.md derives all 23 types of `label_types.json` and the 321 `none` cores by hand,
including the types listed as open in MECHANISMS.md (5, 6, 7, 8, 10, 11, 15, 16, 22) and the quartic family; it is not
repeated here. Correspondences with the lemmas of this note: type 1 and 11 = R1\* (LABELS K=); type 6 = EQ2 (LABELS X6,
shape 6.1); type 22 = TQ (LABELS T); quartic `none` = L (LABELS N4, core level). The cores without a label:

| no-label cores | cores | cells | classes (first lemma in MECHANISMS) | cell level (this note) | core level (§10.1) |
|---|---|---|---|---|---|
| centre-of-mass on one value (LABELS N1) | 18 | 48 | 128 (C, E1), 148 (E) | — | LABELS.md §4.6: Σ m_i, every positive mass |
| A: Lagrange triangles | 6 | 92 | 133 (32, d98), 150 (32, E), 132 (12, d98), 130 (8, C/E1), 16 (8, residual) | Lemma L: every positive mass | H_L(m_a, m_b): no positive zero |
| B: fixed-shape balanced triangles | 6 | 15 | 10, 25, 56 (residual) | Lemma W3: generic | H_W, the same polynomial |
| C: class 29, two triangles coupled by I | 13 | 19 | 29 (E1) | R1\* on the z-triangle {2,3,5} (s = 5): R(23;5) in 17 cells, with body 0 as a rider in 2 (E1 also applies): generic | product of two K= conditions (types 1, 6, 16) |

So all 174 no-label cells have a hand explanation at the cell level (48 by N1, 92 by L at every positive mass, 34
generic), and all 43 no-label cores have a hand-derived necessary condition at the core level (§10.1).

### 10.1 Core-level conditions of the 25 remaining no-label cores

Here the relations are those of the engine's core itself (as in LABELS.md), not of the whole cell.

**Family A (6 cores, 92 cells).** Up to renaming and the exchange of colours, the core consists of: in colour x, s in the
O-child of the node of T = {a,b,s} and S_x: m_a x̂_a + m_b x̂_b = 0; in colour y, S_y: m_a ŷ_a + m_b ŷ_b + m_s ŷ_s = 0
(three positions); D on the three sides; x[a] with position, x[s] balanced, y[a] with position (the cores hash
96674494358ac0b5, 7c60897cf0a47385 (classes 133, 150), 6fd2e5810bbf2a5f, 9a753c1a541ced1d (130, 132, 133),
ba6b8555b3facbb0, 1e2248294818e876 (16)). **Claim: H_L(m_a, m_b) = 0, which has no positive zero.**
*Proof.* As in Lemma L, x[s] and S_x give Q_as = Q_bs, and x[a] gives 1 − m_s Q_as = N Q_ab (N = m_a + m_b). Normalise
x̂_a = 1 and put P_bs = ω P_as (ω³ = 1), P_ab = σ P_as. The y-closure with D gives σ² = m_a m_b ω²/(N(m_a ω² + m_b)).
y[a] gives ŷ_a = P_as (m_s + m_b² σ/N); S_y gives M ŷ_a = m_s/P_as² + m_b²/(N σ² P_as²); x[a] gives
P_as³ (m_s + N σ³) = 1. Eliminating P_as³: −m_s (σ³ − 1)(N² σ² − m_b²) = 0. Moreover the y-position of s is
ŷ_s = σ (m_b² − N² σ²)/(N (m_s + N σ³) P_as²), which is nonzero; so N²σ² ≠ m_b² (that branch would be AK's EQ,
m_a⁶ = m_b⁶) and σ³ = 1, i.e. m_a³ m_b³ = N³ (m_a ω² + m_b)³. Its norm over ω is −H_L. ∎
(`checks/coreA_steps.py`: each step as an exact identity, the ŷ_s formula, the norm. The blind elimination does not
finish in 25 minutes; `checks/coreA_num.sing` and `scripts/coreAB_num.py`: the six cores are inconsistent at random
masses and also at masses with m_a = m_b, as the claim predicts.) So these six cores force the same polynomial as
LABELS.md's quartic family N4, whose cores contain the y-equation of s instead of that of a (N4's proof then gets
P³ = 1/M directly, as in step 4 of Lemma L); here the EQ branch has to be removed by ŷ_s ≠ 0.

**Family B (6 cores, 15 cells).** The core consists of two centre relations that fix the y-shape of T up to scale,
U_T, D on the three sides and one y-balance (at a, say). **Claim: H_W = 0** (the polynomial of Lemma W3).
*Proof.* Normalise P_ca = 1. The balance at a gives P_ab = κ with m_b (e_a − e_b) κ³ + m_c (e_a − e_c) = 0; U_T gives
P_bc = −m_a (m_b κ + m_c)/(m_b m_c); the x-closure with D gives
m_a²(m_bκ + m_c)²(e_b − e_c)(e_c − e_a) + κ² m_b² m_c² (e_a − e_b)(e_c − e_a) + κ² m_a² (m_bκ + m_c)² (e_a − e_b)(e_b − e_c) = 0.
The resultant in κ is −m_b² m_c² (e_a − e_b)² (e_a − e_c)² H_W. ∎ (`checks/coreB.sing`: the elimination ideal of this
system, with e_a, e_b, e_c free, is exactly (H_W), the same generator as for Lemma W3.)

**Family C (13 cores, 19 cells; class 29: z-triangle T' = {2,3,5}, w-triangle T = {1,4,5}, body 5 shared).** Each core
contains the initial form of I, Σ m_k m_l ẑ_kl ŵ_kl over the four pairs of {1,4} × {2,3}. Body 5 is in the O-child of
both triangles' nodes, 1 and 4 are in the O-child of the z-root, and 2, 3 in the O-child of the w-node of T, so
ẑ_kl = −ẑ_l and ŵ_kl = ŵ_k (k ∈ {1,4}, l ∈ {2,3}) and **I = −(m₂ẑ₂ + m₃ẑ₃)(m₁ŵ₁ + m₄ŵ₄)** (in four cores body 0 is a
rider in one factor: m₀ẑ₀ or m₀ŵ₀ is added; the factorisation was computed for each core, `data/coreC_part*.txt`).
The first factor is the centre relation of T' (s = 5), the second that of T
(s = 5). In each branch the core contains one of LABELS.md's Lemma K= configurations on that triangle: two balances and
U_T, V_T or D on the three sides give R(ab;5)·μ₁₅ (type 1, cases (i), (ii)); two balances, D_as, D_bs and one balance
in the other colour give AK's EQ (type 6, case (iv)), with a rider m_b³ = ±m_a(m_a + m₀)² (type 16). The core's
condition is the product of the two. Per core:

| core | cells | relations besides I | branch m₂ẑ₂+m₃ẑ₃(+m₀ẑ₀) = 0 (T′) | branch m₁ŵ₁+m₄ŵ₄(+m₀ŵ₀) = 0 (T) | whole branch eliminated |
|---|---|---|---|---|---|
| 9c5d5a0eb5274caf | 3 | D15 D45 U D25 z[2] z[3] w[1] w[4] z[1] | type 1 (m2,m3,m5) | type 6 (m1,m4) | same, same |
| c1343e65a5f12f68 | 3 | D25 D35 U D15 z[2] z[3] w[1] w[4] w[2] | type 6 (m2,m3) | type 1 (m1,m4,m5) | same, same |
| 9d52073c7df67ada | 2 | D15 D45 V235 D25 z[2] z[3] w[1] w[4] z[1] | type 1 (m2,m3,m5) | type 6 (m1,m4) | same, same |
| a7135526b888cf20 | 2 | D25 D35 V145 D15 z[2] z[3] w[1] w[4] w[2] | type 6 (m2,m3) | type 1 (m1,m4,m5) | same, same |
| f88fb651a732d579 | 1 | D15 D25 D35 D45 z[2] z[3] w[1] w[4] z[1] w[2] | type 6 (m2,m3) | type 16 (m0,m1,m4) | same, same |
| 854f9cb97f452836 | 1 | U D15 D25 D45 z[2] z[3] w[1] w[4] D14 | type 1 (m2,m3,m5) | type 1 (m1,m4,m5) | timeout, timeout |
| a942ebc464768f1a | 1 | D25 D35 D15 D45 z[2] z[3] w[1] w[4] w[2] D14 | type 6 (m2,m3) | type 1 (m1,m4,m5) | same, timeout |
| 9dc44c4284b43aee | 1 | D15 D25 D35 D45 z[2] z[3] w[1] w[4] z[1] w[2] | type 6 (m2,m3) | type 6 (m1,m4) | same, same |
| 2e39da8594e724c4 | 1 | D15 D25 D35 D45 z[2] z[3] w[1] w[4] D14 D23 | type 1 (m2,m3,m5) | type 1 (m1,m4,m5) | timeout, timeout |
| 78d53510b38736e3 | 1 | D15 D25 D35 D45 z[2] z[3] w[1] w[4] z[1] w[2] | type 16 (m0,m2,m3) | type 6 (m1,m4) | same, same |
| de05f2d8fe3db5f1 | 1 | U D15 D25 D35 z[2] z[3] w[1] w[4] D23 | type 1 (m2,m3,m5) | type 1 (m1,m4,m5) | timeout, timeout |
| 9861d60ca184c3e3 | 1 | D15 D25 D35 D45 z[2] z[3] w[1] w[4] z[1] w[2] | type 6 (m2,m3) | type 16 (m0,m1,m4) | same, same |
| 01c96ebcb817106e | 1 | D15 D25 D35 D45 z[2] z[3] w[1] w[4] z[1] w[2] | type 16 (m0,m2,m3) | type 6 (m1,m4) | same, same |

(type 1: R(ab;5)·μ₁₅ in the listed masses, LABELS K= (i)/(ii); type 6: AK's EQ, K= (iv); type 16: EQ with the rider
m₀, m_b³ = ±m_a(m_a+m₀)², K= (iv). "Restricted" eliminations, `scripts/coreC_sub.py` → `data/coreC_sub.txt`: each branch
with only the relations among the bodies of its triangle (and the rider) gives the listed condition; the last column
compares with the elimination of the whole branch, `data/coreC_part*.txt` ("same": the same condition; "timeout":
900 s exceeded).)

These are necessary conditions derived from the cores; for the cells, Lemma R1\* (or E1) on the cell gives the
condition R(23;5) (or E(T)) directly.

## 11. What remains computational, and gaps

1. **Cell data** (as MECHANISMS.md §5.1): completeness of the cell enumeration and the trees and argmin sets of the
   base identities of each cell (the engine's certified LPs). All lemmas take them as hypotheses.
2. **Secondary identities in 5 cells** (class 4 cell 58, class 28 cell 0, class 53 cell 1: subset sums; class 0 cell 0
   and class 15 cell 0: torques): their argmin is certified here by exact Farkas certificates, independently of the
   engine (`data/certificates.txt`). For the subset sums the certificates have the uniform reading of §4.2; for the two
   torques they are explicit but not reduced to a structural statement.
3. **Generic lemmas.** R1\*, W3, EQ2, TQ exclude 60 residual cells off explicit nonzero polynomials; R1\* and W3 have
   positive zeros (R1\*: a graph over the other masses, as R(ab;s); W3: sign changes found), EQ2 vanishes at positive
   masses only on m_a M_A² = m_b M_B² (here m3 = m4), TQ only on {m0 = m1, m3 = m4}. Inside these sets the cells are
   not analysed (the five-body paper's finer analysis is not attempted).
4. **Class 15 cell 0 at every mass** rests on the exact torque certificate of §8, not on a structural lemma.
5. **No-label cores** (§10.1): necessary conditions are derived by hand for all 25 cores; their exactness (that the
   condition generates the core's elimination ideal) is checked for family B (role elimination = (H_W)) and for 19 of
   the 26 class-29 branches (whole-branch elimination); for family A only necessity is proved (the blind elimination
   does not finish), with numeric consistency checks; 7 class-29 branches were checked only in restricted form
   (the relations of one triangle), which suffices for necessity.
6. **Checker programs.** `lemmas_resid.py` is the bridge from the data to the lemmas; it is cross-checked by the
   in-situ computations (item 2 of §9) but not proved correct.
7. The new all-mass counts (70,406) combine the per-cell flags of MECHANISMS.md (`data/coverage.jsonl` there) with
   B0, K, L and TD; the generic lemmas R1\*, W3, EQ2 were applied to all cells only as flags (their polynomials were
   instantiated for the residual cells only).

## 12. Files

- `RESIDUAL.md` — this note.
- `scripts/rkit.py` — read-only access to the engine data and to ../mechanisms data.
- `scripts/exactlp.py` — exact cell polyhedra, exact simplex, Farkas certificates; `scripts/test_exactlp.py`.
- `scripts/lemmas_resid.py` — checkers of B0, K, L, R1\*, W3, EQ2, TQ, TD; `scripts/run_resid.py` →
  `data/resid_cover.jsonl` (witnesses for the 115 cells).
- `scripts/insitu_resid.py` → `data/insitu_resid.log`; `scripts/insitu_sample.py` → `data/insitu_sample.log`.
- `scripts/algebra_resid.py` (sympy venv) → `data/algebra_resid.jsonl`.
- `scripts/global_cover.py` → `data/global_cover.jsonl`, `data/global_cover_summary.json`.
- `scripts/nolabel_list.py` → `data/nolabel_cells.jsonl` (the 174 no-label cells and the lemmas that apply).
- `scripts/certs_dump.py` → `data/certificates.txt`; `scripts/tables_resid.py` → `data/tables_resid.md`;
  `scripts/dump_resid.py` → `data/resid_dump.txt` (readable dump of the 115 cells).
- `checks/R1star.sing`, `W3.sing`, `EQ2.sing`, `TQ.sing` (+ `.out`), `checks/L_steps.py`.
- No-label cores: `checks/coreA_steps.py`, `checks/coreA_num.sing`, `checks/coreB.sing` (+ `.out`),
  `scripts/coreAB_num.py` → `data/coreAB_num.txt`, `scripts/coreC.py` → `data/coreC_part*.txt` (whole branches),
  `scripts/coreC_sub.py` → `data/coreC_sub.txt` (branches restricted to one triangle), `scripts/coreC_table.py`,
  `scripts/coreC_sub_table.py` → `data/coreC_table.md`, `data/coreC_sub_table.md`. `checks/L.sing` and
  `checks/coreA.sing` are the blind eliminations that do not finish (kept for reference).
- Run: `python3 -I scripts/run_resid.py`, then `insitu_resid.py`, `global_cover.py`,
  `insitu_sample.py 150`, `nolabel_list.py`, `certs_dump.py`, `tables_resid.py`; `algebra_resid.py` and
  `checks/L_steps.py`, `checks/coreA_steps.py` with `python3 -I` (with SymPy); `Singular -q checks/*.sing`;
  for the no-label cores `coreAB_num.py`, `coreC.py`, `coreC_sub.py`, `coreC_table.py`, `coreC_sub_table.py` (about
  two hours of Singular in total on one core).
