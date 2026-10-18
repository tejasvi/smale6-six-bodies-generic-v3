# chang_chen_diagrams.json: encoding and conventions

The file lists all 117 six-body zw-diagrams of K.-M. Chang and K.-C. Chen,
arXiv:2303.02853v1 (6 Mar 2023, 117 pp.). The diagrams appear as Figures 3-6 on pp. 72-75; Section 11
(pp. 54-71) treats them. Diagram numbers are the paper's (NO. 1-117). Vertices are the bodies 1..6 in the
paper's labelling.

## Source and confidence
The diagrams come from the authors' own Mathematica worksheet `SingSeqCCver202303.nb`
(http://www.math.nthu.edu.tw/~kchen/SSCC.html; the output of `zwmatrices[6]`, 117 `GraphicsBox`
objects with exact vertex coordinates and RGB colours). The notebook was parsed as text and not
evaluated (script `parse_nb_diagrams.py`, not included).
I then parsed the vector figures `figures/06-01..04.pdf` from the arXiv source independently,
through `pdftocairo -svg` and `pdftotext -bbox` (script `parse_fig_svg.py`, not included). All 117 diagrams agree exactly
(edges, edge colours, circles, numbers). Confidence: high. No diagram was transcribed by eye.

The colour code comes from the notebook's drawing code (Algorithm I, "BEGIN DRAWING DIAGRAMS"):
- edges: red = z-stroke only, light blue = w-stroke only, purple = zw-edge (both strokes);
- vertex disks: red = z-circle only, blue = w-circle only, purple = both, white = none.

## Fields per diagram
- `z_strokes`, `w_strokes`: vertex pairs [i,j] with i<j. A pair in both lists is a zw-edge. For convenience,
  `zw_edges`, `z_only_edges` and `w_only_edges` split the same data.
- `z_circled`, `w_circled`: the circled vertices.
- `z_matrix_A`, `w_matrix_B`: the paper's z- and w-matrices (Sec. 3, p. 10). These are symmetric 0/1
  adjacency matrices with the circles as diagonal 1s; the zw-matrix is (A|B).
- `status`: one of
  - `excluded_algorithm_II_direct` (27 diagrams): listed on p. 54; no individual argument is printed.
  - `excluded_algorithm_II_indirect` (1, 10, 59, 60): Sec. 11.7, pp. 63-65; the argument uses positive masses.
  - `excluded_positive_masses_algorithm_III` (116): Groebner basis gives m1m4m5+m2m3m6=0.
  - `mass_relation` (61): impossible unless the masses satisfy the polynomial `mass_relation_latex`.
  - `unresolved` (24): 5, 6, 8, 52, 63, 64, 65, 66, 67, 69, 71, 73, 74, 75, 79, 80, 81, 82, 88, 89, 90, 93, 94, 98.
    The paper never lists these 24. I obtained them as the complement of every diagram the paper treats.
    The count matches the paper's: 117 - 31 - 62 = 24.
- `mass_relation_latex`, `C2_size` (= |C_2|), `method_or_selection`, `mass_relation_source`: copied from
  Tables 2-3 (pp. 57, 60) and the text of Secs. 11.2-11.13, with page numbers. The mu_k notation is
  defined at the top level of the JSON (Sec. 11.1, p. 55).
- `self_dual_under_colour_swap_up_to_S6`: true for 19 diagrams.
- `orders_given` (15 diagrams): where the paper prints zw-order matrices, r-order matrices or maximal-order
  sets, plus any cluster equations it states. The matrices themselves are not transcribed; the level code is in the
  top-level `orders_note`.

## The paper's conventions (Sec. 2, pp. 5-9; same as Albouy-Kaloshin)
Set z_k = x_k + i y_k, w_k = x_k - i y_k, Z_kl = z_kl^{-1/2} w_kl^{-3/2} (= z_kl r_kl^{-3}), and
W_kl = w_kl^{-1/2} z_kl^{-3/2}. Normalize so that ||Z|| = ||W|| = eps^{-2}, where Z = (z_k, Z_kl) and
W = (w_k, W_kl).
- A z-stroke joins k and l iff Z_kl ~ eps^{-2}.
- A z-circle sits at k iff z_k ~ eps^{-2}.
- w-strokes and w-circles are defined the same way.
- A zw-edge (both strokes) occurs iff r_kl ~ eps.
- A maximal z-stroke has z_kl ~ eps^{-2} and w_kl ~ eps^2.

Order levels in the order matrices (Sec. 4.1, p. 17):
- positions and separations: 0: < eps^2; 1: eps^2; 2: between eps^2 and eps; 3: eps; 4: between eps and eps^{-2}; 5: eps^{-2}.
- distances: 1: eps; 2: between eps and 1; 3: 1; 4: between 1 and eps^{-2}; 5: eps^{-2}.

## Symmetry: S6 x (z <-> w)
The 117 are classes of zw-matrices modulo simultaneous relabelling of the bodies (all of S6) **and**
the exchange of the colours (A|B) -> (B|A).
- Sec. 6, Step (I.4), p. 36: "remove all duplicated matrices up to permutations of bodies and the
  exchange of z and w. ... When n = 6, there are 117 diagrams remaining."
- Notebook: the duplicate test compares {A[p,p],B[p,p]} and {B[p,p],A[p,p]} for all 720 permutations p.
- Checked here (`tools/canon.py`): the 117 are pairwise inequivalent under S6 x Z2.
- 19 diagrams are self-dual under the colour swap (up to S6): 6, 7, 8, 11, 63, 74, 76, 81, 89, 90, 96, 98,
  99, 103, 105, 110, 114, 115, 116. So under S6 alone the same set gives 117 + 98 = **215** classes.
- The representatives satisfy tr(A) <= tr(B), i.e. no more z-circles than w-circles (eq. (6.2), p. 35). In A,
  the circled bodies carry the larger indices (eq. (6.1), p. 34).

**Important for comparisons.** 117 is the output of Algorithm I alone. Algorithm II (order matrices)
then removes 27 + 4, and Algorithm III removes 116. That leaves 85 (the SIADS abstract's "86" is the count
after Algorithm II).

## Rules used by Algorithm I to reach 117 (Table 1, p. 11; Sec. 3, pp. 10-16, rule statements on pp. 12-16; Sec. 6, pp. 33-36)
In application order:
1. Monocolour rules: Column Sums (1a); First Rule of Trace-2 Matrices; Second Rule of Triangles (2c);
   First Rule of Quadrilaterals (2f); First Rule of Triangles (2c); Rule of Trace-3 Matrices;
   Rule of Trace-0 Principal Minors; First Rule of Trace (trace != 1, 1d).
2. Matching of z- and w-matrices: Rule of Fully Connected Companions (1e + 2d).
3. Bicolour rules: Circling (cm); Second Rule of Trace-2 Matrices; Third Rule of Triangles (Cor. 2e,
   which encodes 2b); Two Column Sums (2a); Fourth Rule of Triangles (2e); Connected Components (1c);
   Second Rule of Quadrilaterals (2g); Pentagons (2d + Estimate 2).

Some of these go beyond a literal transcription of the Albouy-Kaloshin colouring rules:
- **Rule of Trace-0 Principal Minors** (p. 16): for any vertex set I with no z-circle, the number of
  z-strokes leaving I is not 1 (same for w). Proof: sum_{k in I} m_k z_k = sum_{k in I, l not in I} m_k m_l Z_lk,
  where the left side is o(eps^{-2}). It corresponds to no AK colouring rule; it generalizes 1c to arbitrary cuts.
  The authors say it can be skipped for n <= 5 but is "irreplaceable" for n = 6.
- **First Rule of Trace-2 Matrices** (p. 12): if exactly two z-circles i, j, then a_ij = 1 and
  a_ik = a_jk for all k. This uses AK Prop. 1 together with 1a, 1d, 2c, 2e.
- **Second Rule of Trace-2 Matrices** (p. 12): the only z-stroke joins the two z-circles i, j, and there are
  no other z-strokes. Then b_ik = b_jk = 0 and, **if m_i^3 + m_j^3 != 0**, tr(B) != n-3. This uses AK Prop. 4
  and is a mass-conditional pruning (it is harmless for positive masses).
- **Rule of Trace-3 Matrices** (p. 12, from 1c, 2c, 2e): with z-circles exactly at i, j, k, if
  a_ij = a_ik = a_il = 1 for some l outside {i, j, k}, then a_jl + a_kl != 0.
- **Rule of Connected Components** (ii) (p. 15): if every vertex of a z-component is z-circled,
  the component contains a pair i, j with c_ij != 2 (that is, not a zw-edge).
- **Fully Connected Companions** (p. 15): if A is connected on all n vertices, then tr(B) = 0.
- **Pentagons** (p. 15): on a 5-cycle of edges, N_z != 1, N_w != 1, and (N_z, N_w, N_zw) is not (4,0,1) or (0,4,1).
- **First Rule of Quadrilaterals** (p. 15): among 4 vertices the number of z-strokes is not 5 (from 2f).

Rules not in Algorithm I:
- Rule 2h and its corollary (a zw-edge implies a second one) and AK Prop. 2 are applied only in Algorithm II
  (p. 25, Secs. 4.4-4.5; `Rule2hQ` in Appendix II). None of the 117 has exactly one zw-edge anyway.
- Rule 2d is used only in the pentagon and connected-companion instances, and 2f only in the quadrilateral instance.

Algorithm I counts: about 2.85e6 zw-matrices after matching, and about 3.35e5 after Circling and the Second
Rule of Trace-2 (paper, p. 35). The notebook output of `zwmatrices[6]` gives 329,577 at that point, then 27,101 (Third Rule of Triangles), 15,943 (Two Column Sums), 2,368 (Fourth Rule of Triangles),
2,188 (Connected Components), 1,123 (Second Rule of Quadrilaterals), 1,010 (Pentagons), and 117 after
removing duplicates under S6 x Z2.

## Known inconsistencies in the paper (flagged in the JSON)
- Table 3 (p. 60) has a row "25" with a mass relation, but 25 is in the Algorithm-II list (p. 54).
  Diagram 22 appears in the Sec. 11.5 header but has no row. I read "25" as 22, but this is **uncertain**.
- p. 56: "applying our subroutine with Groebner basis to diagram 81" sits in the paragraph on 77/102/109/117,
  and the command uses `FindOrder[77]`. Almost certainly 77 is meant (81 is unresolved).
- p. 55: the diagram-107 example prints the command `FindOrder[111]`, probably a typo.
- p. 71 (diagram 14): "f_{6,14,3} is the same as f_{6,16,3}", but the derivation parallels case 4 of
  diagram 16 (f_{6,16,4}).
- Codimension: arXiv v1 (p. 1, p. 38) and the authors' web page say the exceptional masses lie in a
  "co-dimension 2" variety. The SIADS abstract (2025) says "co-dimension 1". Each relation is a single
  homogeneous equation, so the correct reading is codimension 1.
- The journal versions (JSC 2024 part I, SIADS 2025 part II) were not accessible. Their diagram numbering
  is **not verified**. Part I reports 86 diagrams after Algorithms I+II, so it may renumber.
