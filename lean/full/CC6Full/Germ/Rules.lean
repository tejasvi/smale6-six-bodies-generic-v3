import CC6Full.Germ.Orders

/-!
# The rules of Albouy and Kaloshin at a singular place (Lemma 2.11, `lem:rules`)

The *diagram* of a germ consists of its `z`-strokes, `w`-strokes and `z`- and `w`-circled bodies (§2.4). A pair is an
*edge* (`Germ.edge`) if it is a stroke of some colour, a `zw`-edge (`Germ.zwEdge`) if it is a stroke of both colours,
and two edges have the same kind (`Germ.sameKind`: `z`, `w` or `zw`) if they carry the same strokes. The
`z`-component of a body `k` is the set of the bodies `j` with `Relation.ReflTransGen G.zStroke k j`.

* (E1)–(E6): `Germ.E1_z`, `Germ.E1_w`, `Germ.E2`, `Germ.E3`, `Germ.E4_z`, `Germ.E4_w`, `Germ.E5` (with the form
  `Germ.E5'`: a `zw`-edge is not the only one), `Germ.E6`;
* (C1)–(C4): `Germ.C1_z`, `Germ.C1_w`, `Germ.C2_z`, `Germ.C2_w`, `Germ.C3_z`, `Germ.C3_w` (with the remark
  `Germ.C3_z'`, `Germ.C3_w'`: a component never contains exactly one circled body), `Germ.C4_z`, `Germ.C4_w`;
* `Germ.edges_clique`, `Germ.edges_four`: the consequence of (E3) stated after the proof (pairwise edges have one
  kind, one `ζ`, one `ω`), and `Germ.ruleT_z`, `Germ.ruleT_w`: Rule T of §3 (`sec:diagrams`).

The theorems that use the masses assume `hm : ∀ i, 0 < m i`, as Lemma 2.11 does: (C1) and (E4) use it through
`m_k ≠ 0`, (E4) and (C3) through the nonvanishing of partial sums of masses, and (E5) through `m_k m_l ≠ 0` in the
equation `U = E` of the germ (`pot`). (E1)–(E3), (E6), (C2), (C4) and Rule T hold for all masses. (E2), (E3), (E5)
and (E6) are symmetric in the two colours; the other rules are stated for each colour.

The proofs are those of the paper. The coefficient of `τ^{−2}` of the equation of a body or of a subset sum, and the
coefficient of `τ^{−1}` of `U = E`, are the initial forms of Lemma 2.10 (`lem:initial`): a series of order at least
`e` has order exactly `e` iff its coefficient of `τ^e` does not vanish (`Colour.orderTop_eq_iff_coeff`). As in
`Orders.lean`, everything is proved for a colour pair `Colour.Pair m p h h'` and specialised to `G.colZ` and `G.colW`.
-/

namespace CC6Full

open Finset

noncomputable section

namespace Colour

variable {n : ℕ}

/-! ## Coefficients -/

theorem coeff_cS_mul (c : ℂ) (f : Ser) (e : ℚ) : (cS c * f).coeff e = c * f.coeff e := by
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem coeff_cS_of_ne (c : ℂ) {e : ℚ} (he : e ≠ 0) : (cS c).coeff e = 0 := by
  unfold cS
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne he]

/-- A series of order at least `e` has order `e` iff its coefficient of `τ^e` does not vanish. -/
theorem orderTop_eq_iff_coeff {f : Ser} {e : ℚ} (hf : (e : WithTop ℚ) ≤ f.orderTop) :
    f.orderTop = e ↔ f.coeff e ≠ 0 :=
  ⟨HahnSeries.coeff_orderTop_ne, fun hc => le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hc) hf⟩

/-- An antisymmetric double sum over `K × K` vanishes. -/
theorem sum_sum_antisymm {T : Fin n → Fin n → ℂ} (hanti : ∀ j i, T i j = -T j i) (K : Finset (Fin n)) :
    ∑ j ∈ K, ∑ i ∈ K, T j i = 0 := by
  have h : ∑ j ∈ K, ∑ i ∈ K, T j i = -∑ j ∈ K, ∑ i ∈ K, T j i := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => hanti j i
  linear_combination h / 2

/-! ## Three or four rational numbers -/

theorem not_lt_of_min_max {a1 a2 a3 : ℚ} (m1 : a2 ≤ a1 ∨ a3 ≤ a1) (M2 : a2 ≤ a3 ∨ a2 ≤ a1) : ¬ a1 < a2 := by
  intro h
  rcases m1 with m1 | m1
  · linarith
  · rcases M2 with M2 | M2 <;> linarith

/-- Three numbers whose minimum is attained twice, and whose images under a strictly decreasing correspondence have
their minimum attained twice, are equal. -/
theorem tri_eq {a1 a2 a3 b1 b2 b3 : ℚ}
    (m1 : min a2 a3 ≤ a1) (m2 : min a3 a1 ≤ a2) (m3 : min a1 a2 ≤ a3)
    (n1 : min b2 b3 ≤ b1) (n2 : min b3 b1 ≤ b2) (n3 : min b1 b2 ≤ b3)
    (s12 : a1 < a2 → b2 < b1) (s21 : a2 < a1 → b1 < b2) (s13 : a1 < a3 → b3 < b1)
    (s31 : a3 < a1 → b1 < b3) (s23 : a2 < a3 → b3 < b2) (s32 : a3 < a2 → b2 < b3) :
    a1 = a2 ∧ a2 = a3 := by
  have M1 : a1 ≤ a2 ∨ a1 ≤ a3 := by
    by_contra h
    push Not at h
    rcases min_le_iff.mp n1 with h' | h'
    · linarith [s21 h.1]
    · linarith [s31 h.2]
  have M2 : a2 ≤ a3 ∨ a2 ≤ a1 := by
    by_contra h
    push Not at h
    rcases min_le_iff.mp n2 with h' | h'
    · linarith [s32 h.1]
    · linarith [s12 h.2]
  have M3 : a3 ≤ a1 ∨ a3 ≤ a2 := by
    by_contra h
    push Not at h
    rcases min_le_iff.mp n3 with h' | h'
    · linarith [s13 h.1]
    · linarith [s23 h.2]
  have m1' := min_le_iff.mp m1
  have m2' := min_le_iff.mp m2
  have m3' := min_le_iff.mp m3
  have c12 := not_lt_of_min_max m1' M2
  have c21 := not_lt_of_min_max (a1 := a2) (a2 := a1) (a3 := a3) m2'.symm M1.symm
  have c23 := not_lt_of_min_max (a1 := a2) (a2 := a3) (a3 := a1) m2' M3
  have c32 := not_lt_of_min_max (a1 := a3) (a2 := a2) (a3 := a1) m3'.symm M2.symm
  exact ⟨le_antisymm (not_lt.mp c21) (not_lt.mp c12), le_antisymm (not_lt.mp c32) (not_lt.mp c23)⟩

/-- If the images of four numbers under a strictly decreasing correspondence have their minimum attained twice, the
maximum of the four is attained twice. -/
theorem le_max_of_anti {a1 a2 a3 a4 b1 b2 b3 b4 : ℚ} (n1 : min b2 (min b3 b4) ≤ b1)
    (s2 : a2 < a1 → b1 < b2) (s3 : a3 < a1 → b1 < b3) (s4 : a4 < a1 → b1 < b4) :
    a1 ≤ max a2 (max a3 a4) := by
  by_contra h
  simp only [le_max_iff, not_or, not_le] at h
  have := lt_min (s2 h.1) (lt_min (s3 h.2.1) (s4 h.2.2))
  exact absurd n1 (not_le.mpr this)

theorem quad_core {a1 a2 a3 a4 : ℚ}
    (m1 : min a2 (min a3 a4) ≤ a1) (m2 : min a3 (min a4 a1) ≤ a2) (m4 : min a1 (min a2 a3) ≤ a4)
    (M2 : a2 ≤ max a3 (max a4 a1)) (M3 : a3 ≤ max a4 (max a1 a2)) (M4 : a4 ≤ max a1 (max a2 a3))
    (adj12 : ¬ (a1 = a2 ∧ a3 = a4 ∧ a1 < a3)) (adj41 : ¬ (a4 = a1 ∧ a2 = a3 ∧ a4 < a2)) : ¬ a1 < a3 := by
  intro h13
  simp only [min_le_iff, le_max_iff] at m1 m2 m4 M2 M3 M4
  rcases m1 with hA | hA | hA
  · rcases M3 with hB | hB | hB
    · have e12 : a1 = a2 := by rcases m2 with h | h | h <;> linarith
      have e34 : a3 = a4 := by rcases M4 with h | h | h <;> linarith
      exact adj12 ⟨e12, e34, h13⟩
    · linarith
    · linarith
  · linarith
  · rcases M3 with hB | hB | hB
    · linarith
    · linarith
    · have e41 : a4 = a1 := by rcases m4 with h | h | h <;> linarith
      have e23 : a2 = a3 := by rcases M2 with h | h | h <;> linarith
      exact adj41 ⟨e41, e23, by linarith⟩

/-- Four numbers `a₁, …, a₄` around a cycle whose minimum and maximum are both attained twice, and such that two
adjacent ones are never the minimum while the other two are a larger maximum, have `a₁ = a₃` and `a₂ = a₄`. -/
theorem quad_eq {a1 a2 a3 a4 : ℚ}
    (m1 : min a2 (min a3 a4) ≤ a1) (m2 : min a3 (min a4 a1) ≤ a2)
    (m3 : min a4 (min a1 a2) ≤ a3) (m4 : min a1 (min a2 a3) ≤ a4)
    (M1 : a1 ≤ max a2 (max a3 a4)) (M2 : a2 ≤ max a3 (max a4 a1))
    (M3 : a3 ≤ max a4 (max a1 a2)) (M4 : a4 ≤ max a1 (max a2 a3))
    (adj12 : ¬ (a1 = a2 ∧ a3 = a4 ∧ a1 < a3)) (adj23 : ¬ (a2 = a3 ∧ a4 = a1 ∧ a2 < a4))
    (adj34 : ¬ (a3 = a4 ∧ a1 = a2 ∧ a3 < a1)) (adj41 : ¬ (a4 = a1 ∧ a2 = a3 ∧ a4 < a2)) :
    a1 = a3 ∧ a2 = a4 := by
  have c1 := quad_core m1 m2 m4 M2 M3 M4 adj12 adj41
  have c3 := quad_core m3 m4 m2 M4 M1 M2 adj34 adj23
  have c2 := quad_core m2 m3 m1 M3 M4 M1 adj23 adj12
  have c4 := quad_core m4 m1 m3 M1 M2 M3 adj41 adj34
  exact ⟨le_antisymm (not_lt.mp c3) (not_lt.mp c1), le_antisymm (not_lt.mp c4) (not_lt.mp c2)⟩

namespace Pair

variable {m : Fin n → ℝ} {p : Fin n → Fin n → Ser} {h h' : Fin n → Ser}

/-! ## Coefficients of `τ^{−2}` -/

theorem circle_iff_coeff (H : Pair m p h h') (k : Fin n) : Circle h k ↔ (h k).coeff (-2) ≠ 0 :=
  orderTop_eq_iff_coeff (H.low.1 k)

theorem stroke_iff_coeff (H : Pair m p h h') {k l : Fin n} (hkl : k ≠ l) :
    Stroke p h k l ↔ (termZ p h k l).coeff (-2) ≠ 0 := by
  unfold Stroke
  rw [← orderTop_eq_iff_coeff (H.low.2.1 k l hkl)]
  exact ⟨fun h1 => h1.2, fun h1 => ⟨hkl, h1⟩⟩

theorem coeff_termZ_eq_zero (H : Pair m p h h') {k l : Fin n} (hkl : k ≠ l) (hs : ¬ Stroke p h k l) :
    (termZ p h k l).coeff (-2) = 0 := by
  by_contra hc
  exact hs ((H.stroke_iff_coeff hkl).mpr hc)

/-- The coefficient form of the equation of the body `k`. -/
theorem coeff_body (H : Pair m p h h') (k : Fin n) (e : ℚ) :
    (h k).coeff e = ∑ l ∈ univ.erase k, (m l : ℂ) * (termZ p h k l).coeff e := by
  conv_lhs => rw [H.body k]
  rw [HahnSeries.coeff_sum]
  exact Finset.sum_congr rfl fun l _ => coeff_cS_mul _ _ _

/-- The coefficient form of the subset sum `Σ_{j ∈ K} m_j h_j = Σ_{j ∈ K, i ∉ K} m_j m_i p_ji³ (h_j − h_i)`. -/
theorem coeff_subset_sum (H : Pair m p h h') (K : Finset (Fin n)) (e : ℚ) :
    ∑ j ∈ K, (m j : ℂ) * (h j).coeff e =
      ∑ j ∈ K, ∑ i ∈ univ \ K, (m j : ℂ) * ((m i : ℂ) * (termZ p h j i).coeff e) := by
  have hanti : ∀ j i : Fin n, (m i : ℂ) * ((m j : ℂ) * (termZ p h i j).coeff e) =
      -((m j : ℂ) * ((m i : ℂ) * (termZ p h j i).coeff e)) := fun j i => by
    rw [H.termZ_swap j i, HahnSeries.coeff_neg]
    ring
  have h1 : ∀ j, (m j : ℂ) * (h j).coeff e =
      ∑ i, (m j : ℂ) * ((m i : ℂ) * (termZ p h j i).coeff e) := by
    intro j
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), H.coeff_body j, Finset.mul_sum]
    simp [termZ]
  calc ∑ j ∈ K, (m j : ℂ) * (h j).coeff e
      = ∑ j ∈ K, ∑ i, (m j : ℂ) * ((m i : ℂ) * (termZ p h j i).coeff e) :=
        Finset.sum_congr rfl fun j _ => h1 j
    _ = ∑ j ∈ K, ∑ i ∈ K, (m j : ℂ) * ((m i : ℂ) * (termZ p h j i).coeff e) +
          ∑ j ∈ K, ∑ i ∈ univ \ K, (m j : ℂ) * ((m i : ℂ) * (termZ p h j i).coeff e) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ K)]
    _ = _ := by rw [sum_sum_antisymm hanti K, zero_add]

/-- Bodies whose difference has order `> −2` have the same coefficient of `τ^{−2}`. -/
theorem coeff_eq_of_close (H : Pair m p h h') {a b : Fin n} (hab : a ≠ b) (hc : -2 < ord h a b) :
    (h a).coeff (-2) = (h b).coeff (-2) := by
  have h0 : (h a - h b).coeff (-2) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (by rw [H.orderTop_diff hab]; exact_mod_cast hc)
  rwa [HahnSeries.coeff_sub, sub_eq_zero] at h0

/-! ## Edges -/

/-- On an edge (a stroke of some colour) the kind is determined by `e(h_kl)`: `kl` is an `h`-stroke iff
`e(h_kl) ≤ 1` and an `h'`-stroke iff `e(h_kl) ≥ 1`, and `e(h'_kl) = f(e(h_kl))` for the strictly decreasing function
`f(ζ) = (4 − ζ)/3` (`ζ ≤ 1`), `f(ζ) = 4 − 3ζ` (`ζ ≥ 1`). -/
theorem edge_facts (H : Pair m p h h') {k l : Fin n} (he : Stroke p h k l ∨ Stroke p h' k l) :
    (Stroke p h k l ↔ ord h k l ≤ 1) ∧ (Stroke p h' k l ↔ 1 ≤ ord h k l) ∧
      ((ord h k l ≤ 1 ∧ ord h k l + 3 * ord h' k l = 4) ∨
        (1 ≤ ord h k l ∧ 3 * ord h k l + ord h' k l = 4)) := by
  have hkl : k ≠ l := he.elim (fun s => s.1) (fun s => s.1)
  obtain ⟨b1, b2, b3, b4⟩ := H.bounds hkl
  rw [H.stroke_iff hkl, H.stroke_iff' hkl] at he ⊢
  rcases he with e | e
  · exact ⟨⟨fun _ => by linarith, fun _ => e⟩, ⟨fun _ => by linarith, fun _ => by linarith⟩,
      Or.inl ⟨by linarith, e⟩⟩
  · exact ⟨⟨fun _ => by linarith, fun _ => by linarith⟩, ⟨fun _ => by linarith, fun _ => e⟩,
      Or.inr ⟨by linarith, e⟩⟩

theorem edge_anti (H : Pair m p h h') {k l k' l' : Fin n} (he : Stroke p h k l ∨ Stroke p h' k l)
    (he' : Stroke p h k' l' ∨ Stroke p h' k' l') (hlt : ord h k l < ord h k' l') :
    ord h' k' l' < ord h' k l := by
  rcases (H.edge_facts he).2.2 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases (H.edge_facts he').2.2 with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> linarith

theorem edge_eq (H : Pair m p h h') {k l k' l' : Fin n} (he : Stroke p h k l ∨ Stroke p h' k l)
    (he' : Stroke p h k' l' ∨ Stroke p h' k' l') (heq : ord h k l = ord h k' l') :
    ord h' k l = ord h' k' l' := by
  rcases (H.edge_facts he).2.2 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases (H.edge_facts he').2.2 with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> linarith

theorem edge_kind_eq (H : Pair m p h h') {k l k' l' : Fin n} (he : Stroke p h k l ∨ Stroke p h' k l)
    (he' : Stroke p h k' l' ∨ Stroke p h' k' l') (heq : ord h k l = ord h k' l') :
    (Stroke p h k l ↔ Stroke p h k' l') ∧ (Stroke p h' k l ↔ Stroke p h' k' l') := by
  rw [(H.edge_facts he).1, (H.edge_facts he').1, (H.edge_facts he).2.1, (H.edge_facts he').2.1, heq]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- (E2) for a colour pair. -/
theorem zw_trans (H : Pair m p h h') {a b c : Fin n} (z1 : Stroke p h a b) (w1 : Stroke p h' a b)
    (z2 : Stroke p h b c) (w2 : Stroke p h' b c) (hac : a ≠ c) : Stroke p h a c ∧ Stroke p h' a c := by
  have hab := z1.1
  have hbc := z2.1
  have e1 := (H.stroke_iff hab).mp z1
  have f1 := (H.stroke_iff' hab).mp w1
  have e2 := (H.stroke_iff hbc).mp z2
  have f2 := (H.stroke_iff' hbc).mp w2
  have u := H.ultra hab hbc hac
  have v := H.symm.ultra hab hbc hac
  have za : ord h a b = 1 := by linarith
  have zb : ord h b c = 1 := by linarith
  have wa : ord h' a b = 1 := by linarith
  have wb : ord h' b c = 1 := by linarith
  rw [za, zb, min_self] at u
  rw [wa, wb, min_self] at v
  obtain ⟨-, -, b3, b4⟩ := H.bounds hac
  exact ⟨(H.stroke_iff hac).mpr (by linarith), (H.stroke_iff' hac).mpr (by linarith)⟩

/-- (E3) for a colour pair, on the triangle of edges `ab`, `bc`, `ca`. -/
theorem tri_rule (H : Pair m p h h') {a b c : Fin n} (e1 : Stroke p h a b ∨ Stroke p h' a b)
    (e2 : Stroke p h b c ∨ Stroke p h' b c) (e3 : Stroke p h c a ∨ Stroke p h' c a) :
    (ord h a b = ord h b c ∧ ord h b c = ord h c a) ∧
      (ord h' a b = ord h' b c ∧ ord h' b c = ord h' c a) ∧
      ((Stroke p h a b ↔ Stroke p h b c) ∧ (Stroke p h' a b ↔ Stroke p h' b c)) ∧
      ((Stroke p h b c ↔ Stroke p h c a) ∧ (Stroke p h' b c ↔ Stroke p h' c a)) := by
  have hab : a ≠ b := e1.elim (fun s => s.1) (fun s => s.1)
  have hbc : b ≠ c := e2.elim (fun s => s.1) (fun s => s.1)
  have hca : c ≠ a := e3.elim (fun s => s.1) (fun s => s.1)
  have hz := tri_eq (H.ultra' hbc hca hab.symm) (H.ultra' hca hab hbc.symm) (H.ultra' hab hbc hca.symm)
    (H.symm.ultra' hbc hca hab.symm) (H.symm.ultra' hca hab hbc.symm) (H.symm.ultra' hab hbc hca.symm)
    (H.edge_anti e1 e2) (H.edge_anti e2 e1) (H.edge_anti e1 e3) (H.edge_anti e3 e1) (H.edge_anti e2 e3)
    (H.edge_anti e3 e2)
  exact ⟨hz, ⟨H.edge_eq e1 e2 hz.1, H.edge_eq e2 e3 hz.2⟩, H.edge_kind_eq e1 e2 hz.1,
    H.edge_kind_eq e2 e3 hz.2⟩

/-- In a 4-cycle `abcd`, the edges `ab`, `bc` cannot carry the least value of `e(h)` while `cd`, `da` carry a larger
value (O5 in the triangles `acd`, `abc` and (O1) for `ac`). -/
theorem quad_adj (H : Pair m p h h') {a b c d : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d)
    (hda : d ≠ a) (hac : a ≠ c) (e1 : Stroke p h a b ∨ Stroke p h' a b)
    (e2 : Stroke p h b c ∨ Stroke p h' b c) :
    ¬ (ord h a b = ord h b c ∧ ord h c d = ord h d a ∧ ord h a b < ord h c d) := by
  rintro ⟨h12, h34, hlt⟩
  have hu := H.ultra' hcd hda hac.symm
  have hv := H.symm.ultra hab hbc hac
  rw [← h34, min_self] at hu
  rw [← H.edge_eq e1 e2 h12, min_self] at hv
  obtain ⟨-, -, b3, b4⟩ := H.bounds hac
  rcases (H.edge_facts e1).2.2 with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> linarith

/-- (E6) for a colour pair, on the 4-cycle of edges `ab`, `bc`, `cd`, `da`. -/
theorem quad_rule (H : Pair m p h h') {a b c d : Fin n} (hac : a ≠ c) (hbd : b ≠ d)
    (e1 : Stroke p h a b ∨ Stroke p h' a b) (e2 : Stroke p h b c ∨ Stroke p h' b c)
    (e3 : Stroke p h c d ∨ Stroke p h' c d) (e4 : Stroke p h d a ∨ Stroke p h' d a) :
    (ord h a b = ord h c d ∧ ord h' a b = ord h' c d ∧
        ((Stroke p h a b ↔ Stroke p h c d) ∧ (Stroke p h' a b ↔ Stroke p h' c d))) ∧
      (ord h b c = ord h d a ∧ ord h' b c = ord h' d a ∧
        ((Stroke p h b c ↔ Stroke p h d a) ∧ (Stroke p h' b c ↔ Stroke p h' d a))) := by
  have hab : a ≠ b := e1.elim (fun s => s.1) (fun s => s.1)
  have hbc : b ≠ c := e2.elim (fun s => s.1) (fun s => s.1)
  have hcd : c ≠ d := e3.elim (fun s => s.1) (fun s => s.1)
  have hda : d ≠ a := e4.elim (fun s => s.1) (fun s => s.1)
  have hq := quad_eq
    (H.ultra4' hbc hcd hda hab.symm) (H.ultra4' hcd hda hab hbc.symm)
    (H.ultra4' hda hab hbc hcd.symm) (H.ultra4' hab hbc hcd hda.symm)
    (le_max_of_anti (H.symm.ultra4' hbc hcd hda hab.symm) (H.edge_anti e2 e1) (H.edge_anti e3 e1)
      (H.edge_anti e4 e1))
    (le_max_of_anti (H.symm.ultra4' hcd hda hab hbc.symm) (H.edge_anti e3 e2) (H.edge_anti e4 e2)
      (H.edge_anti e1 e2))
    (le_max_of_anti (H.symm.ultra4' hda hab hbc hcd.symm) (H.edge_anti e4 e3) (H.edge_anti e1 e3)
      (H.edge_anti e2 e3))
    (le_max_of_anti (H.symm.ultra4' hab hbc hcd hda.symm) (H.edge_anti e1 e4) (H.edge_anti e2 e4)
      (H.edge_anti e3 e4))
    (H.quad_adj hab hbc hcd hda hac e1 e2) (H.quad_adj hbc hcd hda hab hbd e2 e3)
    (H.quad_adj hcd hda hab hbc hac.symm e3 e4) (H.quad_adj hda hab hbc hcd hbd.symm e4 e1)
  exact ⟨⟨hq.1, H.edge_eq e1 e3 hq.1, H.edge_kind_eq e1 e3 hq.1⟩,
    ⟨hq.2, H.edge_eq e2 e4 hq.2, H.edge_kind_eq e2 e4 hq.2⟩⟩

/-! ## Circles -/

/-- (C1), first part, for a colour pair. -/
theorem not_circle_of_no_stroke (H : Pair m p h h') {k : Fin n} (hk : ∀ l, ¬ Stroke p h k l) :
    ¬ Circle h k := by
  rw [H.circle_iff_coeff, H.coeff_body k, not_not]
  refine Finset.sum_eq_zero fun l hl => ?_
  rw [H.coeff_termZ_eq_zero (Finset.ne_of_mem_erase hl).symm (hk l), mul_zero]

/-- (C1), second part, for a colour pair. -/
theorem circle_of_unique_stroke (H : Pair m p h h') {k l : Fin n} (hm : m l ≠ 0) (hs : Stroke p h k l)
    (hu : ∀ j, Stroke p h k j → j = l) : Circle h k := by
  have hkl := hs.1
  rw [H.circle_iff_coeff, H.coeff_body k, Finset.sum_eq_single l]
  · exact mul_ne_zero (by exact_mod_cast hm) ((H.stroke_iff_coeff hkl).mp hs)
  · intro j hj hjl
    rw [H.coeff_termZ_eq_zero (Finset.ne_of_mem_erase hj).symm (fun hs' => hjl (hu j hs')), mul_zero]
  · intro hl
    exact absurd (Finset.mem_erase.mpr ⟨hkl.symm, Finset.mem_univ l⟩) hl

/-- (E1) for a colour pair. -/
theorem exists_stroke (H : Pair m p h h') : ∃ k l, Stroke p h k l := by
  rcases H.low.2.2 with ⟨k, hk⟩ | ⟨k, l, hkl, hs⟩
  · by_contra hne
    push Not at hne
    exact H.not_circle_of_no_stroke (hne k) hk
  · exact ⟨k, l, hkl, hs⟩

/-- (C2) for a colour pair. -/
theorem circle_iff_of_stroke' (H : Pair m p h h') {k l : Fin n} (hs : Stroke p h' k l) :
    Circle h k ↔ Circle h l := by
  have h1 : 1 ≤ ord h k l := ((H.edge_facts (Or.inr hs)).2.1).mp hs
  constructor
  · intro hk
    by_contra hl
    have := H.ord_of_circle hk hl
    linarith
  · intro hl
    by_contra hk
    have := H.ord_of_circle hl hk
    rw [ord_comm] at this
    linarith

/-- (E4) for a colour pair. -/
theorem stroke_at_zw (H : Pair m p h h') (hm : ∀ i, 0 < m i) {a b : Fin n} (hz : Stroke p h a b)
    (hw : Stroke p h' a b) : ∃ j, j ≠ a ∧ j ≠ b ∧ (Stroke p h a j ∨ Stroke p h b j) := by
  by_contra hne
  push Not at hne
  have hab : a ≠ b := hz.1
  have ca : Circle h a := H.circle_of_unique_stroke (hm b).ne' hz fun j hj => by
    by_contra hjb
    exact (hne j hj.1.symm hjb).1 hj
  have hclose : (h a).coeff (-2) = (h b).coeff (-2) :=
    H.coeff_eq_of_close hab (by linarith [((H.edge_facts (Or.inr hw)).2.1).mp hw])
  have hsum := H.coeff_subset_sum {a, b} (-2)
  have hout : ∀ j ∈ ({a, b} : Finset (Fin n)),
      ∑ i ∈ univ \ {a, b}, (m j : ℂ) * ((m i : ℂ) * (termZ p h j i).coeff (-2)) = 0 := by
    intro j hj
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i ∉ ({a, b} : Finset (Fin n)) := (Finset.mem_sdiff.mp hi).2
    have hji : j ≠ i := fun e => hi' (e ▸ hj)
    have hia : i ≠ a := fun e => hi' (by simp [e])
    have hib : i ≠ b := fun e => hi' (by simp [e])
    have hns : ¬ Stroke p h j i := by
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (hne i hia hib).1
      · rw [Finset.mem_singleton.mp hj]
        exact (hne i hia hib).2
    rw [H.coeff_termZ_eq_zero hji hns, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl hout, Finset.sum_const_zero, Finset.sum_pair hab, ← hclose, ← add_mul] at hsum
  have hmab : (m a : ℂ) + (m b : ℂ) ≠ 0 := by
    have : ((m a + m b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (add_pos (hm a) (hm b)).ne'
    push_cast at this
    exact this
  exact mul_ne_zero hmab ((H.circle_iff_coeff a).mp ca) hsum

/-- Along a path of `h'`-strokes the coefficient of `τ^{−2}` of `h` is constant (on an `h'`-stroke
`e(h_kl) ≥ 1 > −2`). -/
theorem coeff_eq_of_path (H : Pair m p h h') {k j : Fin n}
    (hp : Relation.ReflTransGen (Stroke p h') k j) : (h j).coeff (-2) = (h k).coeff (-2) := by
  induction hp with
  | refl => rfl
  | @tail b c _ hs ih =>
    rw [← ih]
    have h1 : 1 ≤ ord h b c := ((H.edge_facts (Or.inr hs)).2.1).mp hs
    exact (H.coeff_eq_of_close hs.1 (by linarith)).symm

/-- (C3) for a colour pair. -/
theorem circle_component (H : Pair m p h h') (hm : ∀ i, 0 < m i) {k : Fin n} (hk : Circle h k) :
    ∃ j, Relation.ReflTransGen (Stroke p h) k j ∧ Circle h j ∧
      ¬ Relation.ReflTransGen (Stroke p h') k j := by
  classical
  by_contra hne
  push Not at hne
  set K := univ.filter fun j => Relation.ReflTransGen (Stroke p h) k j with hK
  have hkK : k ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ k, Relation.ReflTransGen.refl⟩
  have hsum := H.coeff_subset_sum K (-2)
  have hout : ∀ j ∈ K,
      ∑ i ∈ univ \ K, (m j : ℂ) * ((m i : ℂ) * (termZ p h j i).coeff (-2)) = 0 := by
    intro j hj
    refine Finset.sum_eq_zero fun i hi => ?_
    have hiK : i ∉ K := (Finset.mem_sdiff.mp hi).2
    have hji : j ≠ i := fun e => hiK (e ▸ hj)
    have hns : ¬ Stroke p h j i := fun hs =>
      hiK (Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hj).2.tail hs⟩)
    rw [H.coeff_termZ_eq_zero hji hns, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl hout, Finset.sum_const_zero] at hsum
  have hterm : ∀ j ∈ K, (m j : ℂ) * (h j).coeff (-2) =
      if Circle h j then (m j : ℂ) * (h k).coeff (-2) else 0 := by
    intro j hj
    split_ifs with hcj
    · rw [H.coeff_eq_of_path (hne j (Finset.mem_filter.mp hj).2 hcj)]
    · rw [show (h j).coeff (-2) = 0 from not_not.mp (mt (H.circle_iff_coeff j).mpr hcj), mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← Finset.sum_mul] at hsum
  have hpos : 0 < ∑ j ∈ K.filter (Circle h), m j :=
    Finset.sum_pos (fun i _ => hm i) ⟨k, Finset.mem_filter.mpr ⟨hkK, hk⟩⟩
  have hne0 : ∑ j ∈ K.filter (Circle h), (m j : ℂ) ≠ 0 := by
    have : ((∑ j ∈ K.filter (Circle h), m j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    push_cast at this
    exact this
  exact mul_ne_zero hne0 ((H.circle_iff_coeff k).mp hk) hsum

/-- (C4) for a colour pair. -/
theorem stroke_of_circles (H : Pair m p h h') {k l j : Fin n} (hk : Circle h k) (hj : Circle h j)
    (hl : ¬ Circle h l) (s1 : Stroke p h k l) (s2 : Stroke p h l j) (hkj : k ≠ j) : Stroke p h k j := by
  have hkl := s1.1
  have hlj := s2.1
  have z1 : ord h k l = -2 := H.ord_of_circle hk hl
  have z2 : ord h l j = -2 := by
    rw [ord_comm]
    exact H.ord_of_circle hj hl
  have e1 := (H.stroke_iff hkl).mp s1
  have e2 := (H.stroke_iff hlj).mp s2
  have u := H.symm.ultra hkl hlj hkj
  have w1 : ord h' k l = 2 := by linarith
  have w2 : ord h' l j = 2 := by linarith
  rw [w1, w2, min_self] at u
  obtain ⟨b1, b2, b3, b4⟩ := H.bounds hkj
  rw [H.stroke_iff hkj]
  linarith

/-- Rule T for a colour pair. -/
theorem ruleT (H : Pair m p h h') {k l j : Fin n} (s1 : Stroke p h k l) (s2 : Stroke p h l j)
    (s3 : Stroke p h j k) : ¬ (Circle h k ∧ ¬ Circle h l ∧ ¬ Circle h j) := by
  rintro ⟨hk, hl, hj⟩
  have z1 := H.ord_of_circle hk hl
  have t := H.tri_rule (Or.inl s1) (Or.inl s2) (Or.inl s3)
  have z2 : ord h l j = -2 := t.1.1 ▸ z1
  have hlt : ((-2 : ℚ) : WithTop ℚ) < min (h l).orderTop (h j).orderTop :=
    lt_min (lt_of_le_of_ne (H.low.1 l) (Ne.symm hl)) (lt_of_le_of_ne (H.low.1 j) (Ne.symm hj))
  have h3 := lt_of_lt_of_le hlt (H.min_le_ord s2.1)
  rw [z2] at h3
  exact lt_irrefl _ h3

end Pair

end Colour

namespace Germ

variable {n : ℕ} {m : Fin n → ℝ} (G : Germ n m)

/-! ## The diagram -/

/-- `kl` is an *edge*: a stroke of some colour (§2.4). -/
def edge (k l : Fin n) : Prop := G.zStroke k l ∨ G.wStroke k l

/-- `kl` is a `zw`-*edge*: a `z`-stroke and a `w`-stroke. -/
def zwEdge (k l : Fin n) : Prop := G.zStroke k l ∧ G.wStroke k l

/-- The edges `kl` and `k'l'` have the same kind (`z`, `w` or `zw`): they carry the same strokes. -/
def sameKind (k l k' l' : Fin n) : Prop :=
  (G.zStroke k l ↔ G.zStroke k' l') ∧ (G.wStroke k l ↔ G.wStroke k' l')

theorem ne_of_edge {k l : Fin n} (he : G.edge k l) : k ≠ l := he.elim (fun s => s.1) (fun s => s.1)

theorem edge_comm {k l : Fin n} : G.edge k l ↔ G.edge l k := by
  unfold edge
  rw [G.zStroke_comm, G.wStroke_comm]

theorem zwEdge_comm {k l : Fin n} : G.zwEdge k l ↔ G.zwEdge l k := by
  unfold zwEdge
  rw [G.zStroke_comm, G.wStroke_comm]

/-- The kinds of edges (beginning of the proof of Lemma 2.11, `lem:rules`): on an edge `kl`, `kl` is a `z`-stroke iff
`ζ_kl ≤ 1` and a `w`-stroke iff `ζ_kl ≥ 1`, and `ω_kl = f(ζ_kl)` with `f(ζ) = (4 − ζ)/3` for `ζ ≤ 1` and
`f(ζ) = 4 − 3ζ` for `ζ ≥ 1`. -/
theorem edge_kind {k l : Fin n} (he : G.edge k l) :
    (G.zStroke k l ↔ G.zeta k l ≤ 1) ∧ (G.wStroke k l ↔ 1 ≤ G.zeta k l) ∧
      ((G.zeta k l ≤ 1 ∧ G.zeta k l + 3 * G.omega k l = 4) ∨
        (1 ≤ G.zeta k l ∧ 3 * G.zeta k l + G.omega k l = 4)) :=
  G.colZ.edge_facts he

/-! ## The rules (E1)–(E6) -/

/-- **(E1)** of Lemma 2.11 (`lem:rules`), colour `z`: there is a `z`-stroke. -/
theorem E1_z : ∃ k l, G.zStroke k l := G.colZ.exists_stroke

/-- **(E1)** of Lemma 2.11 (`lem:rules`), colour `w`: there is a `w`-stroke. -/
theorem E1_w : ∃ k l, G.wStroke k l := G.colW.exists_stroke

/-- **(E2)** of Lemma 2.11 (`lem:rules`): if `ab` and `bc` are `zw`-edges (and `a ≠ c`), then `ac` is a
`zw`-edge. -/
theorem E2 {a b c : Fin n} (h1 : G.zwEdge a b) (h2 : G.zwEdge b c) (hac : a ≠ c) : G.zwEdge a c :=
  G.colZ.zw_trans h1.1 h1.2 h2.1 h2.2 hac

/-- **(E3)** of Lemma 2.11 (`lem:rules`): the three edges `ab`, `bc`, `ca` of a triangle of edges have the same kind,
equal `ζ` and equal `ω`. -/
theorem E3 {a b c : Fin n} (e1 : G.edge a b) (e2 : G.edge b c) (e3 : G.edge c a) :
    (G.sameKind a b b c ∧ G.sameKind b c c a) ∧ (G.zeta a b = G.zeta b c ∧ G.zeta b c = G.zeta c a) ∧
      (G.omega a b = G.omega b c ∧ G.omega b c = G.omega c a) := by
  obtain ⟨hz, hw, k1, k2⟩ := G.colZ.tri_rule e1 e2 e3
  exact ⟨⟨k1, k2⟩, hz, hw⟩

/-- **(E4)** of Lemma 2.11 (`lem:rules`), colour `z`: from each `zw`-edge `ab` another `z`-stroke leaves `a` or
`b`. -/
theorem E4_z (hm : ∀ i, 0 < m i) {a b : Fin n} (hab : G.zwEdge a b) :
    ∃ j, j ≠ a ∧ j ≠ b ∧ (G.zStroke a j ∨ G.zStroke b j) :=
  G.colZ.stroke_at_zw hm hab.1 hab.2

/-- **(E4)** of Lemma 2.11 (`lem:rules`), colour `w`: from each `zw`-edge `ab` another `w`-stroke leaves `a` or
`b`. -/
theorem E4_w (hm : ∀ i, 0 < m i) {a b : Fin n} (hab : G.zwEdge a b) :
    ∃ j, j ≠ a ∧ j ≠ b ∧ (G.wStroke a j ∨ G.wStroke b j) :=
  G.colW.stroke_at_zw hm hab.2 hab.1

/-- On a `zw`-edge `x_kl = 1`, so `e(p_kl) = −1`: its coefficient of `τ^{−1}` does not vanish. -/
theorem coeff_p_ne_zero {k l : Fin n} (h : G.zwEdge k l) : (G.p k l).coeff (-1) ≠ 0 := by
  have hkl := h.1.1
  apply HahnSeries.coeff_orderTop_ne
  rw [G.orderTop_p hkl, (G.O4 hkl).mpr h]

/-- Since `e(p_kl) = −x_kl ≥ −1`, a nonzero coefficient of `τ^{−1}` in `p_kl` means `x_kl = 1`: a `zw`-edge (O4). -/
theorem zwEdge_of_coeff {k l : Fin n} (hkl : k ≠ l) (hc : (G.p k l).coeff (-1) ≠ 0) : G.zwEdge k l := by
  have h1 := HahnSeries.orderTop_le_of_coeff_ne_zero hc
  rw [G.orderTop_p hkl] at h1
  have h2 : -G.x k l ≤ -1 := by exact_mod_cast h1
  exact (G.O4 hkl).mp (le_antisymm (G.O1_le hkl).2.2.2 (by linarith))

/-- **(E5)** of Lemma 2.11 (`lem:rules`), in the form used in the proof: a `zw`-edge `ab` is not the only one. The
terms `m_k m_l p_kl` of `U = E` have exponents `−x_kl ≥ −1`, with equality exactly at the `zw`-edges (O4), so a single
`zw`-edge would leave a single term of exponent `−1`. -/
theorem E5' (hm : ∀ i, 0 < m i) {a b : Fin n} (hab : G.zwEdge a b) :
    ∃ c d, G.zwEdge c d ∧ ¬ (c = a ∧ d = b) ∧ ¬ (c = b ∧ d = a) := by
  by_contra hne
  have hz : ∀ c d, G.zwEdge c d → (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
    intro c d hcd
    by_contra h'
    push Not at h'
    exact hne ⟨c, d, hcd, fun h => h'.1 h.1 h.2, fun h => h'.2 h.1 h.2⟩
  have hab' : a ≠ b := hab.1.1
  have hF : ∀ k l, k ≠ l → ¬ ((k = a ∧ l = b) ∨ (k = b ∧ l = a)) →
      ((m k : ℂ) * (m l : ℂ)) * (G.p k l).coeff (-1) = 0 := by
    intro k l hkl h'
    have h0 : (G.p k l).coeff (-1) = 0 := by
      by_contra hc
      exact h' (hz k l (G.zwEdge_of_coeff hkl hc))
    rw [h0, mul_zero]
  have hcoef : ∑ k, ∑ l ∈ univ.erase k, ((m k : ℂ) * (m l : ℂ)) * (G.p k l).coeff (-1) = 0 := by
    have h0 := congrArg (fun f : Ser => f.coeff (-1)) G.pot
    simp only [HahnSeries.coeff_sum, Colour.coeff_cS_mul] at h0
    rw [h0, Colour.coeff_cS_of_ne _ (by norm_num : (-1 : ℚ) ≠ 0)]
  have hA : ∑ l ∈ univ.erase a, ((m a : ℂ) * (m l : ℂ)) * (G.p a l).coeff (-1) =
      ((m a : ℂ) * (m b : ℂ)) * (G.p a b).coeff (-1) := by
    refine Finset.sum_eq_single b (fun l hl hlb => hF a l (Finset.ne_of_mem_erase hl).symm ?_)
      (fun h => absurd (Finset.mem_erase.mpr ⟨hab'.symm, Finset.mem_univ b⟩) h)
    rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact hlb h
    · exact hab' h
  have hB : ∑ l ∈ univ.erase b, ((m b : ℂ) * (m l : ℂ)) * (G.p b l).coeff (-1) =
      ((m b : ℂ) * (m a : ℂ)) * (G.p b a).coeff (-1) := by
    refine Finset.sum_eq_single a (fun l hl hla => hF b l (Finset.ne_of_mem_erase hl).symm ?_)
      (fun h => absurd (Finset.mem_erase.mpr ⟨hab', Finset.mem_univ a⟩) h)
    rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact hab'.symm h
    · exact hla h
  have hO : ∀ c ∈ (univ : Finset (Fin n)), c ≠ a ∧ c ≠ b →
      ∑ l ∈ univ.erase c, ((m c : ℂ) * (m l : ℂ)) * (G.p c l).coeff (-1) = 0 := by
    intro c _ hc
    refine Finset.sum_eq_zero fun l hl => hF c l (Finset.ne_of_mem_erase hl).symm ?_
    rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact hc.1 h
    · exact hc.2 h
  rw [Finset.sum_eq_add_of_mem a b (Finset.mem_univ a) (Finset.mem_univ b) hab' hO, hA, hB,
    G.p_symm b a] at hcoef
  have h2 : (2 * ((m a : ℂ) * (m b : ℂ))) * (G.p a b).coeff (-1) = 0 := by
    linear_combination hcoef
  refine mul_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero ?_ ?_)) (G.coeff_p_ne_zero hab) h2
  · exact_mod_cast (hm a).ne'
  · exact_mod_cast (hm b).ne'

/-- **(E5)** of Lemma 2.11 (`lem:rules`): the number of `zw`-edges (pairs `k < l`) is not `1`. -/
theorem E5 (hm : ∀ i, 0 < m i) : Nat.card {e : Fin n × Fin n // e.1 < e.2 ∧ G.zwEdge e.1 e.2} ≠ 1 := by
  intro h1
  obtain ⟨hsub, ⟨⟨⟨a, b⟩, hlt, hab⟩⟩⟩ := Nat.card_eq_one_iff_unique.mp h1
  obtain ⟨c, d, hcd, h1', h2'⟩ := G.E5' hm hab
  rcases lt_or_gt_of_ne hcd.1.1 with hlt' | hlt'
  · have e := Subsingleton.elim (α := {e : Fin n × Fin n // e.1 < e.2 ∧ G.zwEdge e.1 e.2})
      ⟨(c, d), hlt', hcd⟩ ⟨(a, b), hlt, hab⟩
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at e
    exact h1' e
  · have e := Subsingleton.elim (α := {e : Fin n × Fin n // e.1 < e.2 ∧ G.zwEdge e.1 e.2})
      ⟨(d, c), hlt', G.zwEdge_comm.mp hcd⟩ ⟨(a, b), hlt, hab⟩
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at e
    exact h2' ⟨e.2, e.1⟩

/-- **(E6)** of Lemma 2.11 (`lem:rules`): if `ab`, `bc`, `cd` and `da` are edges (`a, b, c, d` distinct), then `ab`
and `cd` have equal `ζ`, equal `ω` and the same kind, and so have `bc` and `da`. -/
theorem E6 {a b c d : Fin n} (hac : a ≠ c) (hbd : b ≠ d) (e1 : G.edge a b) (e2 : G.edge b c)
    (e3 : G.edge c d) (e4 : G.edge d a) :
    (G.zeta a b = G.zeta c d ∧ G.omega a b = G.omega c d ∧ G.sameKind a b c d) ∧
      (G.zeta b c = G.zeta d a ∧ G.omega b c = G.omega d a ∧ G.sameKind b c d a) :=
  G.colZ.quad_rule hac hbd e1 e2 e3 e4

/-! ## The rules (C1)–(C4) -/

/-- **(C1)** of Lemma 2.11 (`lem:rules`), colour `z`: a body without a `z`-stroke is not `z`-circled, and a body
with exactly one `z`-stroke is `z`-circled. -/
theorem C1_z (hm : ∀ i, 0 < m i) (k : Fin n) :
    ((∀ l, ¬ G.zStroke k l) → ¬ G.zCircle k) ∧ ((∃! l, G.zStroke k l) → G.zCircle k) :=
  ⟨G.colZ.not_circle_of_no_stroke, fun ⟨l, hl, hu⟩ => G.colZ.circle_of_unique_stroke (hm l).ne' hl hu⟩

/-- **(C1)** of Lemma 2.11 (`lem:rules`), colour `w`: a body without a `w`-stroke is not `w`-circled, and a body
with exactly one `w`-stroke is `w`-circled. -/
theorem C1_w (hm : ∀ i, 0 < m i) (k : Fin n) :
    ((∀ l, ¬ G.wStroke k l) → ¬ G.wCircle k) ∧ ((∃! l, G.wStroke k l) → G.wCircle k) :=
  ⟨G.colW.not_circle_of_no_stroke, fun ⟨l, hl, hu⟩ => G.colW.circle_of_unique_stroke (hm l).ne' hl hu⟩

/-- **(C2)** of Lemma 2.11 (`lem:rules`), colour `z`: no `w`-stroke joins a `z`-circled body to a body that is not
`z`-circled. -/
theorem C2_z {k l : Fin n} (hs : G.wStroke k l) : G.zCircle k ↔ G.zCircle l :=
  G.colZ.circle_iff_of_stroke' hs

/-- **(C2)** of Lemma 2.11 (`lem:rules`), colour `w`: no `z`-stroke joins a `w`-circled body to a body that is not
`w`-circled. -/
theorem C2_w {k l : Fin n} (hs : G.zStroke k l) : G.wCircle k ↔ G.wCircle l :=
  G.colW.circle_iff_of_stroke' hs

/-- **(C3)** of Lemma 2.11 (`lem:rules`), colour `z`: if `k` is `z`-circled, some `z`-circled body of the
`z`-component of `k` lies outside the `w`-component of `k`. -/
theorem C3_z (hm : ∀ i, 0 < m i) {k : Fin n} (hk : G.zCircle k) :
    ∃ j, Relation.ReflTransGen G.zStroke k j ∧ G.zCircle j ∧ ¬ Relation.ReflTransGen G.wStroke k j :=
  G.colZ.circle_component hm hk

/-- **(C3)** of Lemma 2.11 (`lem:rules`), colour `w`: if `k` is `w`-circled, some `w`-circled body of the
`w`-component of `k` lies outside the `z`-component of `k`. -/
theorem C3_w (hm : ∀ i, 0 < m i) {k : Fin n} (hk : G.wCircle k) :
    ∃ j, Relation.ReflTransGen G.wStroke k j ∧ G.wCircle j ∧ ¬ Relation.ReflTransGen G.zStroke k j :=
  G.colW.circle_component hm hk

/-- The remark after Lemma 2.11 (`lem:rules`): by (C3), a `z`-component never contains exactly one `z`-circled
body. -/
theorem C3_z' (hm : ∀ i, 0 < m i) {k : Fin n} (hk : G.zCircle k) :
    ∃ j, j ≠ k ∧ Relation.ReflTransGen G.zStroke k j ∧ G.zCircle j := by
  obtain ⟨j, h1, h2, h3⟩ := G.C3_z hm hk
  refine ⟨j, fun e => h3 ?_, h1, h2⟩
  rw [e]

/-- The remark after Lemma 2.11 (`lem:rules`): by (C3), a `w`-component never contains exactly one `w`-circled
body. -/
theorem C3_w' (hm : ∀ i, 0 < m i) {k : Fin n} (hk : G.wCircle k) :
    ∃ j, j ≠ k ∧ Relation.ReflTransGen G.wStroke k j ∧ G.wCircle j := by
  obtain ⟨j, h1, h2, h3⟩ := G.C3_w hm hk
  refine ⟨j, fun e => h3 ?_, h1, h2⟩
  rw [e]

/-- **(C4)** of Lemma 2.11 (`lem:rules`), colour `z`: if `k` and `j` are `z`-circled, `l` is not, and `kl` and `lj`
are `z`-strokes, then `kj` is a `z`-stroke (`k ≠ j`). -/
theorem C4_z {k l j : Fin n} (hk : G.zCircle k) (hj : G.zCircle j) (hl : ¬ G.zCircle l)
    (s1 : G.zStroke k l) (s2 : G.zStroke l j) (hkj : k ≠ j) : G.zStroke k j :=
  G.colZ.stroke_of_circles hk hj hl s1 s2 hkj

/-- **(C4)** of Lemma 2.11 (`lem:rules`), colour `w`: if `k` and `j` are `w`-circled, `l` is not, and `kl` and `lj`
are `w`-strokes, then `kj` is a `w`-stroke (`k ≠ j`). -/
theorem C4_w {k l j : Fin n} (hk : G.wCircle k) (hj : G.wCircle j) (hl : ¬ G.wCircle l)
    (s1 : G.wStroke k l) (s2 : G.wStroke l j) (hkj : k ≠ j) : G.wStroke k j :=
  G.colW.stroke_of_circles hk hj hl s1 s2 hkj

/-! ## Consequences -/

/-- The consequence of (E3) stated after the proof of Lemma 2.11 (`lem:rules`): if all pairs of a set `S` of bodies
are edges (for four bodies: all six pairs), then all of them have the same kind, equal `ζ` and equal `ω`. -/
theorem edges_clique {S : Finset (Fin n)} (hS : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → G.edge k l) {k l k' l' : Fin n}
    (hk : k ∈ S) (hl : l ∈ S) (hk' : k' ∈ S) (hl' : l' ∈ S) (hkl : k ≠ l) (hkl' : k' ≠ l') :
    G.zeta k l = G.zeta k' l' ∧ G.omega k l = G.omega k' l' ∧ G.sameKind k l k' l' := by
  have share : ∀ {v x y : Fin n}, v ∈ S → x ∈ S → y ∈ S → v ≠ x → v ≠ y → x ≠ y →
      G.zeta v x = G.zeta v y := by
    intro v x y hv hx hy hvx hvy hxy
    have t := G.E3 (hS v hv x hx hvx) (hS x hx y hy hxy) (hS y hy v hv hvy.symm)
    rw [G.zeta_comm v y]
    exact t.2.1.1.trans t.2.1.2
  have hζ : G.zeta k l = G.zeta k' l' := by
    by_cases h1 : k' = k
    · rw [h1]
      by_cases h2 : l' = l
      · rw [h2]
      · rw [h1] at hkl'
        exact share hk hl hl' hkl hkl' (Ne.symm h2)
    · by_cases h3 : k' = l
      · rw [h3]
        by_cases h4 : l' = k
        · rw [h4]
          exact G.zeta_comm k l
        · rw [h3] at hkl'
          rw [G.zeta_comm k l]
          exact share hl hk hl' hkl.symm hkl' (Ne.symm h4)
      · by_cases h5 : l' = k
        · rw [h5, G.zeta_comm k' k]
          exact share hk hl hk' hkl (Ne.symm h1) (Ne.symm h3)
        · by_cases h6 : l' = l
          · rw [h6, G.zeta_comm k l, G.zeta_comm k' l]
            exact share hl hk hk' hkl.symm (Ne.symm h3) (Ne.symm h1)
          · calc G.zeta k l = G.zeta k l' := share hk hl hl' hkl (Ne.symm h5) (Ne.symm h6)
              _ = G.zeta l' k := G.zeta_comm k l'
              _ = G.zeta l' k' := share hl' hk hk' h5 (Ne.symm hkl') (Ne.symm h1)
              _ = G.zeta k' l' := G.zeta_comm l' k'
  exact ⟨hζ, G.colZ.edge_eq (hS k hk l hl hkl) (hS k' hk' l' hl' hkl') hζ,
    G.colZ.edge_kind_eq (hS k hk l hl hkl) (hS k' hk' l' hl' hkl') hζ⟩

/-- The consequence of (E3) stated after the proof of Lemma 2.11 (`lem:rules`), for four bodies: if all six pairs of
`{a, b, c, d}` are edges, they have the same kind, equal `ζ` and equal `ω`. -/
theorem edges_four {a b c d : Fin n} (hab : G.edge a b) (hac : G.edge a c) (had : G.edge a d)
    (hbc : G.edge b c) (hbd : G.edge b d) (hcd : G.edge c d) {k l k' l' : Fin n}
    (hk : k ∈ ({a, b, c, d} : Finset (Fin n))) (hl : l ∈ ({a, b, c, d} : Finset (Fin n)))
    (hk' : k' ∈ ({a, b, c, d} : Finset (Fin n))) (hl' : l' ∈ ({a, b, c, d} : Finset (Fin n)))
    (hkl : k ≠ l) (hkl' : k' ≠ l') :
    G.zeta k l = G.zeta k' l' ∧ G.omega k l = G.omega k' l' ∧ G.sameKind k l k' l' := by
  refine G.edges_clique (S := {a, b, c, d}) ?_ hk hl hk' hl' hkl hkl'
  intro x hx y hy hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hxy
    | assumption
    | exact G.edge_comm.mp ‹_›

/-- **Rule T** (§3, `sec:diagrams`), colour `z`: a triangle `klj` of `z`-strokes does not have exactly one `z`-circled
vertex. Indeed, if `k` is the only one, `ζ_kl = −2` by (O6), so `ζ_lj = −2` by (E3), against
`ζ_lj ≥ min(a_l, a_j) > −2`. -/
theorem ruleT_z {k l j : Fin n} (s1 : G.zStroke k l) (s2 : G.zStroke l j) (s3 : G.zStroke j k) :
    ¬ (G.zCircle k ∧ ¬ G.zCircle l ∧ ¬ G.zCircle j) :=
  G.colZ.ruleT s1 s2 s3

/-- **Rule T** (§3, `sec:diagrams`), colour `w`: a triangle `klj` of `w`-strokes does not have exactly one `w`-circled
vertex. -/
theorem ruleT_w {k l j : Fin n} (s1 : G.wStroke k l) (s2 : G.wStroke l j) (s3 : G.wStroke j k) :
    ¬ (G.wCircle k ∧ ¬ G.wCircle l ∧ ¬ G.wCircle j) :=
  G.colW.ruleT s1 s2 s3

end Germ

end

end CC6Full
