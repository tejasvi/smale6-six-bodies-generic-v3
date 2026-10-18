import CC6Full.Germ.Tree

/-!
# The tree of an ultrametric (Lemma 4.2, existence)

Paper Lemma 4.2 (`lem:tree`), first statement, existence part: the closed balls with at least two leaves of the
ultrametric `−h` on `B` are the internal nodes of a tree realizing `h`, and the height of such a ball is the least
value of `h` on two of its points (proof of Lemma 4.2: "the tree is the tree of this hierarchy").

* `diam h A = min_{p, q ∈ A} h p q`; `ultraNodes h`: the balls `ball h p (h p q)` with `h p q ≠ ⊤`;
  `TreeShape.ofUltra h leafO`: the tree with these internal nodes and the body `leafO` on the leaf of `O`;
  `ultraHeights h A`: the height `diam h A` of a node.
* `TreeShape.realizes_ofUltra`: if `h` is an ultrametric whose infinite values are exactly the pairs on one leaf and
  some value is finite, the tree `ofUltra h leafO` with the heights `ultraHeights h` realizes `h`.
* `Germ.exists_tree_z`, `Germ.exists_tree_w`: a germ with at least two bodies has trees of `z` and of `w`, with the
  body `k` with `z_k = 0` (resp. `w_k = 0`), if any, on the leaf of `O` (§4.1).
-/

namespace CC6Full

open Finset

noncomputable section

variable {n : ℕ} {h : Pt n → Pt n → WithTop ℚ}

/-- The least value `min_{p, q ∈ A} h p q` of `h` on a set, the height of a ball. -/
def diam (h : Pt n → Pt n → WithTop ℚ) (A : Finset (Pt n)) : WithTop ℚ := (A ×ˢ A).inf fun pq => h pq.1 pq.2

theorem diam_le {A : Finset (Pt n)} {p q : Pt n} (hp : p ∈ A) (hq : q ∈ A) : diam h A ≤ h p q :=
  show (A ×ˢ A).inf (fun pq : Pt n × Pt n => h pq.1 pq.2) ≤ (fun pq : Pt n × Pt n => h pq.1 pq.2) (p, q) from
    Finset.inf_le (mem_product.mpr ⟨hp, hq⟩)

theorem le_diam {A : Finset (Pt n)} {e : WithTop ℚ} (H : ∀ p ∈ A, ∀ q ∈ A, e ≤ h p q) : e ≤ diam h A :=
  Finset.le_inf fun pq hpq => H pq.1 (mem_product.mp hpq).1 pq.2 (mem_product.mp hpq).2

/-- The closed balls with two points at finite distance: `ball h p (h p q)` with `h p q ≠ ⊤`. -/
def ultraNodes (h : Pt n → Pt n → WithTop ℚ) : Finset (Finset (Pt n)) :=
  ((univ : Finset (Pt n × Pt n)).filter fun pq => h pq.1 pq.2 ≠ ⊤).image fun pq => ball h pq.1 (h pq.1 pq.2)

theorem mem_ultraNodes {A : Finset (Pt n)} : A ∈ ultraNodes h ↔ ∃ p q, h p q ≠ ⊤ ∧ ball h p (h p q) = A := by
  simp [ultraNodes]

/-- The tree of an ultrametric (Lemma 4.2): its internal nodes are the closed balls with at least two leaves. -/
def TreeShape.ofUltra (h : Pt n → Pt n → WithTop ℚ) (leafO : Option (Fin n)) : TreeShape n :=
  ⟨(ultraNodes h).toList, leafO⟩

/-- The heights of the tree of an ultrametric: the least value of `h` on a node. -/
def ultraHeights (h : Pt n → Pt n → WithTop ℚ) (A : Finset (Pt n)) : ℚ := (diam h A).untopD 0

theorem mem_ofUltra_nodes {leafO : Option (Fin n)} {A : Finset (Pt n)} :
    A ∈ (TreeShape.ofUltra h leafO).nodes ↔ A ∈ ultraNodes h :=
  Finset.mem_toList

theorem mem_ball_self (H : IsUltra h) (p : Pt n) (e : WithTop ℚ) : p ∈ ball h p e :=
  mem_ball.mpr (by rw [H.self]; exact le_top)

/-- The least value of `h` on the ball `ball h p (h p q)` is `h p q`. -/
theorem diam_ball (H : IsUltra h) (p q : Pt n) : diam h (ball h p (h p q)) = h p q := by
  apply le_antisymm
  · exact diam_le (mem_ball_self H p _) (mem_ball.mpr le_rfl)
  · apply le_diam
    intro a ha b hb
    rw [mem_ball] at ha hb
    calc h p q ≤ min (h a p) (h p b) := le_min (by rw [H.comm a p]; exact ha) hb
      _ ≤ h a b := H.ultra a p b

/-- A node is the ball of its height around any of its points. -/
theorem node_eq_ball (H : IsUltra h) {A : Finset (Pt n)} (hA : A ∈ ultraNodes h) {p : Pt n} (hp : p ∈ A) :
    A = ball h p (diam h A) := by
  obtain ⟨s, t, -, rfl⟩ := mem_ultraNodes.mp hA
  rw [diam_ball H]
  exact (ball_eq_of_mem H hp).symm

theorem diam_ne_top (H : IsUltra h) {A : Finset (Pt n)} (hA : A ∈ ultraNodes h) : diam h A ≠ ⊤ := by
  obtain ⟨s, t, hst, rfl⟩ := mem_ultraNodes.mp hA
  rw [diam_ball H]
  exact hst

theorem coe_ultraHeights (H : IsUltra h) {A : Finset (Pt n)} (hA : A ∈ ultraNodes h) :
    ((ultraHeights h A : ℚ) : WithTop ℚ) = diam h A := by
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (diam_ne_top H hA)
  rw [ultraHeights, ← ha, WithTop.untopD_coe]

/-- The tree of an ultrametric satisfies the tree conditions. -/
theorem TreeShape.wf_ofUltra (H : IsUltra h) (leafO : Option (Fin n))
    (htop : ∀ p q, h p q = ⊤ ↔ (TreeShape.ofUltra h leafO).SameLeaf p q) (htwo : ∃ p q, h p q ≠ ⊤) :
    (TreeShape.ofUltra h leafO).WF where
  root := by
    rw [mem_ofUltra_nodes, mem_ultraNodes]
    obtain ⟨a, b, hab⟩ := htwo
    obtain ⟨q, -, hq⟩ := (univ : Finset (Pt n)).exists_min_image (h none) univ_nonempty
    have hfin : h none q ≠ ⊤ := by
      intro htq
      have ha := hq a (mem_univ a)
      have hb := hq b (mem_univ b)
      rw [htq, top_le_iff] at ha hb
      apply hab
      apply top_le_iff.mp
      calc (⊤ : WithTop ℚ) = min (h a none) (h none b) := by rw [H.comm, ha, hb, min_self]
        _ ≤ h a b := H.ultra a none b
    refine ⟨none, q, hfin, ?_⟩
    ext r
    simp only [mem_ball, mem_univ, iff_true]
    exact hq r (mem_univ r)
  laminar := by
    intro A hA B hB
    rw [mem_ofUltra_nodes] at hA hB
    obtain ⟨p, q, -, rfl⟩ := mem_ultraNodes.mp hA
    obtain ⟨p', q', -, rfl⟩ := mem_ultraNodes.mp hB
    rcases ball_laminar H p p' (h p q) (h p' q') with hd | hs | hs
    · exact Or.inr (Or.inr hd)
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
  closed := by
    intro A hA p q hpq hpA
    rw [mem_ofUltra_nodes] at hA
    obtain ⟨s, t, -, rfl⟩ := mem_ultraNodes.mp hA
    rw [mem_ball] at hpA ⊢
    have h1 : h p q = ⊤ := (htop p q).mpr hpq
    calc h s t ≤ min (h s p) (h p q) := le_min hpA (by rw [h1]; exact le_top)
      _ ≤ h s q := H.ultra s p q
  two := by
    intro A hA
    rw [mem_ofUltra_nodes] at hA
    obtain ⟨s, t, hst, rfl⟩ := mem_ultraNodes.mp hA
    exact ⟨s, mem_ball_self H s _, t, mem_ball.mpr le_rfl, fun hs => hst ((htop s t).mpr hs)⟩

/-- **Lemma 4.2** (`lem:tree`), existence: if `h` is an ultrametric whose infinite values are exactly the pairs on
one leaf and some value of `h` is finite, the tree of its closed balls with the heights `min_{p,q ∈ A} h p q`
realizes `h`. -/
theorem TreeShape.realizes_ofUltra (H : IsUltra h) (leafO : Option (Fin n))
    (htop : ∀ p q, h p q = ⊤ ↔ (TreeShape.ofUltra h leafO).SameLeaf p q) (htwo : ∃ p q, h p q ≠ ⊤) :
    (TreeShape.ofUltra h leafO).Realizes h (ultraHeights h) where
  wf := TreeShape.wf_ofUltra H leafO htop htwo
  same p q hpq := (htop p q).mpr hpq
  diff p q hpq := by
    have hT := TreeShape.wf_ofUltra H leafO htop htwo
    have hfin : h p q ≠ ⊤ := fun h0 => hpq ((htop p q).mp h0)
    have hB : ball h p (h p q) ∈ (TreeShape.ofUltra h leafO).nodes :=
      mem_ofUltra_nodes.mpr (mem_ultraNodes.mpr ⟨p, q, hfin, rfl⟩)
    have hlca : (TreeShape.ofUltra h leafO).lca p q = ball h p (h p q) := by
      refine Finset.Subset.antisymm ((TreeShape.ofUltra h leafO).lca_subset hB (mem_ball_self H p _)
        (mem_ball.mpr le_rfl)) ?_
      have hL := (TreeShape.ofUltra h leafO).lca_mem hT p q
      rw [mem_ofUltra_nodes] at hL
      obtain ⟨s, t, -, hst⟩ := mem_ultraNodes.mp hL
      have hp' := (TreeShape.ofUltra h leafO).mem_lca_left p q
      have hq' := (TreeShape.ofUltra h leafO).mem_lca_right p q
      rw [← hst] at hp' hq' ⊢
      rw [mem_ball] at hp' hq'
      intro r hr
      rw [mem_ball] at hr ⊢
      have h1 : h s t ≤ h p q := le_trans (le_min (by rw [H.comm p s]; exact hp') hq') (H.ultra p s q)
      exact le_trans (le_min hp' (le_trans h1 hr)) (H.ultra s p r)
    rw [hlca, coe_ultraHeights H (mem_ultraNodes.mpr ⟨p, q, hfin, rfl⟩), diam_ball H]
  mono A hA B hB hAB := by
    rw [mem_ofUltra_nodes] at hA hB
    obtain ⟨hsub, hne⟩ := Finset.ssubset_iff_subset_ne.mp hAB
    have hle : diam h B ≤ diam h A := Finset.inf_mono (product_subset_product hsub hsub)
    have hne' : diam h B ≠ diam h A := by
      intro heq
      obtain ⟨s, t, -, hst⟩ := mem_ultraNodes.mp hA
      have hsA : s ∈ A := hst ▸ mem_ball_self H s _
      have e1 := node_eq_ball H hA hsA
      have e2 := node_eq_ball H hB (hsub hsA)
      rw [heq] at e2
      exact hne (e1.trans e2.symm)
    have hlt : diam h B < diam h A := lt_of_le_of_ne hle hne'
    rw [← coe_ultraHeights H hA, ← coe_ultraHeights H hB] at hlt
    exact WithTop.coe_lt_coe.mp hlt

namespace Germ

variable {m : Fin n → ℝ} (G : Germ n m)

open Classical in
/-- The body on the leaf of `O` in the tree of `z`: the body with `z_k = 0`, if any (§4.1). -/
def zLeafO : Option (Fin n) := if hk : ∃ k, G.z k = 0 then some hk.choose else none

open Classical in
/-- The body on the leaf of `O` in the tree of `w`: the body with `w_k = 0`, if any. -/
def wLeafO : Option (Fin n) := if hk : ∃ k, G.w k = 0 then some hk.choose else none

theorem z_eq_zero_of_zLeafO {k : Fin n} (hk : G.zLeafO = some k) : G.z k = 0 := by
  unfold zLeafO at hk
  split_ifs at hk with h0
  · rw [← Option.some_injective _ hk]
    exact h0.choose_spec

theorem zLeafO_eq_some {k : Fin n} (hk : G.z k = 0) : G.zLeafO = some k := by
  have h0 : ∃ k, G.z k = 0 := ⟨k, hk⟩
  rw [zLeafO, dite_eq_left h0]
  exact congrArg some (G.z_eq_zero_unique h0.choose_spec hk)

theorem w_eq_zero_of_wLeafO {k : Fin n} (hk : G.wLeafO = some k) : G.w k = 0 := by
  unfold wLeafO at hk
  split_ifs at hk with h0
  · rw [← Option.some_injective _ hk]
    exact h0.choose_spec

theorem wLeafO_eq_some {k : Fin n} (hk : G.w k = 0) : G.wLeafO = some k := by
  have h0 : ∃ k, G.w k = 0 := ⟨k, hk⟩
  rw [wLeafO, dite_eq_left h0]
  exact congrArg some (G.w_eq_zero_unique h0.choose_spec hk)

/-- Lemma 4.2 (§4.1): `e(z_p − z_q) = ⊤` exactly for the points on one leaf of a tree with the body `zLeafO` on the
leaf of `O`. -/
theorem hz_eq_top_iff_sameLeaf {T : TreeShape n} (hT : T.leafO = G.zLeafO) (p q : Pt n) :
    G.hz p q = ⊤ ↔ T.SameLeaf p q := by
  rw [TreeShape.sameLeaf_iff]
  constructor
  · intro h0
    by_cases hpq : p = q
    · exact Or.inl hpq
    · obtain ⟨k, hk, hk'⟩ := G.hz_eq_top hpq h0
      exact Or.inr ⟨k, hT.trans (G.zLeafO_eq_some hk), hk'⟩
  · rintro (rfl | ⟨k, hk, hk'⟩)
    · exact G.isUltra_hz.self p
    · have hz0 : G.z k = 0 := G.z_eq_zero_of_zLeafO (hT ▸ hk)
      rcases hk' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hz_some_none, hz0, HahnSeries.orderTop_zero]
      · rw [hz_comm, hz_some_none, hz0, HahnSeries.orderTop_zero]

/-- `e(w_p − w_q) = ⊤` exactly for the points on one leaf of a tree with the body `wLeafO` on the leaf of `O`. -/
theorem hw_eq_top_iff_sameLeaf {T : TreeShape n} (hT : T.leafO = G.wLeafO) (p q : Pt n) :
    G.hw p q = ⊤ ↔ T.SameLeaf p q := by
  rw [TreeShape.sameLeaf_iff]
  constructor
  · intro h0
    by_cases hpq : p = q
    · exact Or.inl hpq
    · obtain ⟨k, hk, hk'⟩ := G.hw_eq_top hpq h0
      exact Or.inr ⟨k, hT.trans (G.wLeafO_eq_some hk), hk'⟩
  · rintro (rfl | ⟨k, hk, hk'⟩)
    · exact G.isUltra_hw.self p
    · have hw0 : G.w k = 0 := G.w_eq_zero_of_wLeafO (hT ▸ hk)
      rcases hk' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hw_some_none, hw0, HahnSeries.orderTop_zero]
      · rw [hw_comm, hw_some_none, hw0, HahnSeries.orderTop_zero]

/-- **Lemma 4.2** (`lem:tree`): a germ with at least two bodies has a tree of `z`. -/
theorem exists_tree_z (hn : 2 ≤ n) : ∃ (T : TreeShape n) (hts : Finset (Pt n) → ℚ), T.Realizes G.hz hts := by
  refine ⟨TreeShape.ofUltra G.hz G.zLeafO, ultraHeights G.hz,
    TreeShape.realizes_ofUltra G.isUltra_hz _ (G.hz_eq_top_iff_sameLeaf rfl) ?_⟩
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  exact ⟨some ⟨0, by omega⟩, some ⟨1, by omega⟩, by rw [G.hz_some_some h01]; exact WithTop.coe_ne_top⟩

/-- **Lemma 4.2** (`lem:tree`): a germ with at least two bodies has a tree of `w`. -/
theorem exists_tree_w (hn : 2 ≤ n) : ∃ (T : TreeShape n) (hts : Finset (Pt n) → ℚ), T.Realizes G.hw hts := by
  refine ⟨TreeShape.ofUltra G.hw G.wLeafO, ultraHeights G.hw,
    TreeShape.realizes_ofUltra G.isUltra_hw _ (G.hw_eq_top_iff_sameLeaf rfl) ?_⟩
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  exact ⟨some ⟨0, by omega⟩, some ⟨1, by omega⟩, by rw [G.hw_some_some h01]; exact WithTop.coe_ne_top⟩

end Germ

end

end CC6Full
