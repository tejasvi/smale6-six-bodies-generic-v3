import CC6Full.Germ.Identities

/-!
# Trees of exponents (§4.1: Definition 4.1, Lemma 4.2, Lemma 4.3 (b))

Paper §4.1 (`ss:trees`). The points of `B = {1, …, n, O}` are `Pt n = Option (Fin n)`: `some k` is the body `k`
and `none` is the centre of mass `O`, whose positions are `z_O = w_O = 0`.

## Lemma 4.2, first part

* `Germ.zpos`, `Germ.wpos`: the positions `z_p`, `w_p` of the points; `Germ.hz p q = e(z_p − z_q)` and
  `Germ.hw p q = e(w_p − w_q)` (as `orderTop`, so `⊤` if the difference vanishes). In general `hOf pos` is the
  exponent of the differences of any family `pos` of series indexed by the points.
* `IsUltra h`: `h p p = ⊤`, `h` is symmetric and `h p r ≥ min (h p q) (h q r)`, so that `−h` is an ultrametric.
  `Germ.isUltra_hz`, `Germ.isUltra_hw`, with `Germ.hz_comm`, `Germ.hz_ultra`.
* `Germ.hz_eq_top`: for `p ≠ q`, `hz p q = ⊤` only if `{p, q} = {k, O}` for a body with `z_k = 0`, and
  `Germ.z_eq_zero_unique`: at most one body has `z_k = 0`. The same for `w`.
* `ball h p e = {q | e ≤ h p q}`, the closed ball of radius `−e`; `ball_laminar`: two balls are disjoint or
  nested, so the closed balls form a hierarchy.

## Definition 4.1: trees without heights

A tree is encoded by its internal nodes, each given by the set of the points below it (`TreeShape.nodes`, a list of
subsets of `B`), and by the body that shares the leaf of `O`, if any (`TreeShape.leafO`); every other point has a
leaf of its own. Two points are on the same leaf (`TreeShape.SameLeaf`) if they are equal or are `O` and the body on
its leaf. The tree conditions are `TreeShape.WF`: the whole set `B` is a node (the root), the nodes form a laminar
family, every node is a union of leaves, and every node contains two points on different leaves. This encoding
needs no parent pointers: the order of the tree is inclusion.

* `TreeShape.lca p q`: the lowest common ancestor of the leaves of `p` and `q`, the intersection of the nodes
  containing `p` and `q` (a node, `TreeShape.lca_mem`).
* `TreeShape.child v p`: the points below the child of the node `v` that contains `p`, namely the points `r` of `v`
  on the leaf of `p` or with `lca(p, r)` strictly below `v`. `TreeShape.children v` is the set of the children of
  `v`, as sets of points. The children partition the node (`TreeShape.child_eq_of_mem`), and every node has at
  least two children (`TreeShape.child_ne_self`). `TreeShape.sameLeaf_iff` describes the leaves.
* `IsFirst v c`: the child `c` of `v` is the first child `c₀`, the one containing the point of least index of `v`
  (in the order `O < 1 < ⋯ < n`, `Pt.idx`).
* `TreeShape.Realizes T h hts`: `T` is a tree, the heights `hts` increase strictly from a node to the nodes below
  it, `h p q = hts (lca p q)` for points on different leaves and `h p q = ⊤` for points on the same leaf.

The existence of the tree of an ultrametric (Lemma 4.2, first statement) is in `CC6Full/Germ/TreeExists.lean`.

## Lemma 4.2, second part: node coordinates

`coordOf pos hts v c = [pos_a − pos_o]_{h_v}`, where `a` is the point of least index of `c` and `o` that of `v`;
`Germ.xcoord`, `Germ.ycoord` for the two colours. For a tree realizing `hOf pos`:

* `TreeShape.Realizes.coord_child`: `X_{v,c(p)} = [pos_p − pos_o]_{h_v}` for every `p` below `v`, so the coordinate
  depends only on the child containing `p`;
* `TreeShape.Realizes.coord_first`: `X_{v,c₀} = 0`;
* `TreeShape.Realizes.lc_eq`: `lc(pos_p − pos_q) = X_{v,c(p)} − X_{v,c(q)}` for `v = lca(p, q)`
  (`Germ.lc_z_eq`, `Germ.lc_w_eq`);
* `TreeShape.Realizes.coord_ne`: the coordinates of different children of a node are distinct.

## Lemma 4.3 (b)

`TreeShape.Realizes.three_children`, `Germ.three_children_z`, `Germ.three_children_w`: for positive masses the
root of each tree of a germ has at least three children.
-/

namespace CC6Full

open Finset

/-- The points of `B = {1, …, n, O}` (§4.1): `some k` is the body `k`, `none` is the centre of mass `O`. -/
abbrev Pt (n : ℕ) := Option (Fin n)

namespace Pt

variable {n : ℕ}

/-- The index of a point in the order `O < 1 < ⋯ < n`. The first child of a node is the child containing the point
of least index below the node. -/
def idx : Pt n → ℕ
  | none => 0
  | some k => k.val + 1

theorem idx_injective : Function.Injective (idx : Pt n → ℕ) := by
  rintro (_ | a) (_ | b) h
  · rfl
  · simp [idx] at h
  · simp [idx] at h
  · simp only [idx, Nat.add_right_cancel_iff] at h
    exact congrArg some (Fin.ext h)

/-- The point of least index of a set (`O` for the empty set). -/
noncomputable def least (s : Finset (Pt n)) : Pt n :=
  if h : s.Nonempty then (s.exists_min_image idx h).choose else none

theorem least_spec {s : Finset (Pt n)} (h : s.Nonempty) :
    least s ∈ s ∧ ∀ q ∈ s, idx (least s) ≤ idx q := by
  rw [least, dite_eq_left h]
  exact (s.exists_min_image idx h).choose_spec

theorem least_mem {s : Finset (Pt n)} (h : s.Nonempty) : least s ∈ s := (least_spec h).1

theorem least_eq {s : Finset (Pt n)} {p : Pt n} (hp : p ∈ s) (hle : ∀ q ∈ s, idx p ≤ idx q) :
    least s = p := by
  have h := least_spec ⟨p, hp⟩
  exact idx_injective (le_antisymm (h.2 p hp) (hle _ h.1))

end Pt

/-! ## Ultrametrics and balls -/

section ultra

variable {α : Type*}

/-- An ultrametric in exponent form (§4.1): `h p p = ⊤`, `h` is symmetric and `h p r ≥ min (h p q) (h q r)`; the
ultrametric distance is `−h`. -/
structure IsUltra (h : α → α → WithTop ℚ) : Prop where
  self : ∀ p, h p p = ⊤
  comm : ∀ p q, h p q = h q p
  ultra : ∀ p q r, min (h p q) (h q r) ≤ h p r

variable [Fintype α] [DecidableEq α] {h : α → α → WithTop ℚ}

/-- The closed ball `{q | e ≤ h p q}`, of radius `−e` for the ultrametric `−h`. -/
def ball (h : α → α → WithTop ℚ) (p : α) (e : WithTop ℚ) : Finset α := univ.filter fun q => e ≤ h p q

omit [DecidableEq α] in
theorem mem_ball {p q : α} {e : WithTop ℚ} : q ∈ ball h p e ↔ e ≤ h p q := by simp [ball]

omit [DecidableEq α] in
/-- Every point of a closed ball is a centre of it. -/
theorem ball_eq_of_mem (H : IsUltra h) {p q : α} {e : WithTop ℚ} (hq : q ∈ ball h p e) :
    ball h q e = ball h p e := by
  rw [mem_ball] at hq
  ext r
  simp only [mem_ball]
  constructor
  · intro hr
    exact le_trans (le_min hq hr) (H.ultra p q r)
  · intro hr
    exact le_trans (le_min (by rw [H.comm]; exact hq) hr) (H.ultra q p r)

/-- Lemma 4.2 (`lem:tree`): the closed balls of an ultrametric form a hierarchy; two of them are disjoint or
nested. -/
theorem ball_laminar (H : IsUltra h) (p q : α) (e f : WithTop ℚ) :
    Disjoint (ball h p e) (ball h q f) ∨ ball h p e ⊆ ball h q f ∨ ball h q f ⊆ ball h p e := by
  by_cases hd : Disjoint (ball h p e) (ball h q f)
  · exact Or.inl hd
  rw [Finset.not_disjoint_iff] at hd
  obtain ⟨r, hrp, hrq⟩ := hd
  rw [← ball_eq_of_mem H hrp, ← ball_eq_of_mem H hrq]
  rcases le_total e f with hef | hef
  · refine Or.inr (Or.inr fun s hs => ?_)
    rw [mem_ball] at hs ⊢
    exact hef.trans hs
  · refine Or.inr (Or.inl fun s hs => ?_)
    rw [mem_ball] at hs ⊢
    exact hef.trans hs

end ultra

/-! ## Positions of the points and their exponents -/

noncomputable section

/-- The exponents `e(pos_p − pos_q)` of the differences of a family of series indexed by the points of `B`. -/
def hOf {n : ℕ} (pos : Pt n → Ser) (p q : Pt n) : WithTop ℚ := (pos p - pos q).orderTop

theorem isUltra_hOf {n : ℕ} (pos : Pt n → Ser) : IsUltra (hOf pos) where
  self p := by simp [hOf]
  comm p q := by
    unfold hOf
    rw [← neg_sub, HahnSeries.orderTop_neg]
  ultra p q r := by
    unfold hOf
    have e : pos p - pos r = (pos p - pos q) + (pos q - pos r) := by ring
    rw [e]
    exact HahnSeries.min_orderTop_le_orderTop_add

namespace Germ

variable {n : ℕ} {m : Fin n → ℝ} (G : Germ n m)

/-- The positions `z_p` of the points of `B` (§4.1), with `z_O = 0`. -/
def zpos : Pt n → Ser
  | none => 0
  | some k => G.z k

/-- The positions `w_p` of the points of `B` (§4.1), with `w_O = 0`. -/
def wpos : Pt n → Ser
  | none => 0
  | some k => G.w k

@[simp] theorem zpos_none : G.zpos none = 0 := rfl

@[simp] theorem zpos_some (k : Fin n) : G.zpos (some k) = G.z k := rfl

@[simp] theorem wpos_none : G.wpos none = 0 := rfl

@[simp] theorem wpos_some (k : Fin n) : G.wpos (some k) = G.w k := rfl

/-- `hz p q = e(z_p − z_q)` (§4.1). -/
def hz : Pt n → Pt n → WithTop ℚ := hOf G.zpos

/-- `hw p q = e(w_p − w_q)` (§4.1). -/
def hw : Pt n → Pt n → WithTop ℚ := hOf G.wpos

theorem hz_def (p q : Pt n) : G.hz p q = (G.zpos p - G.zpos q).orderTop := rfl

theorem hw_def (p q : Pt n) : G.hw p q = (G.wpos p - G.wpos q).orderTop := rfl

/-- Lemma 4.2: `−e(z_p − z_q)` is an ultrametric on `B`. -/
theorem isUltra_hz : IsUltra G.hz := isUltra_hOf G.zpos

/-- Lemma 4.2: `−e(w_p − w_q)` is an ultrametric on `B`. -/
theorem isUltra_hw : IsUltra G.hw := isUltra_hOf G.wpos

theorem hz_comm (p q : Pt n) : G.hz p q = G.hz q p := G.isUltra_hz.comm p q

theorem hw_comm (p q : Pt n) : G.hw p q = G.hw q p := G.isUltra_hw.comm p q

/-- The ultrametric inequality `e(z_p − z_r) ≥ min(e(z_p − z_q), e(z_q − z_r))`. -/
theorem hz_ultra (p q r : Pt n) : min (G.hz p q) (G.hz q r) ≤ G.hz p r := G.isUltra_hz.ultra p q r

theorem hw_ultra (p q r : Pt n) : min (G.hw p q) (G.hw q r) ≤ G.hw p r := G.isUltra_hw.ultra p q r

/-- `hz k l = ζ_kl` for bodies `k ≠ l`. -/
theorem hz_some_some {k l : Fin n} (h : k ≠ l) : G.hz (some k) (some l) = (G.zeta k l : WithTop ℚ) :=
  G.orderTop_z_sub h

/-- `hw k l = ω_kl` for bodies `k ≠ l`. -/
theorem hw_some_some {k l : Fin n} (h : k ≠ l) : G.hw (some k) (some l) = (G.omega k l : WithTop ℚ) :=
  G.orderTop_w_sub h

/-- `hz k O = a_k = e(z_k)`. -/
theorem hz_some_none (k : Fin n) : G.hz (some k) none = (G.z k).orderTop := by
  rw [hz_def, zpos_some, zpos_none, sub_zero]

/-- `hw k O = b_k = e(w_k)`. -/
theorem hw_some_none (k : Fin n) : G.hw (some k) none = (G.w k).orderTop := by
  rw [hw_def, wpos_some, wpos_none, sub_zero]

theorem hz_eq_top_iff {p q : Pt n} : G.hz p q = ⊤ ↔ G.zpos p = G.zpos q := by
  rw [hz_def, HahnSeries.orderTop_eq_top, sub_eq_zero]

theorem hw_eq_top_iff {p q : Pt n} : G.hw p q = ⊤ ↔ G.wpos p = G.wpos q := by
  rw [hw_def, HahnSeries.orderTop_eq_top, sub_eq_zero]

/-- Lemma 4.2 (§4.1): for `p ≠ q` the exponent `e(z_p − z_q)` is finite unless `{p, q} = {k, O}` for a body `k`
with `z_k = 0`. -/
theorem hz_eq_top {p q : Pt n} (hpq : p ≠ q) (h : G.hz p q = ⊤) :
    ∃ k, G.z k = 0 ∧ ((p = some k ∧ q = none) ∨ (p = none ∧ q = some k)) := by
  rw [hz_eq_top_iff] at h
  rcases p with _ | a <;> rcases q with _ | b
  · exact absurd rfl hpq
  · exact ⟨b, by simpa using h.symm, Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨a, by simpa using h, Or.inl ⟨rfl, rfl⟩⟩
  · exfalso
    have hab : a ≠ b := fun e => hpq (congrArg some e)
    exact G.z_sub_ne_zero hab (sub_eq_zero.mpr (by simpa using h))

/-- Lemma 4.2 (§4.1): for `p ≠ q` the exponent `e(w_p − w_q)` is finite unless `{p, q} = {k, O}` for a body `k`
with `w_k = 0`. -/
theorem hw_eq_top {p q : Pt n} (hpq : p ≠ q) (h : G.hw p q = ⊤) :
    ∃ k, G.w k = 0 ∧ ((p = some k ∧ q = none) ∨ (p = none ∧ q = some k)) := by
  rw [hw_eq_top_iff] at h
  rcases p with _ | a <;> rcases q with _ | b
  · exact absurd rfl hpq
  · exact ⟨b, by simpa using h.symm, Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨a, by simpa using h, Or.inl ⟨rfl, rfl⟩⟩
  · exfalso
    have hab : a ≠ b := fun e => hpq (congrArg some e)
    exact G.w_sub_ne_zero hab (sub_eq_zero.mpr (by simpa using h))

/-- At most one body has `z_k = 0`, since `z_k − z_l ≠ 0` for `k ≠ l` (§4.1). -/
theorem z_eq_zero_unique {k l : Fin n} (hk : G.z k = 0) (hl : G.z l = 0) : k = l := by
  by_contra hkl
  exact G.z_sub_ne_zero hkl (by rw [hk, hl, sub_zero])

/-- At most one body has `w_k = 0`. -/
theorem w_eq_zero_unique {k l : Fin n} (hk : G.w k = 0) (hl : G.w l = 0) : k = l := by
  by_contra hkl
  exact G.w_sub_ne_zero hkl (by rw [hk, hl, sub_zero])

end Germ

end

/-! ## Intersections of chains of sets -/

section foldr

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem foldr_inter_eq_univ_or_mem (L : List (Finset α)) (hL : ∀ A ∈ L, ∀ B ∈ L, A ⊆ B ∨ B ⊆ A) :
    L.foldr (· ∩ ·) univ = univ ∨ L.foldr (· ∩ ·) univ ∈ L := by
  induction L with
  | nil => exact Or.inl rfl
  | cons A L ih =>
    simp only [List.foldr_cons]
    rcases ih fun B hB C hC => hL B (List.mem_cons_of_mem _ hB) C (List.mem_cons_of_mem _ hC) with h | h
    · right
      rw [h, Finset.inter_univ]
      exact List.mem_cons_self
    · rcases hL A List.mem_cons_self _ (List.mem_cons_of_mem _ h) with h' | h'
      · right
        rw [Finset.inter_eq_left.mpr h']
        exact List.mem_cons_self
      · right
        rw [Finset.inter_eq_right.mpr h']
        exact List.mem_cons_of_mem _ h

theorem mem_foldr_inter {L : List (Finset α)} {x : α} (h : ∀ A ∈ L, x ∈ A) :
    x ∈ L.foldr (· ∩ ·) univ := by
  induction L with
  | nil => exact mem_univ x
  | cons A L ih =>
    simp only [List.foldr_cons]
    exact mem_inter.mpr ⟨h A List.mem_cons_self, ih fun B hB => h B (List.mem_cons_of_mem _ hB)⟩

theorem foldr_inter_subset {L : List (Finset α)} {A : Finset α} (hA : A ∈ L) :
    L.foldr (· ∩ ·) univ ⊆ A := by
  induction L with
  | nil => simp at hA
  | cons B L ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hA with rfl | hA
    · exact inter_subset_left
    · exact inter_subset_right.trans (ih hA)

end foldr

/-! ## Trees without heights (Definition 4.1) -/

/-- A tree without heights (Definition 4.1, `def:tree`): its internal nodes, each given by the set of the points
below it, and the body that shares the leaf of `O`, if any; every other point has a leaf of its own. The tree
conditions are `TreeShape.WF`. -/
structure TreeShape (n : ℕ) where
  /-- the internal nodes, as the sets of points below them -/
  nodes : List (Finset (Pt n))
  /-- the body on the leaf of `O`, if any -/
  leafO : Option (Fin n)
  deriving DecidableEq

/-- `c` is the first child `c₀` of the node `v`: it contains the point of least index of `v` (Lemma 4.2,
`X_{v,c₀} = 0`). -/
def IsFirst {n : ℕ} (v c : Finset (Pt n)) : Prop := ∃ p ∈ c, ∀ q ∈ v, Pt.idx p ≤ Pt.idx q

instance {n : ℕ} (v c : Finset (Pt n)) : Decidable (IsFirst v c) := by
  unfold IsFirst
  infer_instance

namespace TreeShape

variable {n : ℕ} (T : TreeShape n)

/-- The representative of the leaf of a point: the body on the leaf of `O` is sent to `O`. -/
def lrep (p : Pt n) : Pt n := if p = T.leafO then none else p

/-- `p` and `q` lie on the same leaf of `T`. -/
def SameLeaf (p q : Pt n) : Prop := T.lrep p = T.lrep q

instance (p q : Pt n) : Decidable (T.SameLeaf p q) := inferInstanceAs (Decidable (T.lrep p = T.lrep q))

theorem sameLeaf_refl (p : Pt n) : T.SameLeaf p p := rfl

variable {T} in
theorem SameLeaf.symm {p q : Pt n} (h : T.SameLeaf p q) : T.SameLeaf q p := Eq.symm h

variable {T} in
theorem SameLeaf.trans {p q r : Pt n} (h : T.SameLeaf p q) (h' : T.SameLeaf q r) : T.SameLeaf p r :=
  Eq.trans h h'

/-- Two distinct bodies are never on the same leaf. -/
theorem not_sameLeaf_some {k l : Fin n} (hkl : k ≠ l) : ¬ T.SameLeaf (some k) (some l) := by
  intro h
  unfold SameLeaf lrep at h
  by_cases h1 : (some k : Pt n) = T.leafO <;> by_cases h2 : (some l : Pt n) = T.leafO
  · exact hkl (Option.some_injective _ (h1.trans h2.symm))
  · rw [ite_eq_left h1, ite_eq_right h2] at h
    simp at h
  · rw [ite_eq_right h1, ite_eq_left h2] at h
    simp at h
  · rw [ite_eq_right h1, ite_eq_right h2] at h
    exact hkl (Option.some_injective _ h)

/-- Two points share a leaf if they are equal or are `O` and the body on its leaf. -/
theorem sameLeaf_iff {p q : Pt n} :
    T.SameLeaf p q ↔ p = q ∨ ∃ k, T.leafO = some k ∧ ((p = some k ∧ q = none) ∨ (p = none ∧ q = some k)) := by
  obtain ⟨nodes, o⟩ := T
  unfold SameLeaf lrep
  rcases o with _ | k <;> rcases p with _ | a <;> rcases q with _ | b
  all_goals (try simp)
  all_goals (try aesop)

/-- The tree conditions of Definition 4.1 in the encoding by internal nodes: the whole set is a node (the root), the
nodes form a laminar family, every node is a union of leaves, and every node contains two points on different
leaves (so that every node has at least two children, `child_ne_self`). -/
structure WF : Prop where
  root : (univ : Finset (Pt n)) ∈ T.nodes
  laminar : ∀ A ∈ T.nodes, ∀ B ∈ T.nodes, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B
  closed : ∀ A ∈ T.nodes, ∀ p q, T.SameLeaf p q → p ∈ A → q ∈ A
  two : ∀ A ∈ T.nodes, ∃ p ∈ A, ∃ q ∈ A, ¬ T.SameLeaf p q

/-- The tree conditions are decidable (for a checker over explicit trees). -/
instance instDecidableWF : Decidable T.WF :=
  have _h1 : Decidable ((univ : Finset (Pt n)) ∈ T.nodes) := inferInstance
  have _h2 : Decidable (∀ A ∈ T.nodes, ∀ B ∈ T.nodes, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) := inferInstance
  have _h3 : Decidable (∀ A ∈ T.nodes, ∀ p q, T.SameLeaf p q → p ∈ A → q ∈ A) := inferInstance
  have _h4 : Decidable (∀ A ∈ T.nodes, ∃ p ∈ A, ∃ q ∈ A, ¬ T.SameLeaf p q) := inferInstance
  decidable_of_iff (((univ : Finset (Pt n)) ∈ T.nodes) ∧
      (∀ A ∈ T.nodes, ∀ B ∈ T.nodes, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) ∧
      (∀ A ∈ T.nodes, ∀ p q, T.SameLeaf p q → p ∈ A → q ∈ A) ∧
      (∀ A ∈ T.nodes, ∃ p ∈ A, ∃ q ∈ A, ¬ T.SameLeaf p q))
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-- The lowest common ancestor of the leaves of `p` and `q`: the intersection of the nodes containing `p` and `q`
(a node if `T.WF`, `lca_mem`). -/
def lca (p q : Pt n) : Finset (Pt n) := (T.nodes.filter fun A => p ∈ A ∧ q ∈ A).foldr (· ∩ ·) univ

/-- The points below the child of the node `v` that contains `p` (for `p ∈ v`): the points `r` of `v` that are on the
leaf of `p` or have `lca(p, r)` strictly below `v`. -/
def child (v : Finset (Pt n)) (p : Pt n) : Finset (Pt n) := v.filter fun r => T.SameLeaf p r ∨ T.lca p r ⊂ v

/-- The children of the node `v`, as sets of points. -/
def children (v : Finset (Pt n)) : Finset (Finset (Pt n)) := v.image (T.child v)

theorem mem_lca_left (p q : Pt n) : p ∈ T.lca p q := by
  apply mem_foldr_inter
  intro A hA
  simp only [List.mem_filter, decide_eq_true_eq] at hA
  exact hA.2.1

theorem mem_lca_right (p q : Pt n) : q ∈ T.lca p q := by
  apply mem_foldr_inter
  intro A hA
  simp only [List.mem_filter, decide_eq_true_eq] at hA
  exact hA.2.2

/-- The lowest common ancestor lies below every node containing `p` and `q`. -/
theorem lca_subset {A : Finset (Pt n)} (hA : A ∈ T.nodes) {p q : Pt n} (hp : p ∈ A) (hq : q ∈ A) :
    T.lca p q ⊆ A :=
  foldr_inter_subset (by simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hA, hp, hq⟩)

theorem lca_comm (p q : Pt n) : T.lca p q = T.lca q p := by
  unfold lca
  congr 1
  exact List.filter_congr fun A _ => by simp only [Bool.decide_and, Bool.and_comm]

/-- The lowest common ancestor is a node. -/
theorem lca_mem (hT : T.WF) (p q : Pt n) : T.lca p q ∈ T.nodes := by
  have hL : ∀ A ∈ T.nodes.filter (fun A => p ∈ A ∧ q ∈ A),
      ∀ B ∈ T.nodes.filter (fun A => p ∈ A ∧ q ∈ A), A ⊆ B ∨ B ⊆ A := by
    intro A hA B hB
    simp only [List.mem_filter, decide_eq_true_eq] at hA hB
    rcases hT.laminar A hA.1 B hB.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd hB.2.1 (Finset.disjoint_left.mp h hA.2.1)
  rcases foldr_inter_eq_univ_or_mem _ hL with h | h
  · rw [lca, h]
    exact hT.root
  · exact (List.mem_filter.mp h).1

theorem mem_child {v : Finset (Pt n)} {p r : Pt n} :
    r ∈ T.child v p ↔ r ∈ v ∧ (T.SameLeaf p r ∨ T.lca p r ⊂ v) := by
  simp [child]

theorem mem_child_self {v : Finset (Pt n)} {p : Pt n} (hp : p ∈ v) : p ∈ T.child v p :=
  T.mem_child.mpr ⟨hp, Or.inl (T.sameLeaf_refl p)⟩

theorem child_subset (v : Finset (Pt n)) (p : Pt n) : T.child v p ⊆ v := filter_subset _ _

theorem child_mem_children {v : Finset (Pt n)} {p : Pt n} (hp : p ∈ v) : T.child v p ∈ T.children v :=
  mem_image_of_mem _ hp

/-- Points of a node `v` that are not in the same child of `v` have `lca(p, q) = v`. -/
theorem lca_eq_of_not_mem_child {v : Finset (Pt n)} (hv : v ∈ T.nodes) {p q : Pt n} (hp : p ∈ v)
    (hq : q ∈ v) (hpq : q ∉ T.child v p) : ¬ T.SameLeaf p q ∧ T.lca p q = v := by
  rw [mem_child] at hpq
  push Not at hpq
  obtain ⟨h1, h2⟩ := hpq hq
  refine ⟨h1, ?_⟩
  have hsub := T.lca_subset hv hp hq
  by_contra hne
  exact h2 (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)

/-- Being in the same child of a node is transitive. -/
theorem sameChild_trans (hT : T.WF) {v : Finset (Pt n)} {x y z : Pt n} (hxy : T.SameLeaf x y ∨ T.lca x y ⊂ v)
    (hyz : T.SameLeaf y z ∨ T.lca y z ⊂ v) : T.SameLeaf x z ∨ T.lca x z ⊂ v := by
  rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
  · exact Or.inl (hxy.trans hyz)
  · right
    have hx : x ∈ T.lca y z := hT.closed _ (T.lca_mem hT y z) y x hxy.symm (T.mem_lca_left y z)
    exact Finset.ssubset_of_subset_of_ssubset (T.lca_subset (T.lca_mem hT y z) hx (T.mem_lca_right y z)) hyz
  · right
    have hz : z ∈ T.lca x y := hT.closed _ (T.lca_mem hT x y) y z hyz (T.mem_lca_right x y)
    exact Finset.ssubset_of_subset_of_ssubset (T.lca_subset (T.lca_mem hT x y) (T.mem_lca_left x y) hz) hxy
  · right
    rcases hT.laminar _ (T.lca_mem hT x y) _ (T.lca_mem hT y z) with h | h | h
    · exact Finset.ssubset_of_subset_of_ssubset
        (T.lca_subset (T.lca_mem hT y z) (h (T.mem_lca_left x y)) (T.mem_lca_right y z)) hyz
    · exact Finset.ssubset_of_subset_of_ssubset
        (T.lca_subset (T.lca_mem hT x y) (T.mem_lca_left x y) (h (T.mem_lca_right y z))) hxy
    · exact absurd (T.mem_lca_left y z) (Finset.disjoint_left.mp h (T.mem_lca_right x y))

/-- The children of a node partition it: a point of the child of `p` has the same child. -/
theorem child_eq_of_mem (hT : T.WF) {v : Finset (Pt n)} {p q : Pt n} (hq : q ∈ T.child v p) :
    T.child v q = T.child v p := by
  have hpq := (T.mem_child.mp hq).2
  have hqp : T.SameLeaf q p ∨ T.lca q p ⊂ v := by
    rcases hpq with h | h
    · exact Or.inl h.symm
    · exact Or.inr (T.lca_comm q p ▸ h)
  ext r
  rw [mem_child, mem_child]
  exact ⟨fun ⟨hr, h⟩ => ⟨hr, T.sameChild_trans hT hpq h⟩, fun ⟨hr, h⟩ => ⟨hr, T.sameChild_trans hT hqp h⟩⟩

/-- Every node has at least two children: the child of a point is not the whole node. -/
theorem child_ne_self (hT : T.WF) {v : Finset (Pt n)} (hv : v ∈ T.nodes) (p : Pt n) :
    T.child v p ≠ v := by
  intro hc
  have hall : ∀ r ∈ v, T.SameLeaf p r ∨ T.lca p r ⊂ v := fun r hr =>
    (T.mem_child.mp (hc.symm ▸ hr : r ∈ T.child v p)).2
  set D := v.filter fun r => ¬ T.SameLeaf p r with hD
  rcases D.eq_empty_or_nonempty with hD0 | hDne
  · obtain ⟨a, ha, b, hb, hab⟩ := hT.two v hv
    have hs : ∀ r ∈ v, T.SameLeaf p r := by
      intro r hr
      by_contra h
      have hrD : r ∈ D := mem_filter.mpr ⟨hr, h⟩
      rw [hD0] at hrD
      simp at hrD
    exact hab ((hs a ha).symm.trans (hs b hb))
  · obtain ⟨q, hqD, hqmax⟩ := D.exists_max_image (fun r => (T.lca p r).card) hDne
    have hqv : q ∈ v := (mem_filter.mp hqD).1
    have hpq : ¬ T.SameLeaf p q := (mem_filter.mp hqD).2
    have hW : T.lca p q ⊂ v := (hall q hqv).resolve_left hpq
    have hsub : v ⊆ T.lca p q := by
      intro r hr
      by_cases hs : T.SameLeaf p r
      · exact hT.closed _ (T.lca_mem hT p q) p r hs (T.mem_lca_left p q)
      · have hrD : r ∈ D := mem_filter.mpr ⟨hr, hs⟩
        rcases hT.laminar _ (T.lca_mem hT p r) _ (T.lca_mem hT p q) with h | h | h
        · exact h (T.mem_lca_right p r)
        · have heq : T.lca p q = T.lca p r := eq_of_subset_of_card_le h (hqmax r hrD)
          rw [heq]
          exact T.mem_lca_right p r
        · exact absurd (T.mem_lca_left p q) (Finset.disjoint_left.mp h (T.mem_lca_left p r))
    exact (Finset.ssubset_iff_subset_ne.mp hW).2 (subset_antisymm hW.subset hsub)

/-! ## Trees with heights -/

/-- The tree `T` with the heights `hts` on its internal nodes realizes the exponents `h` (Definition 4.1,
Lemma 4.2): `T` is a tree, the heights increase strictly from a node to the nodes below it, `h p q` is the height of
`lca(p, q)` for points on different leaves, and `h p q = ⊤` for points on the same leaf. -/
structure Realizes (h : Pt n → Pt n → WithTop ℚ) (hts : Finset (Pt n) → ℚ) : Prop where
  wf : T.WF
  same : ∀ p q, T.SameLeaf p q → h p q = ⊤
  diff : ∀ p q, ¬ T.SameLeaf p q → h p q = (hts (T.lca p q) : WithTop ℚ)
  mono : ∀ A ∈ T.nodes, ∀ B ∈ T.nodes, A ⊂ B → hts B < hts A

end TreeShape

/-! ## Node coordinates (Lemma 4.2) -/

noncomputable section

/-- The node coordinate `X_{v,c} = [pos_a − pos_o]_{h_v}` of Lemma 4.2 (`lem:tree`), where `a` is the point of
least index of the child `c` and `o` that of the node `v`. -/
def coordOf {n : ℕ} (pos : Pt n → Ser) (hts : Finset (Pt n) → ℚ) (v c : Finset (Pt n)) : ℂ :=
  (pos (Pt.least c) - pos (Pt.least v)).coeff (hts v)

namespace TreeShape.Realizes

variable {n : ℕ} {T : TreeShape n} {pos : Pt n → Ser} {hts : Finset (Pt n) → ℚ}

/-- Points below one child of `v` have differences of exponent larger than `h_v`: `[pos_p − pos_r]_{h_v} = 0` for
`r` in the child of `v` containing `p`. -/
theorem coeff_child (hR : T.Realizes (hOf pos) hts) {v : Finset (Pt n)} (hv : v ∈ T.nodes) {p r : Pt n}
    (hr : r ∈ T.child v p) : (pos p - pos r).coeff (hts v) = 0 := by
  obtain ⟨_, hr⟩ := T.mem_child.mp hr
  by_cases hs : T.SameLeaf p r
  · have h0 := hR.same p r hs
    rw [hOf, HahnSeries.orderTop_eq_top] at h0
    rw [h0, HahnSeries.coeff_zero]
  · have hlt : T.lca p r ⊂ v := hr.resolve_left hs
    have h1 : (pos p - pos r).orderTop = (hts (T.lca p r) : WithTop ℚ) := hR.diff p r hs
    have h2 := hR.mono _ (T.lca_mem hR.wf p r) _ hv hlt
    apply Ser.coeff_eq_zero_of_lt
    rw [h1]
    exact WithTop.coe_lt_coe.mpr h2

/-- Lemma 4.2: `X_{v,c(p)} = [pos_p − pos_o]_{h_v}` for every point `p` below `v`, where `o` is the point of least
index of `v`; so the coordinate depends only on the child `c(p)`. -/
theorem coord_child (hR : T.Realizes (hOf pos) hts) {v : Finset (Pt n)} (hv : v ∈ T.nodes) {p : Pt n}
    (hp : p ∈ v) : coordOf pos hts v (T.child v p) = (pos p - pos (Pt.least v)).coeff (hts v) := by
  have hne : (T.child v p).Nonempty := ⟨p, T.mem_child_self hp⟩
  have h0 := hR.coeff_child hv (Pt.least_mem hne)
  unfold coordOf
  have e : pos (Pt.least (T.child v p)) - pos (Pt.least v) =
      (pos p - pos (Pt.least v)) - (pos p - pos (Pt.least (T.child v p))) := by ring
  rw [e, Ser.coeff_sub, h0, sub_zero]

/-- Lemma 4.2: `X_{v,c₀} = 0` for the first child `c₀`. -/
theorem coord_first (hR : T.Realizes (hOf pos) hts) {v : Finset (Pt n)} (hv : v ∈ T.nodes) {p : Pt n}
    (hp : p ∈ v) (hf : IsFirst v (T.child v p)) : coordOf pos hts v (T.child v p) = 0 := by
  rw [hR.coord_child hv hp]
  obtain ⟨a, ha, hmin⟩ := hf
  rw [Pt.least_eq (T.child_subset v p ha) hmin]
  exact hR.coeff_child hv ha

/-- Lemma 4.2 (`lem:tree`): `lc(pos_p − pos_q) = X_{v,c(p)} − X_{v,c(q)}` for points on different leaves, where
`v = lca(p, q)` and `c(p)`, `c(q)` are the children of `v` containing `p` and `q`. -/
theorem lc_eq (hR : T.Realizes (hOf pos) hts) {p q : Pt n} (hpq : ¬ T.SameLeaf p q) :
    (pos p - pos q).leadingCoeff = coordOf pos hts (T.lca p q) (T.child (T.lca p q) p) -
      coordOf pos hts (T.lca p q) (T.child (T.lca p q) q) := by
  have hv := T.lca_mem hR.wf p q
  rw [hR.coord_child hv (T.mem_lca_left p q), hR.coord_child hv (T.mem_lca_right p q), ← Ser.coeff_sub]
  have e : pos p - pos (Pt.least (T.lca p q)) - (pos q - pos (Pt.least (T.lca p q))) = pos p - pos q := by ring
  rw [e]
  exact (Ser.coeff_of_orderTop_eq (hR.diff p q hpq)).symm

/-- Lemma 4.2: the node coordinates of different children of a node are distinct. -/
theorem coord_ne (hR : T.Realizes (hOf pos) hts) {v : Finset (Pt n)} (hv : v ∈ T.nodes) {p q : Pt n}
    (hp : p ∈ v) (hq : q ∈ v) (hpq : q ∉ T.child v p) :
    coordOf pos hts v (T.child v p) ≠ coordOf pos hts v (T.child v q) := by
  obtain ⟨hs, hl⟩ := T.lca_eq_of_not_mem_child hv hp hq hpq
  have h := hR.lc_eq hs
  rw [hl] at h
  rw [← sub_ne_zero, ← h]
  have hord : (pos p - pos q).orderTop = (hts (T.lca p q) : WithTop ℚ) := hR.diff p q hs
  exact HahnSeries.leadingCoeff_ne_zero.mpr (Ser.ne_zero_of_orderTop_eq hord)

/-- Lemma 4.3 (b) (`lem:constraints`), for any family of positions with `pos_O = 0` and centre of mass
`Σ_k m_k pos_k = 0` at positive masses: the root of a tree realizing `hOf pos` has at least three children.
Proof of the paper: the coefficient of exponent `h_r` in `Σ_k m_k pos_k = 0` is
`Σ_{c ≠ c_O} (X_{r,c} − X_{r,c_O}) M_c`; with only two children it would be `X M_c ≠ 0`. -/
theorem three_children {m : Fin n → ℝ} (hm : ∀ k, 0 < m k) (h0 : pos none = 0)
    (hcom : ∑ k, cS (m k) * pos (some k) = 0) (hR : T.Realizes (hOf pos) hts) :
    3 ≤ (T.children univ).card := by
  by_contra hlt
  push Not at hlt
  have hT := hR.wf
  set cO := T.child univ none with hcO_def
  have hcO : cO ∈ T.children univ := T.child_mem_children (mem_univ _)
  have hOcO : (none : Pt n) ∈ cO := T.mem_child_self (mem_univ _)
  obtain ⟨p₁, hp₁⟩ : ∃ p₁, p₁ ∉ cO := by
    by_contra h
    push Not at h
    exact T.child_ne_self hT hT.root none (eq_univ_of_forall h)
  set c₁ := T.child univ p₁ with hc₁_def
  have hc₁ : c₁ ∈ T.children univ := T.child_mem_children (mem_univ _)
  have hp₁c₁ : p₁ ∈ c₁ := T.mem_child_self (mem_univ _)
  have hne : cO ≠ c₁ := fun h => hp₁ (h ▸ hp₁c₁)
  have hpair : T.children univ = {cO, c₁} := by
    symm
    apply eq_of_subset_of_card_le
    · intro c hc
      simp only [mem_insert, mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact hcO
      · exact hc₁
    · rw [card_pair hne]
      omega
  have hall : ∀ q, q ∈ cO ∨ q ∈ c₁ := by
    intro q
    have hq : T.child univ q ∈ T.children univ := T.child_mem_children (mem_univ _)
    rw [hpair, mem_insert, mem_singleton] at hq
    rcases hq with hq | hq
    · left
      rw [← hq]
      exact T.mem_child_self (mem_univ _)
    · right
      rw [← hq]
      exact T.mem_child_self (mem_univ _)
  obtain ⟨a, rfl⟩ : ∃ a, p₁ = some a := by
    rcases p₁ with _ | a
    · exact absurd hOcO hp₁
    · exact ⟨a, rfl⟩
  set e := hts univ with he_def
  -- the body `a` is below `c₁`, so `e(pos_a) = h_r` and its coefficient of exponent `h_r` is not zero
  have hnsl : ¬ T.SameLeaf none (some a) := fun h => hp₁ (T.mem_child.mpr ⟨mem_univ _, Or.inl h⟩)
  have hlca : T.lca none (some a) = univ := by
    by_contra h
    exact hp₁ (T.mem_child.mpr ⟨mem_univ _, Or.inr (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, h⟩)⟩)
  have hord : (pos (some a)).orderTop = (e : WithTop ℚ) := by
    have h1 : (pos none - pos (some a)).orderTop = (hts (T.lca none (some a)) : WithTop ℚ) :=
      hR.diff none (some a) hnsl
    rw [hlca, h0, zero_sub, HahnSeries.orderTop_neg] at h1
    exact h1
  have hlc : (pos (some a)).coeff e ≠ 0 := by
    rw [Ser.coeff_of_orderTop_eq hord]
    exact HahnSeries.leadingCoeff_ne_zero.mpr (Ser.ne_zero_of_orderTop_eq hord)
  -- the coefficient of exponent `h_r` of each term of the centre of mass
  have key : ∀ k, (m k : ℂ) * (pos (some k)).coeff e =
      if some k ∉ cO then (m k : ℂ) * (pos (some a)).coeff e else 0 := by
    intro k
    by_cases hk : some k ∈ cO
    · rw [ite_eq_right (not_not.mpr hk)]
      have h1 : (pos none - pos (some k)).coeff e = 0 := hR.coeff_child hT.root hk
      rw [h0, zero_sub, Ser.coeff_neg, neg_eq_zero] at h1
      rw [h1, mul_zero]
    · rw [ite_eq_left hk]
      have hk1 : some k ∈ c₁ := (hall (some k)).resolve_left hk
      have h1 : (pos (some a) - pos (some k)).coeff e = 0 := hR.coeff_child hT.root hk1
      rw [Ser.coeff_sub, sub_eq_zero] at h1
      rw [h1]
  have hcoef := congrArg (fun f : Ser => f.coeff e) hcom
  simp only [Ser.coeff_sum_cS_mul, HahnSeries.coeff_zero] at hcoef
  rw [Finset.sum_congr rfl fun k _ => key k, ← Finset.sum_filter, ← Finset.sum_mul] at hcoef
  have hS : (univ.filter fun k : Fin n => some k ∉ cO).Nonempty := ⟨a, mem_filter.mpr ⟨mem_univ _, hp₁⟩⟩
  have hpos : (0 : ℝ) < ∑ k ∈ univ.filter (fun k : Fin n => some k ∉ cO), m k :=
    Finset.sum_pos (fun k _ => hm k) hS
  rcases mul_eq_zero.mp hcoef with h1 | h1
  · rw [← Complex.ofReal_sum] at h1
    exact hpos.ne' (Complex.ofReal_eq_zero.mp h1)
  · exact hlc h1

end TreeShape.Realizes

namespace Germ

variable {n : ℕ} {m : Fin n → ℝ} (G : Germ n m)

/-- The node coordinates `X_{v,c}` of a tree of `z` (Lemma 4.2). -/
def xcoord (hts : Finset (Pt n) → ℚ) (v c : Finset (Pt n)) : ℂ := coordOf G.zpos hts v c

/-- The node coordinates `Y_{v,c}` of a tree of `w` (Lemma 4.2). -/
def ycoord (hts : Finset (Pt n) → ℚ) (v c : Finset (Pt n)) : ℂ := coordOf G.wpos hts v c

variable {G} {T : TreeShape n} {hts : Finset (Pt n) → ℚ}

/-- Lemma 4.2 (`lem:tree`): `lc(z_p − z_q) = X_{v,c(p)} − X_{v,c(q)}` with `v = lca(p, q)`. -/
theorem lc_z_eq (hR : T.Realizes G.hz hts) {p q : Pt n} (hpq : ¬ T.SameLeaf p q) :
    (G.zpos p - G.zpos q).leadingCoeff =
      G.xcoord hts (T.lca p q) (T.child (T.lca p q) p) - G.xcoord hts (T.lca p q) (T.child (T.lca p q) q) :=
  TreeShape.Realizes.lc_eq (pos := G.zpos) hR hpq

/-- Lemma 4.2 (`lem:tree`): `lc(w_p − w_q) = Y_{v,c(p)} − Y_{v,c(q)}` with `v = lca(p, q)`. -/
theorem lc_w_eq (hR : T.Realizes G.hw hts) {p q : Pt n} (hpq : ¬ T.SameLeaf p q) :
    (G.wpos p - G.wpos q).leadingCoeff =
      G.ycoord hts (T.lca p q) (T.child (T.lca p q) p) - G.ycoord hts (T.lca p q) (T.child (T.lca p q) q) :=
  TreeShape.Realizes.lc_eq (pos := G.wpos) hR hpq

variable (G) in
/-- Lemma 4.3 (b) (`lem:constraints`): for positive masses the root of a tree of `z` has at least three
children. -/
theorem three_children_z (hm : ∀ k, 0 < m k) (hR : T.Realizes G.hz hts) : 3 ≤ (T.children univ).card :=
  TreeShape.Realizes.three_children (pos := G.zpos) hm rfl G.com_z hR

variable (G) in
/-- Lemma 4.3 (b) (`lem:constraints`): for positive masses the root of a tree of `w` has at least three
children. -/
theorem three_children_w (hm : ∀ k, 0 < m k) (hR : T.Realizes G.hw hts) : 3 ≤ (T.children univ).card :=
  TreeShape.Realizes.three_children (pos := G.wpos) hm rfl G.com_w hR

end Germ

end

end CC6Full
