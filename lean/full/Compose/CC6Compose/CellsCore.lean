import CC6Compose.EnumCore
import CC6Full.Germ.Cell
import L6Sound.F2S.StoredSem
import L6F2.Check

/-!
# Bridge: the trees of a germ as trees of the specification search, and the conditions `Cond`

The specification search of the certificate project (`L6F2S`, Proposition 4.5) works with trees whose nodes are bit
masks of the points `0, …, 5` (the bodies) and `6` (the centre of mass `O`), with heights `ℕ → ℚ` on the masks
(`L6.F2S.ExpTree`). Its completeness theorem (`L6.F2S.search_complete`, `L6.F2S.cell_stored`) applies to every pair of
complete trees with heights satisfying `L6.F2S.Cond D`: the conditions of Lemma 4.3 for the diagram `D` and
`ℓ(x) ≤ 0`. This file converts the trees of a germ (`TreeShape 6` with heights realizing `Germ.hz`, `Germ.hw`, Lemma
4.2) and proves every field of `Cond` from the results proved for germs.

* `ptN`: the number of a point (`none ↦ 6`); `maskOf A`: the mask of a set of points; `setOfMask c`: its inverse.
* `toTS T`: the tree with the masks of the nodes of `T` (without repetition) and the number of the body on the leaf
  of `O`; `toExp T hts`: with the heights `c ↦ hts (setOfMask c)`, so that `(toExp T hts).h (maskOf A) = hts A`
  (`toExp_h_maskOf`).
* The correspondence: `toTS_lca` (the lowest common ancestor of `ptN p, ptN q` is the mask of `T.lca p q`),
  `toTS_sameLeaf`, `toExp_e` (`(toExp T hts).e (ptN p) (ptN q) = hts (T.lca p q)`), and for a germ
  `zExp_e_eq_order`, `wExp_e_eq_order`: `(toExp Tz htz).e (ptN p) (ptN q) = e(z_p − z_q)` for points with
  `z_p ≠ z_q` (and the same for `w`).
* Keys: `toTS_key`; `nodes_of_key_eq`: a tree with the key of `toTS T` (for example a tree read from a stored line)
  has as nodes exactly the masks of the nodes of `T` and the body of `T` on the leaf of `O`; `setOfMask_of_mem_toTS`:
  the nodes of `toTS T` are `maskOf A` for `A = setOfMask C ∈ T.nodes`, with height `hts A` (`toExp_h`).
* `good_toExp`, `comOk_toTS`: the tree conditions and the root rule (Lemma 4.3 (b)).
* The exponents of the base identities at the germ (`Identity.base`, `Term.expo`) and in the specification
  (`L6.F2S.baseExps` at the converted trees): `bodyZ_filter_eq`, `bodyW_filter_eq` (the terms of finite exponent of
  the equations of the bodies have, in order, the exponents of the specification, which omits the position term
  exactly when its exponent is `⊤`), `uExps_eq`, `iExps_eq` with `potU_expos`, `lagr_expos` (the constant term, first
  in the specification, is last in `Identity.potU`, `Identity.lagr`), `xkl_eq` (`x_kl`).
* `cond_of_germ`: **`Cond (Diag.ofF1 d) (toExp Tz htz) (toExp Tw htw)`** for a germ with positive masses, diagram
  `toDiagram d` and `ℓ ≤ 0`, and any trees with heights realizing its exponents.
* `exists_cond`: the same with the trees of Lemma 4.2, as complete trees with heights `Xz`, `Xw` whose exponents are
  those of the germ.
* `classes6_eq`, `diagOf_eq_ofF1`, `germ_cell_stored_of` (in `CellsConv.lean`): the representatives of the checks
  are those of `L6F1.classes6`, and the key of the cell of a germ is that of a stored line of its class.
-/

namespace CC6Compose

open CC6Full Finset

/-! ## Points as numbers -/

/-- The number of a point of `B` in the specification search: the body `k` is `k`, the centre of mass `O` is `6`. -/
def ptN : Pt 6 → ℕ
  | none => 6
  | some k => k.val

/-- The point with a given number (`O` for the numbers `≥ 6`). -/
def ptOfN (i : ℕ) : Pt 6 := if h : i < 6 then some ⟨i, h⟩ else none

@[simp] theorem ptN_none : ptN none = L6.F2S.O := rfl

@[simp] theorem ptN_some (k : Fin 6) : ptN (some k) = k.val := rfl

theorem ptN_lt (p : Pt 6) : ptN p < 7 := by
  rcases p with _ | k
  · show 6 < 7
    omega
  · show k.val < 7
    omega

theorem ptOfN_ptN (p : Pt 6) : ptOfN (ptN p) = p := by
  rcases p with _ | k
  · rfl
  · simp [ptOfN, ptN, k.isLt]

theorem ptN_ptOfN {i : ℕ} (hi : i < 7) : ptN (ptOfN i) = i := by
  unfold ptOfN
  split_ifs with h
  · rfl
  · show 6 = i
    omega

theorem ptN_injective : Function.Injective ptN := fun p q h => by
  rw [← ptOfN_ptN p, ← ptOfN_ptN q, h]

theorem ptN_eq_iff {p q : Pt 6} : ptN p = ptN q ↔ p = q := ptN_injective.eq_iff

/-! ## Sets of points as bit masks -/

/-- The bit mask of a set of points (bit `ptN p` for the point `p`). -/
def maskOf (A : Finset (Pt 6)) : ℕ :=
  ((List.range 7).filter fun i => decide (ptOfN i ∈ A)).foldr L6.F2S.ins 0

/-- The set of points of a bit mask. -/
def setOfMask (c : ℕ) : Finset (Pt 6) := univ.filter fun p => L6.F2S.mem (ptN p) c = true

theorem mem_zero (q : ℕ) : L6.F2S.mem q 0 = false := Nat.zero_testBit q

theorem mem_foldr_ins (q : ℕ) : ∀ L : List ℕ, L6.F2S.mem q (L.foldr L6.F2S.ins 0) = decide (q ∈ L)
  | [] => by simp [mem_zero]
  | a :: L => by
    rw [List.foldr_cons, L6.F2S.mem_ins, mem_foldr_ins q L]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro (h | rfl)
      · exact Or.inr h
      · exact Or.inl rfl
    · rintro (rfl | h)
      · exact Or.inr rfl
      · exact Or.inl h

theorem mem_maskOf {q : ℕ} {A : Finset (Pt 6)} :
    L6.F2S.mem q (maskOf A) = true ↔ q < 7 ∧ ptOfN q ∈ A := by
  rw [maskOf, mem_foldr_ins, decide_eq_true_iff, List.mem_filter, List.mem_range, decide_eq_true_iff]

theorem mem_maskOf_ptN {p : Pt 6} {A : Finset (Pt 6)} : L6.F2S.mem (ptN p) (maskOf A) = true ↔ p ∈ A := by
  rw [mem_maskOf, ptOfN_ptN]
  exact ⟨fun h => h.2, fun h => ⟨ptN_lt p, h⟩⟩

theorem mem_maskOf_eq (p : Pt 6) (A : Finset (Pt 6)) : L6.F2S.mem (ptN p) (maskOf A) = decide (p ∈ A) :=
  Bool.eq_iff_iff.mpr (mem_maskOf_ptN.trans decide_eq_true_iff.symm)

theorem maskOf_injective : Function.Injective maskOf := by
  intro A B h
  ext p
  rw [← mem_maskOf_ptN, ← mem_maskOf_ptN, h]

theorem subset_maskOf {A B : Finset (Pt 6)} : L6.F2S.subset (maskOf A) (maskOf B) = true ↔ A ⊆ B := by
  rw [L6.F2S.subset_iff]
  constructor
  · intro h p hp
    exact mem_maskOf_ptN.mp (h _ (mem_maskOf_ptN.mpr hp))
  · intro h q hq
    obtain ⟨hq7, hqA⟩ := mem_maskOf.mp hq
    exact mem_maskOf.mpr ⟨hq7, h hqA⟩

theorem ssubset_maskOf {A B : Finset (Pt 6)} : L6.F2S.ssubset (maskOf A) (maskOf B) = true ↔ A ⊂ B := by
  rw [L6.F2S.ssubset_iff, subset_maskOf, Finset.ssubset_iff_subset_ne, maskOf_injective.ne_iff]

theorem and_maskOf_eq_zero {A B : Finset (Pt 6)} : maskOf A &&& maskOf B = 0 ↔ Disjoint A B := by
  rw [L6.F2S.TreeAux.disjoint_iff, Finset.disjoint_left]
  constructor
  · intro h p hpA hpB
    exact h (ptN p) ⟨mem_maskOf_ptN.mpr hpA, mem_maskOf_ptN.mpr hpB⟩
  · rintro h q ⟨hqA, hqB⟩
    exact h (mem_maskOf.mp hqA).2 (mem_maskOf.mp hqB).2

theorem setOfMask_maskOf (A : Finset (Pt 6)) : setOfMask (maskOf A) = A := by
  ext p
  simp only [setOfMask, Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_maskOf_ptN

theorem mem_all {q : ℕ} : L6.F2S.mem q L6.F2S.all = true ↔ q < 7 := by
  constructor
  · intro h
    exact L6.F2S.lt7_of_mem (by decide) h
  · intro h
    interval_cases q <;> decide

theorem maskOf_univ : maskOf univ = L6.F2S.all := by
  apply L6.F2S.mask_ext
  intro q
  apply Bool.eq_iff_iff.mpr
  rw [mem_maskOf, mem_all]
  simp

/-! ## Trees -/

/-- A tree of Definition 4.1 as a tree of the specification search: the masks of its nodes (without repetition) and
the number of the body on the leaf of `O`. -/
def toTS (T : TreeShape 6) : L6.F2S.TS := ⟨T.nodes.dedup.map maskOf, T.leafO.map Fin.val⟩

/-- A tree with heights as a tree with heights of the specification search: the height of a mask is the height of
its set of points. -/
def toExp (T : TreeShape 6) (hts : Finset (Pt 6) → ℚ) : L6.F2S.ExpTree := ⟨toTS T, fun c => hts (setOfMask c)⟩

theorem toTS_nodes (T : TreeShape 6) : (toTS T).nodes = T.nodes.dedup.map maskOf := rfl

theorem toTS_leafO (T : TreeShape 6) : (toTS T).leafO = T.leafO.map Fin.val := rfl

theorem toExp_T (T : TreeShape 6) (hts : Finset (Pt 6) → ℚ) : (toExp T hts).T = toTS T := rfl

/-- The key of the converted tree: the masks of the nodes in increasing order, and the body on the leaf of `O`. -/
theorem toTS_key (T : TreeShape 6) :
    (toTS T).key = ((T.nodes.dedup.map maskOf).mergeSort (· ≤ ·), T.leafO.map Fin.val) := rfl

theorem mem_toTS_nodes {T : TreeShape 6} {C : ℕ} : C ∈ (toTS T).nodes ↔ ∃ A ∈ T.nodes, maskOf A = C := by
  rw [toTS_nodes, List.mem_map]
  simp only [List.mem_dedup]

theorem maskOf_mem_toTS {T : TreeShape 6} {A : Finset (Pt 6)} : maskOf A ∈ (toTS T).nodes ↔ A ∈ T.nodes := by
  rw [mem_toTS_nodes]
  constructor
  · rintro ⟨B, hB, h⟩
    rwa [← maskOf_injective h]
  · exact fun h => ⟨A, h, rfl⟩

theorem toExp_h_maskOf (T : TreeShape 6) (hts : Finset (Pt 6) → ℚ) (A : Finset (Pt 6)) :
    (toExp T hts).h (maskOf A) = hts A := by
  show hts (setOfMask (maskOf A)) = hts A
  rw [setOfMask_maskOf]

theorem toExp_h (T : TreeShape 6) (hts : Finset (Pt 6) → ℚ) (C : ℕ) : (toExp T hts).h C = hts (setOfMask C) := rfl

/-- The nodes of a converted tree are the masks of the nodes, and `setOfMask` inverts `maskOf` on them. -/
theorem setOfMask_of_mem_toTS {T : TreeShape 6} {C : ℕ} (hC : C ∈ (toTS T).nodes) :
    setOfMask C ∈ T.nodes ∧ maskOf (setOfMask C) = C := by
  obtain ⟨A, hA, rfl⟩ := mem_toTS_nodes.mp hC
  rw [setOfMask_maskOf]
  exact ⟨hA, rfl⟩

/-- Two trees of the specification search with the same key have the same nodes (as a set) and the same body on
the leaf of `O`. -/
theorem equiv_of_key_eq {t t' : L6.F2S.TS} (h : t.key = t'.key) : t.Equiv t' := by
  unfold L6.F2S.TS.key at h
  rw [Prod.mk.injEq] at h
  have hp : t.nodes.Perm t'.nodes :=
    (List.mergeSort_perm t.nodes _).symm.trans (by rw [h.1]; exact List.mergeSort_perm t'.nodes _)
  exact ⟨Finset.ext fun a => by simp only [List.mem_toFinset]; exact hp.mem_iff, h.2⟩

/-- **A tree with the key of the converted tree of `T`** (for example a tree read from a stored line) has as nodes
exactly the masks of the nodes of `T`, and the number of the body on the leaf of `O` of `T`. -/
theorem nodes_of_key_eq {t : L6.F2S.TS} {T : TreeShape 6} (h : t.key = (toTS T).key) :
    (∀ C, C ∈ t.nodes ↔ ∃ A ∈ T.nodes, maskOf A = C) ∧ t.leafO = T.leafO.map Fin.val := by
  have he := equiv_of_key_eq h
  refine ⟨fun C => ?_, he.2⟩
  rw [← mem_toTS_nodes, ← List.mem_toFinset, he.1, List.mem_toFinset]

theorem toTS_lrep (T : TreeShape 6) (p : Pt 6) : (toTS T).lrep (ptN p) = ptN (T.lrep p) := by
  rw [L6.F2S.TreeAux.lrep_eq, toTS_leafO]
  unfold TreeShape.lrep
  rcases h : T.leafO with _ | k
  · rcases p with _ | j <;> simp
  · by_cases hp : p = some k
    · subst hp
      simp
    · have hk : k.val ≠ ptN p := fun hk => hp (ptN_injective (by rw [← hk]; rfl))
      simp [hp, hk]

theorem lrep_lrep (T : TreeShape 6) (p : Pt 6) : T.lrep (T.lrep p) = T.lrep p := by
  unfold TreeShape.lrep
  by_cases hp : p = T.leafO
  · rw [ite_eq_left hp]
    split_ifs <;> rfl
  · rw [ite_eq_right hp, ite_eq_right hp]

theorem toTS_sameLeaf (T : TreeShape 6) (p q : Pt 6) :
    (toTS T).sameLeaf (ptN p) (ptN q) = decide (T.SameLeaf p q) := by
  unfold L6.F2S.TS.sameLeaf
  rw [toTS_lrep, toTS_lrep]
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, ptN_eq_iff, decide_eq_true_iff]
  rfl

/-- **The tree conditions** of the specification search for a converted tree. -/
theorem wf_toTS {T : TreeShape 6} (hT : T.WF) : L6.F2S.WF (toTS T) L6.F2S.all where
  S_lt := by decide
  O_mem := by decide
  nodup := (List.nodup_dedup _).map maskOf_injective
  sub C hC := by
    obtain ⟨A, -, rfl⟩ := mem_toTS_nodes.mp hC
    rw [← maskOf_univ, subset_maskOf]
    exact subset_univ A
  two C hC := by
    obtain ⟨A, hA, rfl⟩ := mem_toTS_nodes.mp hC
    obtain ⟨p, hp, q, hq, hpq⟩ := hT.two A hA
    rw [L6.F2S.TreeAux.twoLeaves_iff]
    refine ⟨ptN p, ptN q, ptN_lt p, ptN_lt q, mem_maskOf_ptN.mpr hp, mem_maskOf_ptN.mpr hq, ?_⟩
    rw [toTS_lrep, toTS_lrep, Ne, ptN_eq_iff]
    exact hpq
  lam C hC D hD := by
    obtain ⟨A, hA, rfl⟩ := mem_toTS_nodes.mp hC
    obtain ⟨B, hB, rfl⟩ := mem_toTS_nodes.mp hD
    rcases hT.laminar A hA B hB with h | h | h
    · exact Or.inl (subset_maskOf.mpr h)
    · exact Or.inr (Or.inl (subset_maskOf.mpr h))
    · exact Or.inr (Or.inr (and_maskOf_eq_zero.mpr h))
  root _ := by
    rw [← maskOf_univ]
    exact maskOf_mem_toTS.mpr hT.root
  leafO k hk := by
    rw [toTS_leafO, Option.map_eq_some_iff] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    refine ⟨j.isLt, mem_all.mpr (by omega), fun C hC => ?_⟩
    obtain ⟨A, hA, rfl⟩ := mem_toTS_nodes.mp hC
    have hs : T.SameLeaf none (some j) := T.sameLeaf_iff.mpr (Or.inr ⟨j, hj, Or.inr ⟨rfl, rfl⟩⟩)
    rw [← ptN_none, ← ptN_some, mem_maskOf_eq, mem_maskOf_eq]
    exact decide_eq_decide.mpr ⟨fun h => hT.closed A hA _ _ hs h, fun h => hT.closed A hA _ _ hs.symm h⟩

/-- The converted tree with heights is good: a tree, with heights increasing from the root to the leaves. -/
theorem good_toExp {T : TreeShape 6} {h : Pt 6 → Pt 6 → WithTop ℚ} {hts : Finset (Pt 6) → ℚ}
    (hR : T.Realizes h hts) : (toExp T hts).Good := by
  refine ⟨wf_toTS hR.wf, fun C hC D hD hCD => ?_⟩
  obtain ⟨A, hA, rfl⟩ := mem_toTS_nodes.mp hC
  obtain ⟨B, hB, rfl⟩ := mem_toTS_nodes.mp hD
  rw [toExp_h_maskOf, toExp_h_maskOf]
  exact hR.mono A hA B hB (ssubset_maskOf.mp hCD)

/-- The lowest common ancestor of two points in the converted tree is the mask of their lowest common ancestor. -/
theorem toTS_lca {T : TreeShape 6} (hT : T.WF) (p q : Pt 6) :
    (toTS T).lca (ptN p) (ptN q) = some (maskOf (T.lca p q)) := by
  rw [L6.F2S.TreeAux.lca_eq_pickMin]
  refine L6.F2S.TreeAux.pickMin_eq_some ((wf_toTS hT).chain_lca _ _)
    (maskOf_mem_toTS.mpr (T.lca_mem hT p q)) ?_ ?_
  · rw [Bool.and_eq_true, mem_maskOf_ptN, mem_maskOf_ptN]
    exact ⟨T.mem_lca_left p q, T.mem_lca_right p q⟩
  · intro C hC hmem
    obtain ⟨A, hA, rfl⟩ := mem_toTS_nodes.mp hC
    rw [Bool.and_eq_true, mem_maskOf_ptN, mem_maskOf_ptN] at hmem
    exact subset_maskOf.mpr (T.lca_subset hA hmem.1 hmem.2)

/-- **The exponents of the converted tree**: `e(p, q)` is the height of the lowest common ancestor. -/
theorem toExp_e {T : TreeShape 6} (hT : T.WF) (hts : Finset (Pt 6) → ℚ) (p q : Pt 6) :
    (toExp T hts).e (ptN p) (ptN q) = hts (T.lca p q) := by
  show (match (toTS T).lca (ptN p) (ptN q) with
    | some C => (toExp T hts).h C
    | none => 0) = _
  rw [toTS_lca hT]
  exact toExp_h_maskOf T hts _

theorem toExp_e_eq {T : TreeShape 6} {h : Pt 6 → Pt 6 → WithTop ℚ} {hts : Finset (Pt 6) → ℚ}
    (hR : T.Realizes h hts) {p q : Pt 6} (hpq : ¬ T.SameLeaf p q) :
    (((toExp T hts).e (ptN p) (ptN q) : ℚ) : WithTop ℚ) = h p q := by
  rw [toExp_e hR.wf, hR.diff p q hpq]

/-- Two bodies: the exponent of the converted tree is the value of `h`. -/
theorem toExp_e_body {T : TreeShape 6} {h : Pt 6 → Pt 6 → WithTop ℚ} {hts : Finset (Pt 6) → ℚ}
    (hR : T.Realizes h hts) {k l : ℕ} (hk : k < 6) (hl : l < 6) (hkl : k ≠ l) :
    (((toExp T hts).e k l : ℚ) : WithTop ℚ) = h (some ⟨k, hk⟩) (some ⟨l, hl⟩) :=
  toExp_e_eq hR (p := some ⟨k, hk⟩) (q := some ⟨l, hl⟩)
    (T.not_sameLeaf_some fun e => hkl (congrArg Fin.val e))

/-! ### The exponents of a germ -/

variable {m : Fin 6 → ℝ}

theorem zExp_e_body {G : Germ 6 m} {Tz : TreeShape 6} {htz : Finset (Pt 6) → ℚ} (hR : Tz.Realizes G.hz htz)
    {k l : ℕ} (hk : k < 6) (hl : l < 6) (hkl : k ≠ l) : (toExp Tz htz).e k l = G.zeta ⟨k, hk⟩ ⟨l, hl⟩ := by
  have h := toExp_e_body hR hk hl hkl
  rw [G.hz_some_some fun e => hkl (congrArg Fin.val e)] at h
  exact_mod_cast h

theorem wExp_e_body {G : Germ 6 m} {Tw : TreeShape 6} {htw : Finset (Pt 6) → ℚ} (hR : Tw.Realizes G.hw htw)
    {k l : ℕ} (hk : k < 6) (hl : l < 6) (hkl : k ≠ l) : (toExp Tw htw).e k l = G.omega ⟨k, hk⟩ ⟨l, hl⟩ := by
  have h := toExp_e_body hR hk hl hkl
  rw [G.hw_some_some fun e => hkl (congrArg Fin.val e)] at h
  exact_mod_cast h

/-- **The exponents of the cell are those of the germ** (colour `z`): for points with `z_p ≠ z_q`,
`(toExp Tz htz).e (ptN p) (ptN q) = e(z_p − z_q)`. -/
theorem zExp_e_eq_order {G : Germ 6 m} {Tz : TreeShape 6} {htz : Finset (Pt 6) → ℚ} (hR : Tz.Realizes G.hz htz)
    {p q : Pt 6} (hpq : G.zpos p ≠ G.zpos q) : (toExp Tz htz).e (ptN p) (ptN q) = (G.zpos p - G.zpos q).order := by
  have hs : ¬ Tz.SameLeaf p q := fun hs => hpq (G.hz_eq_top_iff.mp (hR.same p q hs))
  have h := toExp_e_eq hR hs
  rw [G.hz_def, ← HahnSeries.order_eq_orderTop_of_ne_zero (sub_ne_zero.mpr hpq)] at h
  exact_mod_cast h

/-- **The exponents of the cell are those of the germ** (colour `w`). -/
theorem wExp_e_eq_order {G : Germ 6 m} {Tw : TreeShape 6} {htw : Finset (Pt 6) → ℚ} (hR : Tw.Realizes G.hw htw)
    {p q : Pt 6} (hpq : G.wpos p ≠ G.wpos q) : (toExp Tw htw).e (ptN p) (ptN q) = (G.wpos p - G.wpos q).order := by
  have hs : ¬ Tw.SameLeaf p q := fun hs => hpq (G.hw_eq_top_iff.mp (hR.same p q hs))
  have h := toExp_e_eq hR hs
  rw [G.hw_def, ← HahnSeries.order_eq_orderTop_of_ne_zero (sub_ne_zero.mpr hpq)] at h
  exact_mod_cast h

/-! ## The height of the root -/

/-- The root of a tree realizing `hOf pos` has height `≥ −2` when all positions have exponents `≥ −2`. -/
theorem root_height_ge {T : TreeShape 6} {pos : Pt 6 → Ser} {hts : Finset (Pt 6) → ℚ}
    (hR : T.Realizes (hOf pos) hts) (hlow : ∀ p, ((-2 : ℚ) : WithTop ℚ) ≤ (pos p).orderTop) :
    -2 ≤ hts univ := by
  have hT := hR.wf
  obtain ⟨q, hq⟩ : ∃ q, q ∉ T.child univ none := by
    by_contra hc
    push Not at hc
    exact T.child_ne_self hT hT.root none (eq_univ_of_forall hc)
  obtain ⟨hs, hl⟩ := T.lca_eq_of_not_mem_child hT.root (mem_univ _) (mem_univ _) hq
  have h1 := hR.diff none q hs
  rw [hl] at h1
  have h2 : ((-2 : ℚ) : WithTop ℚ) ≤ hOf pos none q :=
    le_trans (le_min (hlow none) (hlow q)) HahnSeries.min_orderTop_le_orderTop_sub
  rw [h1] at h2
  exact_mod_cast h2

theorem zpos_low (G : Germ 6 m) (p : Pt 6) : ((-2 : ℚ) : WithTop ℚ) ≤ (G.zpos p).orderTop := by
  rcases p with _ | k
  · simp
  · exact G.low_z.1 k

theorem wpos_low (G : Germ 6 m) (p : Pt 6) : ((-2 : ℚ) : WithTop ℚ) ≤ (G.wpos p).orderTop := by
  rcases p with _ | k
  · simp
  · exact G.low_w.1 k

theorem toExp_h_all (T : TreeShape 6) (hts : Finset (Pt 6) → ℚ) : (toExp T hts).h L6.F2S.all = hts univ := by
  rw [← maskOf_univ, toExp_h_maskOf]

/-! ## The root rule -/

theorem numChildren_eq (T : L6.F2S.TS) (S C : ℕ) : L6.F2S.numChildren T S C =
    ((T.nodes.filter fun D => L6.F2S.ssubset D C).filter fun D =>
        !((T.nodes.filter fun D => L6.F2S.ssubset D C).any fun E => L6.F2S.ssubset D E)).length +
      ((T.classes S).filter fun L => L6.F2S.subset L C &&
        !((T.nodes.filter fun D => L6.F2S.ssubset D C).any fun D => L6.F2S.subset L D)).length := rfl

/-- **The root rule** (Lemma 4.3 (b)) for a converted tree whose root has at least three children. -/
theorem comOk_toTS {T : TreeShape 6} (hT : T.WF) (h3 : 3 ≤ (T.children univ).card) :
    L6.F2S.comOk (toTS T) L6.F2S.all = true := by
  unfold L6.F2S.comOk
  rw [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_iff, numChildren_eq]
  refine ⟨by rw [← maskOf_univ]; exact maskOf_mem_toTS.mpr hT.root, ?_⟩
  set subs := (toTS T).nodes.filter fun D => L6.F2S.ssubset D L6.F2S.all with hsubs
  set maxl := subs.filter fun D => !(subs.any fun E => L6.F2S.ssubset D E) with hmaxl
  set lc := ((toTS T).classes L6.F2S.all).filter fun L => L6.F2S.subset L L6.F2S.all &&
    !(subs.any fun D => L6.F2S.subset L D) with hlc
  have hsub : ∀ {E : ℕ}, E ∈ subs → ∃ B ∈ T.nodes, B ⊂ univ ∧ maskOf B = E := by
    intro E hE
    rw [hsubs, List.mem_filter] at hE
    obtain ⟨B, hB, rfl⟩ := mem_toTS_nodes.mp hE.1
    rw [← maskOf_univ, ssubset_maskOf] at hE
    exact ⟨B, hB, hE.2, rfl⟩
  have key : ∀ c ∈ T.children univ, maskOf c ∈ maxl ++ lc := by
    intro c hc
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hc
    by_cases hP : ∃ A ∈ T.nodes, p ∈ A ∧ A ⊂ univ
    · -- the child of the root containing `p` is the largest proper node containing `p`
      set P := T.nodes.toFinset.filter fun A => p ∈ A ∧ A ⊂ univ with hPdef
      have hPne : P.Nonempty := by
        obtain ⟨A, hA, hpA, hAu⟩ := hP
        exact ⟨A, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hA, hpA, hAu⟩⟩
      obtain ⟨A0, hA0P, hA0max⟩ := P.exists_max_image Finset.card hPne
      obtain ⟨hA0, hpA0, hA0u⟩ : A0 ∈ T.nodes ∧ p ∈ A0 ∧ A0 ⊂ univ := by
        have h := Finset.mem_filter.mp hA0P
        exact ⟨List.mem_toFinset.mp h.1, h.2.1, h.2.2⟩
      have hbelow : ∀ B ∈ T.nodes, p ∈ B → B ⊂ univ → B ⊆ A0 := by
        intro B hB hpB hBu
        rcases hT.laminar B hB A0 hA0 with h | h | h
        · exact h
        · have hcard := hA0max B (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hB, hpB, hBu⟩)
          obtain rfl := Finset.eq_of_subset_of_card_le h hcard
          exact Finset.Subset.refl _
        · exact absurd hpA0 (Finset.disjoint_left.mp h hpB)
      have hchild : T.child univ p = A0 := by
        ext r
        rw [T.mem_child]
        constructor
        · rintro ⟨-, hs | hl⟩
          · exact hT.closed A0 hA0 p r hs hpA0
          · exact hbelow _ (T.lca_mem hT p r) (T.mem_lca_left p r) hl (T.mem_lca_right p r)
        · intro hr
          exact ⟨mem_univ r, Or.inr (Finset.ssubset_of_subset_of_ssubset (T.lca_subset hA0 hpA0 hr) hA0u)⟩
      rw [hchild]
      apply List.mem_append_left
      rw [hmaxl, List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [hsubs, List.mem_filter, ← maskOf_univ, ssubset_maskOf]
        exact ⟨maskOf_mem_toTS.mpr hA0, hA0u⟩
      · rw [Bool.not_eq_true', List.any_eq_false]
        intro E hE hAE
        obtain ⟨B, hB, hBu, rfl⟩ := hsub hE
        rw [ssubset_maskOf] at hAE
        exact ssubset_irrefl _ (Finset.ssubset_of_ssubset_of_subset hAE (hbelow B hB (hAE.subset hpA0) hBu))
    · -- the child of the root containing `p` is the leaf of `p`
      push Not at hP
      have hchild : T.child univ p = univ.filter (T.SameLeaf p ·) := by
        ext r
        rw [T.mem_child, Finset.mem_filter]
        constructor
        · rintro ⟨-, hs | hl⟩
          · exact ⟨mem_univ r, hs⟩
          · exact absurd hl (hP _ (T.lca_mem hT p r) (T.mem_lca_left p r))
        · rintro ⟨-, hs⟩
          exact ⟨mem_univ r, Or.inl hs⟩
      rw [hchild]
      apply List.mem_append_right
      set x := ptN (T.lrep p) with hx
      have hx7 : x < 7 := ptN_lt _
      have hxx : (toTS T).lrep x = x := by rw [hx, toTS_lrep, lrep_lrep]
      have hlo : ∀ k, (toTS T).leafO = some k → k ≠ L6.F2S.O := by
        intro k hk
        rw [toTS_leafO, Option.map_eq_some_iff] at hk
        obtain ⟨j, -, rfl⟩ := hk
        have := j.isLt
        unfold L6.F2S.O
        omega
      have hcls : (toTS T).leafClass x = maskOf (univ.filter (T.SameLeaf p ·)) := by
        apply L6.F2S.mask_ext
        intro y
        apply Bool.eq_iff_iff.mpr
        rw [L6.F2S.TreeAux.mem_leafClass hlo hxx, mem_maskOf]
        constructor
        · intro hy
          have hy7 : y < 7 := by
            by_contra hy7
            rw [L6.F2S.TreeAux.lrep_eq] at hy
            split_ifs at hy with hyl
            · rw [toTS_leafO, Option.map_eq_some_iff] at hyl
              obtain ⟨j, -, hj⟩ := hyl
              have := j.isLt
              omega
            · omega
          refine ⟨hy7, Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
          rw [← ptN_ptOfN hy7, toTS_lrep, hx, ptN_eq_iff] at hy
          exact hy.symm
        · rintro ⟨hy7, hy⟩
          rw [Finset.mem_filter] at hy
          rw [← ptN_ptOfN hy7, toTS_lrep, hx, ptN_eq_iff]
          exact hy.2.symm
      rw [hlc, List.mem_filter]
      refine ⟨?_, ?_⟩
      · unfold L6.F2S.TS.classes
        rw [← hcls]
        refine List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨(L6.F2S.mem_toList _ _).mpr ⟨hx7, mem_all.mpr hx7⟩, ?_⟩,
          rfl⟩
        rw [hxx, beq_self_eq_true]
      · rw [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, ← maskOf_univ, subset_maskOf]
        refine ⟨subset_univ _, fun E hE hcE => ?_⟩
        obtain ⟨B, hB, hBu, rfl⟩ := hsub hE
        rw [subset_maskOf] at hcE
        have hpB : p ∈ B := hcE (Finset.mem_filter.mpr ⟨mem_univ _, T.sameLeaf_refl p⟩)
        exact hP B hB hpB hBu
  calc 3 ≤ (T.children univ).card := h3
    _ = ((T.children univ).image maskOf).card := (Finset.card_image_of_injective _ maskOf_injective).symm
    _ ≤ (maxl ++ lc).toFinset.card := Finset.card_le_card fun y hy => by
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
        exact List.mem_toFinset.mpr (key c hc)
    _ ≤ (maxl ++ lc).length := List.toFinset_card_le _
    _ = maxl.length + lc.length := List.length_append

/-! ## The diagram -/

theorem ofF1_zstroke (d : L6F1.Diagram) {k l : ℕ} (hkl : k < l) (hl : l < 6) :
    (L6.F2.Diag.ofF1 d).zstroke k l = L6F1.zStroke d.e k l := by
  have h1 : min k l = k := min_eq_left hkl.le
  have h2 : max k l = l := max_eq_right hkl.le
  have e1 : (6 * k + l) / 6 = k := by omega
  have e2 : (6 * k + l) % 6 = l := by omega
  simp only [L6.F2.Diag.zstroke, L6.F2.Diag.ofF1, h1, h2]
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
  simp only [e1, e2, hkl, decide_true, Bool.true_and]

theorem ofF1_wstroke (d : L6F1.Diagram) {k l : ℕ} (hkl : k < l) (hl : l < 6) :
    (L6.F2.Diag.ofF1 d).wstroke k l = L6F1.wStroke d.e k l := by
  have h1 : min k l = k := min_eq_left hkl.le
  have h2 : max k l = l := max_eq_right hkl.le
  have e1 : (6 * k + l) / 6 = k := by omega
  have e2 : (6 * k + l) % 6 = l := by omega
  simp only [L6.F2.Diag.wstroke, L6.F2.Diag.ofF1, h1, h2]
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
  simp only [e1, e2, hkl, decide_true, Bool.true_and]

theorem ofF1_zc (d : L6F1.Diagram) {k : ℕ} (hk : k < 6) : (L6.F2.Diag.ofF1 d).zc[k]! = L6F1.circled d.zc k := by
  simp only [L6.F2.Diag.ofF1]
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]

theorem ofF1_wc (d : L6F1.Diagram) {k : ℕ} (hk : k < 6) : (L6.F2.Diag.ofF1 d).wc[k]! = L6F1.circled d.wc k := by
  simp only [L6.F2.Diag.ofF1]
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]

/-! ## The least exponent attained twice -/

/-- Two positions of a list with a given value. -/
theorem exists_two_of_count {α : Type*} [BEq α] [LawfulBEq α] :
    ∀ (l : List α) (a : α), 2 ≤ l.count a →
      ∃ i j : ℕ, ∃ (hi : i < l.length) (hj : j < l.length), i ≠ j ∧ l[i] = a ∧ l[j] = a
  | [], a, h => by simp at h
  | b :: l, a, h => by
    rw [List.count_cons] at h
    by_cases hb : b = a
    · rw [hb, beq_self_eq_true, ite_eq_left rfl] at h
      have h1 : 0 < l.count a := by omega
      obtain ⟨j, hj, hja⟩ := List.mem_iff_getElem.mp (List.count_pos_iff.mp h1)
      exact ⟨0, j + 1, by simp, by simpa using hj, by omega, hb, hja⟩
    · rw [beq_false_of_ne hb, ite_eq_right (by simp)] at h
      obtain ⟨i, j, hi, hj, hij, e1, e2⟩ := exists_two_of_count l a (by omega)
      exact ⟨i + 1, j + 1, by simpa using hi, by simpa using hj, by omega, e1, e2⟩

/-- Two positions with a given value give a count at least two. -/
theorem two_le_count_of {α : Type*} [BEq α] [LawfulBEq α] :
    ∀ (l : List α) (a : α) (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i ≠ j → l[i] = a → l[j] = a →
      2 ≤ l.count a
  | [], _, _, _, hi, _, _, _, _ => by simp at hi
  | b :: l, a, i, j, hi, hj, hij, e1, e2 => by
    rw [List.count_cons]
    rcases i with _ | i <;> rcases j with _ | j
    · exact absurd rfl hij
    · have hb : b = a := e1
      have hj' : j < l.length := Nat.lt_of_succ_lt_succ hj
      have e2' : l[j] = a := e2
      have hpos : 0 < l.count a := List.count_pos_iff.mpr (by rw [← e2']; exact List.getElem_mem hj')
      rw [hb, beq_self_eq_true, ite_eq_left rfl]
      omega
    · have hb : b = a := e2
      have hi' : i < l.length := Nat.lt_of_succ_lt_succ hi
      have e1' : l[i] = a := e1
      have hpos : 0 < l.count a := List.count_pos_iff.mpr (by rw [← e1']; exact List.getElem_mem hi')
      rw [hb, beq_self_eq_true, ite_eq_left rfl]
      omega
    · have h := two_le_count_of l a i j (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj)
        (fun h => hij (congrArg Nat.succ h)) e1 e2
      omega

/-- The condition `MinTwice` of the specification from a least value of count at least two. -/
theorem minTwice_of {L : List ℚ} {μ : ℚ} (hle : ∀ x ∈ L, μ ≤ x)
    (hc : 2 ≤ (L.map fun x : ℚ => (x : WithTop ℚ)).count (μ : WithTop ℚ)) : L6.F2S.MinTwice L := by
  obtain ⟨i, j, hi, hj, hij, e1, e2⟩ := exists_two_of_count _ _ hc
  have hi' : i < L.length := by simpa using hi
  have hj' : j < L.length := by simpa using hj
  have f1 : L[i] = μ := by simpa using e1
  have f2 : L[j] = μ := by simpa using e2
  refine ⟨i, j, hi', hj', hij, ?_, ?_⟩
  · rw [getElem!_pos L i hi', getElem!_pos L j hj', f1, f2]
  · intro k hk
    rw [getElem!_pos L i hi', getElem!_pos L k hk, f1]
    exact hle _ (List.getElem_mem hk)

/-- Lemma 4.3 (c) at a germ as a least value with count at least two. -/
theorem count_of_minTwice {I : Identity 6} {G : Germ 6 m} (h : I.MinTwice G) :
    ∃ μ : ℚ, (∀ t ∈ I, (μ : WithTop ℚ) ≤ t.expo G) ∧ 2 ≤ (I.map (Term.expo G)).count (μ : WithTop ℚ) := by
  obtain ⟨i, j, hij, hfin, heq, hle⟩ := h
  obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp hfin
  refine ⟨e, fun t ht => ?_, ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ht
    rw [he]
    exact hle ⟨k, hk⟩
  · refine two_le_count_of _ _ i.1 j.1 (by simp) (by simp) (fun h => hij (Fin.ext h)) ?_ ?_
    · simp [he]
    · simp [he, heq]

/-- **The transfer of Lemma 4.3 (c)**: if the terms of finite exponent of an identity have, up to order, the
exponents of a list `L`, then the least value of `L` is attained twice. -/
theorem minTwice_transfer {I : Identity 6} {G : Germ 6 m} {L : List ℚ} (h : I.MinTwice G)
    (hL : ((I.map (Term.expo G)).filter fun e => e ≠ ⊤).Perm (L.map fun x : ℚ => (x : WithTop ℚ))) :
    L6.F2S.MinTwice L := by
  obtain ⟨μ, hle, hc⟩ := count_of_minTwice h
  refine minTwice_of (μ := μ) (fun x hx => ?_) ?_
  · have hx' : (x : WithTop ℚ) ∈ (I.map (Term.expo G)).filter fun e => e ≠ ⊤ :=
      hL.symm.subset (List.mem_map_of_mem hx)
    obtain ⟨t, ht, hte⟩ := List.mem_map.mp (List.mem_of_mem_filter hx')
    have h1 := hle t ht
    rw [hte] at h1
    exact_mod_cast h1
  · rw [← hL.count_eq, List.count_filter (by simp)]
    exact hc

/-! ## The exponents of the base identities -/

theorem mem_pairs {kl : Fin 6 × Fin 6} (h : kl ∈ Identity.pairs 6) : kl.1 < kl.2 := by
  simp only [Identity.pairs, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
  obtain ⟨k, -, l, ⟨-, hkl⟩, rfl⟩ := h
  exact hkl

theorem pairs6_toList : L6.F2.pairs6.toList = (Identity.pairs 6).map fun kl => ((kl.1 : ℕ), (kl.2 : ℕ)) := by
  decide

theorem range_filter_ne (k : Fin 6) :
    (List.range 6).filter (· != k.val) = ((List.finRange 6).filter fun l => l ≠ k).map Fin.val := by
  revert k
  decide

theorem filter_ne_top_map {α : Type*} (L : List α) (f : α → ℚ) :
    ((L.map fun a => ((f a : ℚ) : WithTop ℚ)).filter fun e => e ≠ ⊤) = L.map fun a => ((f a : ℚ) : WithTop ℚ) :=
  List.filter_eq_self.mpr fun e he => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
    simp

theorem bodyExps_true (Xz Xw : L6.F2S.ExpTree) (i : ℕ) : L6.F2S.bodyExps Xz Xw true i =
    (if Xz.T.sameLeaf i L6.F2S.O then [] else [Xz.e i L6.F2S.O]) ++
      ((List.range 6).filter (· != i)).map fun j => -(Xz.e i j + 3 * Xw.e i j) / 2 := rfl

theorem bodyExps_false (Xz Xw : L6.F2S.ExpTree) (i : ℕ) : L6.F2S.bodyExps Xz Xw false i =
    (if Xw.T.sameLeaf i L6.F2S.O then [] else [Xw.e i L6.F2S.O]) ++
      ((List.range 6).filter (· != i)).map fun j => -(3 * Xz.e i j + Xw.e i j) / 2 := rfl

theorem toExp_sameLeaf_O (T : TreeShape 6) (hts : Finset (Pt 6) → ℚ) (k : Fin 6) :
    (toExp T hts).T.sameLeaf k L6.F2S.O = decide (T.SameLeaf (some k) none) :=
  toTS_sameLeaf T (some k) none

theorem toExp_e_O {T : TreeShape 6} {h : Pt 6 → Pt 6 → WithTop ℚ} {hts : Finset (Pt 6) → ℚ}
    (hR : T.Realizes h hts) {k : Fin 6} (hs : ¬ T.SameLeaf (some k) none) :
    (((toExp T hts).e k L6.F2S.O : ℚ) : WithTop ℚ) = h (some k) none :=
  toExp_e_eq hR hs

theorem expo_pos_z (G : Germ 6 m) (k : Fin 6) :
    Term.expo G ⟨1, [(some k, none)], [], []⟩ = G.hz (some k) none := by
  simp [Term.expo]

theorem expo_pos_w (G : Germ 6 m) (k : Fin 6) :
    Term.expo G ⟨1, [], [(some k, none)], []⟩ = G.hw (some k) none := by
  simp [Term.expo]

theorem expo_cross_z (G : Germ 6 m) {k l : Fin 6} (hkl : k ≠ l) :
    Term.expo G ⟨-Identity.cm l, [(some k, some l)], [], [(k, l), (k, l), (k, l)]⟩ =
      ((-(G.zeta k l + 3 * G.omega k l) / 2 : ℚ) : WithTop ℚ) := by
  have e : G.zeta k l + (-G.x k l + (-G.x k l + -G.x k l)) = -(G.zeta k l + 3 * G.omega k l) / 2 := by
    rw [G.x_eq hkl]
    ring
  simp only [Term.expo, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [G.hz_some_some hkl, G.orderTop_p hkl, ← e]
  norm_cast

theorem expo_cross_w (G : Germ 6 m) {k l : Fin 6} (hkl : k ≠ l) :
    Term.expo G ⟨-Identity.cm l, [], [(some k, some l)], [(k, l), (k, l), (k, l)]⟩ =
      ((-(3 * G.zeta k l + G.omega k l) / 2 : ℚ) : WithTop ℚ) := by
  have e : G.omega k l + (-G.x k l + (-G.x k l + -G.x k l)) = -(3 * G.zeta k l + G.omega k l) / 2 := by
    rw [G.x_eq hkl]
    ring
  simp only [Term.expo, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, zero_add]
  rw [G.hw_some_some hkl, G.orderTop_p hkl, ← e]
  norm_cast

theorem bodyZ_expos (G : Germ 6 m) (k : Fin 6) :
    (Identity.bodyZ k).map (Term.expo G) = G.hz (some k) none ::
      (((List.finRange 6).filter fun l => l ≠ k).map fun l =>
        ((-(G.zeta k l + 3 * G.omega k l) / 2 : ℚ) : WithTop ℚ)) := by
  rw [Identity.bodyZ, List.map_cons, List.map_map, expo_pos_z]
  congr 1
  refine List.map_congr_left fun l hl => ?_
  have hlk : l ≠ k := by simpa using (List.mem_filter.mp hl).2
  exact expo_cross_z G hlk.symm

theorem bodyW_expos (G : Germ 6 m) (k : Fin 6) :
    (Identity.bodyW k).map (Term.expo G) = G.hw (some k) none ::
      (((List.finRange 6).filter fun l => l ≠ k).map fun l =>
        ((-(3 * G.zeta k l + G.omega k l) / 2 : ℚ) : WithTop ℚ)) := by
  rw [Identity.bodyW, List.map_cons, List.map_map, expo_pos_w]
  congr 1
  refine List.map_congr_left fun l hl => ?_
  have hlk : l ≠ k := by simpa using (List.mem_filter.mp hl).2
  exact expo_cross_w G hlk.symm

theorem potU_expos (G : Germ 6 m) :
    (Identity.potU 6).map (Term.expo G) =
      ((Identity.pairs 6).map fun kl => ((-G.x kl.1 kl.2 : ℚ) : WithTop ℚ)) ++ [0] := by
  rw [Identity.potU, List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left fun kl hkl => ?_
    have hne : kl.1 ≠ kl.2 := (mem_pairs hkl).ne
    simp [Term.expo, G.orderTop_p hne]
  · simp [Term.expo]

theorem lagr_expos (G : Germ 6 m) :
    (Identity.lagr 6).map (Term.expo G) =
      ((Identity.pairs 6).map fun kl => ((2 * G.x kl.1 kl.2 : ℚ) : WithTop ℚ)) ++ [0] := by
  rw [Identity.lagr, List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left fun kl hkl => ?_
    have hne : kl.1 ≠ kl.2 := (mem_pairs hkl).ne
    have e : G.zeta kl.1 kl.2 + G.omega kl.1 kl.2 = 2 * G.x kl.1 kl.2 := by
      rw [G.x_eq hne]
      ring
    simp only [Function.comp_apply, Term.expo, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [G.hz_some_some hne, G.hw_some_some hne, ← e]
    norm_cast
  · simp [Term.expo]

/-! ### The exponents of the specification at the converted trees -/

section spec

variable {G : Germ 6 m} {Tz Tw : TreeShape 6} {htz htw : Finset (Pt 6) → ℚ}

theorem xkl_eq (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) {k l : Fin 6} (hkl : k ≠ l) :
    L6.F2S.xkl (toExp Tz htz) (toExp Tw htw) k l = G.x k l := by
  have hkl' : k.val ≠ l.val := fun e => hkl (Fin.ext e)
  unfold L6.F2S.xkl
  rw [zExp_e_body hRz k.isLt l.isLt hkl', wExp_e_body hRw k.isLt l.isLt hkl', G.x_eq hkl]

/-- **The terms of the equation of body `k` in `z`**, at the germ: those of finite exponent have, in order, the
exponents of the specification at the converted trees (the position term is omitted in the specification exactly
when `z_k = 0`, i.e. its exponent is `⊤`). -/
theorem bodyZ_filter_eq (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) (k : Fin 6) :
    ((Identity.bodyZ k).map (Term.expo G)).filter (fun e => e ≠ ⊤) =
      (L6.F2S.bodyExps (toExp Tz htz) (toExp Tw htw) true k).map fun x : ℚ => (x : WithTop ℚ) := by
  have htail : ((((List.range 6).filter (· != k.val)).map fun j =>
      -((toExp Tz htz).e k j + 3 * (toExp Tw htw).e k j) / 2).map fun x : ℚ => (x : WithTop ℚ)) =
      (((List.finRange 6).filter fun l => l ≠ k).map fun l =>
        ((-(G.zeta k l + 3 * G.omega k l) / 2 : ℚ) : WithTop ℚ)) := by
    rw [range_filter_ne, List.map_map, List.map_map]
    refine List.map_congr_left fun l hl => ?_
    have hlk : k.val ≠ l.val := fun e => (by simpa using (List.mem_filter.mp hl).2 : l ≠ k) (Fin.ext e).symm
    simp only [Function.comp_apply]
    rw [zExp_e_body hRz k.isLt l.isLt hlk, wExp_e_body hRw k.isLt l.isLt hlk]
  rw [bodyExps_true, List.map_append, htail, bodyZ_expos, List.filter_cons, filter_ne_top_map]
  by_cases hs : Tz.SameLeaf (some k) none
  · rw [toExp_sameLeaf_O, decide_eq_true hs, ite_eq_left rfl, hRz.same _ _ hs]
    simp
  · rw [toExp_sameLeaf_O, decide_eq_false hs, ← toExp_e_O hRz hs]
    simp

/-- **The terms of the equation of body `k` in `w`**, as `bodyZ_filter_eq`. -/
theorem bodyW_filter_eq (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) (k : Fin 6) :
    ((Identity.bodyW k).map (Term.expo G)).filter (fun e => e ≠ ⊤) =
      (L6.F2S.bodyExps (toExp Tz htz) (toExp Tw htw) false k).map fun x : ℚ => (x : WithTop ℚ) := by
  have htail : ((((List.range 6).filter (· != k.val)).map fun j =>
      -(3 * (toExp Tz htz).e k j + (toExp Tw htw).e k j) / 2).map fun x : ℚ => (x : WithTop ℚ)) =
      (((List.finRange 6).filter fun l => l ≠ k).map fun l =>
        ((-(3 * G.zeta k l + G.omega k l) / 2 : ℚ) : WithTop ℚ)) := by
    rw [range_filter_ne, List.map_map, List.map_map]
    refine List.map_congr_left fun l hl => ?_
    have hlk : k.val ≠ l.val := fun e => (by simpa using (List.mem_filter.mp hl).2 : l ≠ k) (Fin.ext e).symm
    simp only [Function.comp_apply]
    rw [zExp_e_body hRz k.isLt l.isLt hlk, wExp_e_body hRw k.isLt l.isLt hlk]
  rw [bodyExps_false, List.map_append, htail, bodyW_expos, List.filter_cons, filter_ne_top_map]
  by_cases hs : Tw.SameLeaf (some k) none
  · rw [toExp_sameLeaf_O, decide_eq_true hs, ite_eq_left rfl, hRw.same _ _ hs]
    simp
  · rw [toExp_sameLeaf_O, decide_eq_false hs, ← toExp_e_O hRw hs]
    simp

/-- The exponents of `U = E` in the specification: `E` first (`0`), then the `p_kl`. The constant term is the last
term of `Identity.potU`. -/
theorem uExps_eq (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) :
    (L6.F2S.uExps (toExp Tz htz) (toExp Tw htw)).map (fun x : ℚ => (x : WithTop ℚ)) =
      0 :: ((Identity.pairs 6).map fun kl => ((-G.x kl.1 kl.2 : ℚ) : WithTop ℚ)) := by
  unfold L6.F2S.uExps
  rw [List.map_cons, pairs6_toList, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun kl hkl => ?_
  simp only [Function.comp_apply]
  rw [xkl_eq hRz hRw (mem_pairs hkl).ne]

/-- The exponents of `I = ME` in the specification: `E` first (`0`), then the `z_kl w_kl`. -/
theorem iExps_eq (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) :
    (L6.F2S.iExps (toExp Tz htz) (toExp Tw htw)).map (fun x : ℚ => (x : WithTop ℚ)) =
      0 :: ((Identity.pairs 6).map fun kl => ((2 * G.x kl.1 kl.2 : ℚ) : WithTop ℚ)) := by
  unfold L6.F2S.iExps
  rw [List.map_cons, pairs6_toList, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun kl hkl => ?_
  simp only [Function.comp_apply]
  rw [xkl_eq hRz hRw (mem_pairs hkl).ne]

theorem perm_last {α : Type*} (L : List α) (a : α) : (L ++ [a]).Perm (a :: L) := List.perm_append_singleton a L

theorem filter_ne_top_finite (L : List (WithTop ℚ)) (h : ∀ e ∈ L, e ≠ ⊤) : (L.filter fun e => e ≠ ⊤) = L :=
  List.filter_eq_self.mpr fun e he => by simpa using h e he

/-- **Lemma 4.3 (c)** for the converted trees: the least exponent of each base identity of the specification is
attained twice. -/
theorem twice_of_germ (hm : ∀ k, 0 < m k) (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) :
    ∀ l ∈ L6.F2S.baseExps (toExp Tz htz) (toExp Tw htw), L6.F2S.MinTwice l := by
  have hmin := Identity.base_minTwice hm (by norm_num) G
  intro l hl
  simp only [L6.F2S.baseExps, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hl
  rcases hl with (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | rfl | rfl
  · have hI : Identity.bodyZ (⟨i, hi⟩ : Fin 6) ∈ Identity.base 6 := by
      simp [Identity.base]
    exact minTwice_transfer (hmin _ hI) (bodyZ_filter_eq hRz hRw ⟨i, hi⟩ ▸ List.Perm.refl _)
  · have hI : Identity.bodyW (⟨i, hi⟩ : Fin 6) ∈ Identity.base 6 := by
      simp [Identity.base]
    exact minTwice_transfer (hmin _ hI) (bodyW_filter_eq hRz hRw ⟨i, hi⟩ ▸ List.Perm.refl _)
  · have hI : Identity.potU 6 ∈ Identity.base 6 := by
      simp [Identity.base]
    refine minTwice_transfer (hmin _ hI) ?_
    rw [uExps_eq hRz hRw, filter_ne_top_finite _ (fun e he => ?_), potU_expos]
    · exact perm_last _ _
    · rw [potU_expos] at he
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at he
      rcases he with ⟨kl, -, rfl⟩ | rfl
      · exact WithTop.coe_ne_top
      · exact WithTop.coe_ne_top
  · have hI : Identity.lagr 6 ∈ Identity.base 6 := by
      simp [Identity.base]
    refine minTwice_transfer (hmin _ hI) ?_
    rw [iExps_eq hRz hRw, filter_ne_top_finite _ (fun e he => ?_), lagr_expos]
    · exact perm_last _ _
    · rw [lagr_expos] at he
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at he
      rcases he with ⟨kl, -, rfl⟩ | rfl
      · exact WithTop.coe_ne_top
      · exact WithTop.coe_ne_top

/-! ### `ℓ(x) ≤ 0` -/

theorem sum_erase_eq_two_mul (f : Fin 6 → Fin 6 → ℚ) (hf : ∀ k l, f k l = f l k) :
    ∑ k, ∑ l ∈ univ.erase k, f k l = 2 * ∑ k, ∑ l ∈ Ioi k, f k l := by
  have h1 : ∀ k : Fin 6, ∑ l ∈ univ.erase k, f k l = ∑ l ∈ Ioi k, f k l + ∑ l ∈ Iio k, f k l := by
    intro k
    rw [← Finset.sum_union (Finset.disjoint_left.mpr fun l h1 h2 => by
      rw [Finset.mem_Ioi] at h1
      rw [Finset.mem_Iio] at h2
      exact absurd (h1.trans h2) (lt_irrefl k))]
    congr 1
    ext l
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Ioi, Finset.mem_Iio]
    constructor
    · intro h
      rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · exact h.ne'
      · exact h.ne
  have h2 : ∑ k : Fin 6, ∑ l ∈ Iio k, f k l = ∑ k : Fin 6, ∑ l ∈ Ioi k, f k l := by
    rw [Finset.sum_comm' (t' := univ) (s' := fun l => Ioi l)]
    · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => hf k l
    · intro k l
      simp only [Finset.mem_univ, Finset.mem_Iio, Finset.mem_Ioi, true_and, and_true]
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_add_distrib, h2]
  ring

theorem ell_sum (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) :
    (L6.F2.pairs6.toList.map fun kl => L6.F2S.xkl (toExp Tz htz) (toExp Tw htw) kl.1 kl.2).sum = G.ell := by
  rw [pairs6_toList, List.map_map]
  have h : ((Identity.pairs 6).map ((fun kl : ℕ × ℕ => L6.F2S.xkl (toExp Tz htz) (toExp Tw htw) kl.1 kl.2) ∘
      fun kl : Fin 6 × Fin 6 => ((kl.1 : ℕ), (kl.2 : ℕ)))) = (Identity.pairs 6).map fun kl => G.x kl.1 kl.2 := by
    refine List.map_congr_left fun kl hkl => ?_
    simp only [Function.comp_apply]
    exact xkl_eq hRz hRw (mem_pairs hkl).ne
  rw [h, Identity.sum_pairs, Germ.ell, sum_erase_eq_two_mul _ G.x_comm]
  ring

end spec

/-! ## The conditions `Cond` -/

/-- **The conditions of Lemma 4.3 and `ℓ ≤ 0` for the cell of a germ.** For a germ with positive masses, diagram
`toDiagram d` and `ℓ(x) ≤ 0`, and any trees with heights realizing its exponents (Lemma 4.2), the converted trees
satisfy `Cond (Diag.ofF1 d)`. -/
theorem cond_of_germ (hm : ∀ k, 0 < m k) (G : Germ 6 m) {d : L6F1.Diagram} (hD : G.HasDiagram (toDiagram d))
    (hell : G.ell ≤ 0) {Tz Tw : TreeShape 6} {htz htw : Finset (Pt 6) → ℚ}
    (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) :
    L6.F2S.Cond (L6.F2.Diag.ofF1 d) (toExp Tz htz) (toExp Tw htw) where
  gz := good_toExp hRz
  gw := good_toExp hRw
  root_z := by
    rw [toExp_h_all]
    exact root_height_ge (pos := G.zpos) hRz (zpos_low G)
  root_w := by
    rw [toExp_h_all]
    exact root_height_ge (pos := G.wpos) hRw (wpos_low G)
  O1z k l hkl hl := by
    have hk : k < 6 := by omega
    have hab : (⟨k, hk⟩ : Fin 6) ≠ ⟨l, hl⟩ := fun e => hkl.ne (congrArg Fin.val e)
    rw [zExp_e_body hRz hk hl hkl.ne, wExp_e_body hRw hk hl hkl.ne]
    exact (G.O1 hab).2.2.1
  O1w k l hkl hl := by
    have hk : k < 6 := by omega
    have hab : (⟨k, hk⟩ : Fin 6) ≠ ⟨l, hl⟩ := fun e => hkl.ne (congrArg Fin.val e)
    rw [zExp_e_body hRz hk hl hkl.ne, wExp_e_body hRw hk hl hkl.ne]
    exact (G.O1 hab).2.2.2
  O2z k l hkl hl := by
    have hk : k < 6 := by omega
    have hab : (⟨k, hk⟩ : Fin 6) ≠ ⟨l, hl⟩ := fun e => hkl.ne (congrArg Fin.val e)
    rw [zExp_e_body hRz hk hl hkl.ne, wExp_e_body hRw hk hl hkl.ne, ofF1_zstroke d hkl hl]
    exact (G.O2 hab).1.symm.trans ((hD.1 _ _).trans ((toDiagram_zS d _ _).trans ⟨fun h => h.2, fun h => ⟨hab, h⟩⟩))
  O2w k l hkl hl := by
    have hk : k < 6 := by omega
    have hab : (⟨k, hk⟩ : Fin 6) ≠ ⟨l, hl⟩ := fun e => hkl.ne (congrArg Fin.val e)
    rw [zExp_e_body hRz hk hl hkl.ne, wExp_e_body hRw hk hl hkl.ne, ofF1_wstroke d hkl hl]
    exact (G.O2 hab).2.symm.trans ((hD.2.1 _ _).trans ((toDiagram_wS d _ _).trans ⟨fun h => h.2, fun h => ⟨hab, h⟩⟩))
  circ_z k hk := by
    have hsl : (toExp Tz htz).T.sameLeaf k L6.F2S.O = decide (Tz.SameLeaf (some ⟨k, hk⟩) none) :=
      toTS_sameLeaf Tz (some ⟨k, hk⟩) none
    have hcirc : L6F1.circled d.zc k = true ↔ G.zCircle ⟨k, hk⟩ :=
      (mem_toDiagram_zCircles d ⟨k, hk⟩).symm.trans (hD.2.2.1 ⟨k, hk⟩).symm
    rw [hsl, ofF1_zc d hk]
    by_cases hs : Tz.SameLeaf (some ⟨k, hk⟩) none
    · rw [ite_eq_left (decide_eq_true hs), Bool.eq_false_iff]
      intro hc
      have h1 := hRz.same _ _ hs
      rw [G.hz_some_none] at h1
      have h2 := hcirc.mp hc
      unfold Germ.zCircle at h2
      rw [h1] at h2
      exact WithTop.top_ne_coe h2
    · rw [ite_eq_right (by simpa using hs)]
      have h1 := toExp_e_eq hRz hs
      rw [G.hz_some_none] at h1
      rw [hcirc]
      unfold Germ.zCircle
      rw [← h1]
      exact WithTop.coe_inj.symm
  circ_w k hk := by
    have hsl : (toExp Tw htw).T.sameLeaf k L6.F2S.O = decide (Tw.SameLeaf (some ⟨k, hk⟩) none) :=
      toTS_sameLeaf Tw (some ⟨k, hk⟩) none
    have hcirc : L6F1.circled d.wc k = true ↔ G.wCircle ⟨k, hk⟩ :=
      (mem_toDiagram_wCircles d ⟨k, hk⟩).symm.trans (hD.2.2.2 ⟨k, hk⟩).symm
    rw [hsl, ofF1_wc d hk]
    by_cases hs : Tw.SameLeaf (some ⟨k, hk⟩) none
    · rw [ite_eq_left (decide_eq_true hs), Bool.eq_false_iff]
      intro hc
      have h1 := hRw.same _ _ hs
      rw [G.hw_some_none] at h1
      have h2 := hcirc.mp hc
      unfold Germ.wCircle at h2
      rw [h1] at h2
      exact WithTop.top_ne_coe h2
    · rw [ite_eq_right (by simpa using hs)]
      have h1 := toExp_e_eq hRw hs
      rw [G.hw_some_none] at h1
      rw [hcirc]
      unfold Germ.wCircle
      rw [← h1]
      exact WithTop.coe_inj.symm
  com_z := comOk_toTS hRz.wf (G.three_children_z hm hRz)
  com_w := comOk_toTS hRw.wf (G.three_children_w hm hRw)
  twice := twice_of_germ hm hRz hRw
  ell := by
    rw [ell_sum hRz hRw]
    exact hell

/-- **The cell of a germ satisfies `Cond`, with the exponents of the germ.** For a germ with positive masses, diagram
`toDiagram d` and `ℓ(x) ≤ 0`, there are complete trees with heights `Xz`, `Xw` of the specification search satisfying
`Cond (Diag.ofF1 d)` whose exponents are those of the germ: `Xz.e (ptN p) (ptN q) = e(z_p − z_q)` and
`Xw.e (ptN p) (ptN q) = e(w_p − w_q)` for the points with `z_p ≠ z_q` (resp. `w_p ≠ w_q`), that is, on different
leaves. (They are `toExp Tz htz`, `toExp Tw htw` for the trees of Lemma 4.2.) -/
theorem exists_cond (hm : ∀ k, 0 < m k) (G : Germ 6 m) {d : L6F1.Diagram} (hD : G.HasDiagram (toDiagram d))
    (hell : G.ell ≤ 0) :
    ∃ Xz Xw : L6.F2S.ExpTree, L6.F2S.Cond (L6.F2.Diag.ofF1 d) Xz Xw ∧
      (∀ p q : Pt 6, G.zpos p ≠ G.zpos q → Xz.e (ptN p) (ptN q) = (G.zpos p - G.zpos q).order) ∧
      (∀ p q : Pt 6, G.wpos p ≠ G.wpos q → Xw.e (ptN p) (ptN q) = (G.wpos p - G.wpos q).order) := by
  obtain ⟨Tz, htz, hRz⟩ := G.exists_tree_z (by norm_num)
  obtain ⟨Tw, htw, hRw⟩ := G.exists_tree_w (by norm_num)
  exact ⟨toExp Tz htz, toExp Tw htw, cond_of_germ hm G hD hell hRz hRw,
    fun p q hpq => zExp_e_eq_order hRz hpq, fun p q hpq => wExp_e_eq_order hRw hpq⟩

end CC6Compose
