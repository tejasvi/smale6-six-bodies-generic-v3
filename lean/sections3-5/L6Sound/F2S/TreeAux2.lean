import L6Sound.F2S.TreeAux1

/-!
# Trees of the specification search: inserting a point

`insert_complete`: a well-formed tree `T'` on `S ∪ {p}` (`p` a body not in `S`, `O ∈ S`) is, up to the order of the
nodes, one of the insertions of `p` into any tree `T` equivalent to its restriction to `S`:

* (a) `p` is the body on the leaf of `O`: `T.atO p`;
* (b) otherwise, with `C*` the smallest node of `T'` containing `p` and `Y = C* ∖ {p}`:
  - `Y` has two leaves and is not a node of `T'`: `p` is attached to the node `Y` (`T.attach Y p`);
  - `Y` is a node of `T'`, or `Y` has no two leaves (then `Y` is a leaf class of `T`): `p` is on a new node
    subdividing the edge above `Y` (`T.subdivide Y p`), or under a new root when `Y = S` (`T.newRoot S p`).

`options_complete'`: the case of the restrictions of a good complete tree.
-/

namespace L6.F2S.TreeAux

/-! ## Masks with and without the point `p` -/

theorem and_of_not_mem {C S p : Nat} (hC : subset C (ins p S) = true) (hpC : mem p C = false) :
    C &&& S = C := by
  apply mask_ext; intro x
  cases hx : mem x C
  · rw [mem_and, hx]; rfl
  · have hxp : x ≠ p := fun e => by rw [e, hpC] at hx; exact absurd hx (by simp)
    exact mem_and_of_ne hC hx hxp

theorem ins_and_of_mem {C S p : Nat} (hC : subset C (ins p S) = true) (hpC : mem p C = true) :
    ins p (C &&& S) = C := by
  apply mask_ext; intro x
  rw [mem_ins, mem_and]
  by_cases hxp : p = x
  · rw [← hxp, hpC]; simp
  · cases hx : mem x C
    · simp [hxp]
    · have h := mem_and_of_ne hC hx (Ne.symm hxp)
      rw [mem_and, hx, Bool.true_and] at h
      simp [h]

theorem ins_and_eq {E S p : Nat} (hE : subset E S = true) (hpS : mem p S = false) : ins p E &&& S = E := by
  apply mask_ext; intro x
  rw [mem_and, mem_ins]
  by_cases hxp : p = x
  · rw [← hxp, hpS, not_mem_of_subset hE hpS]; simp
  · cases hx : mem x E
    · simp [hxp]
    · simp [mem_of_subset hE hx]

theorem ite_ins_and {E S p : Nat} (b : Bool) (hE : subset E S = true) (hpS : mem p S = false) :
    (if b = true then ins p E else E) &&& S = E := by
  cases b
  · rw [ite_eq_right (show ¬(false = true) by simp)]; exact and_eq_self hE
  · rw [ite_eq_left rfl]; exact ins_and_eq hE hpS

theorem nodup_map_of_and {L : List Nat} {S : Nat} {φ : Nat → Nat} (hL : L.Nodup)
    (hφ : ∀ E ∈ L, φ E &&& S = E) : (L.map φ).Nodup :=
  hL.map_on fun x hx y hy hxy => by rw [← hφ x hx, ← hφ y hy, hxy]

/-! ## Leaves -/

/-- Nodes are unions of leaves: a node containing a point contains every point on the same leaf. -/
theorem _root_.L6.F2S.WF.mem_of_lrep_eq {T : TS} {S : Nat} (hT : WF T S) {C x q : Nat} (hC : C ∈ T.nodes)
    (hq : mem q C = true) (hxq : T.lrep x = T.lrep q) : mem x C = true := by
  rw [lrep_eq, lrep_eq] at hxq
  by_cases hx : T.leafO = some x
  · by_cases hq' : T.leafO = some q
    · rw [hx] at hq'; cases hq'; exact hq
    · rw [ite_eq_left hx, ite_eq_right hq'] at hxq
      rw [← hxq] at hq
      rw [← (hT.leafO x hx).2.2 C hC]; exact hq
  · by_cases hq' : T.leafO = some q
    · rw [ite_eq_right hx, ite_eq_left hq'] at hxq
      rw [hxq, (hT.leafO q hq').2.2 C hC]; exact hq
    · rw [ite_eq_right hx, ite_eq_right hq'] at hxq
      rw [hxq]; exact hq

/-- The points of a leaf class: those with the same representative. -/
theorem mem_leafClass {T : TS} (hk : ∀ k, T.leafO = some k → k ≠ O) {r : Nat} (hr : T.lrep r = r) (x : Nat) :
    mem x (T.leafClass r) = true ↔ T.lrep x = r := by
  revert hr
  unfold TS.leafClass TS.lrep
  cases h : T.leafO with
  | none =>
    intro _
    simp only [mem_single, decide_eq_true_eq]
    exact eq_comm
  | some k =>
    have hkO : k ≠ O := hk k h
    intro hr
    unfold O at hkO hr ⊢
    simp only [beq_iff_eq, Bool.or_eq_true] at hr ⊢
    split_ifs at hr ⊢ <;>
      simp only [mem_or, mem_single, Bool.or_eq_true, decide_eq_true_eq] <;> constructor <;> intro <;> omega

/-! ## The setting of an insertion -/

/-- A well-formed tree `T'` on `S ∪ {p}` and a tree `T` with the nodes of the restriction of `T'` to `S` (without
repetition) and its body on the leaf of `O`. -/
structure InsSetting (T' T : TS) (S p : Nat) : Prop where
  wf : WF T' (ins p S)
  p6 : p < 6
  pS : mem p S = false
  OS : mem O S = true
  memT : ∀ D, D ∈ T.nodes ↔ D ∈ (restrict T' S).nodes
  lo : T.leafO = restrictLeafO T'.leafO S
  nodup : T.nodes.Nodup

namespace InsSetting

variable {T' T : TS} {S p : Nat}

theorem S_lt (H : InsSetting T' T S p) : S < 128 :=
  lt_of_le_of_lt (subset_le (subset_ins_self p S)) H.wf.S_lt

theorem sub (H : InsSetting T' T S p) {D : Nat} (hD : D ∈ T.nodes) : subset D S = true := by
  obtain ⟨C, _, rfl, _⟩ := mem_restrict.1 ((H.memT D).1 hD)
  exact and_subset_right C S

theorem p_ne_O (H : InsSetting T' T S p) : p ≠ O := by
  have := H.p6; unfold O; omega

theorem lo_ne_O (H : InsSetting T' T S p) : ¬ T'.leafO = some O := fun h => by
  have := (H.wf.leafO O h).1; unfold O at this; omega

/-- (a) `p` on the leaf of `O`. -/
theorem atO_case (H : InsSetting T' T S p) (hlo : T'.leafO = some p) :
    ∃ T'' ∈ T.options S p, T''.Equiv T' ∧ T''.nodes.Nodup := by
  have hTlo : T.leafO = none := by
    rw [H.lo, hlo]; simp [restrictLeafO, H.pS]
  have hOp : ∀ C ∈ T'.nodes, mem O C = mem p C := fun C hC => (H.wf.leafO p hlo).2.2 C hC
  have hf : ∀ C ∈ T'.nodes, (if mem O (C &&& S) = true then ins p (C &&& S) else C &&& S) = C := by
    intro C hC
    have hsub := H.wf.sub C hC
    cases hpC : mem p C
    · have h0 : mem O (C &&& S) = false := by rw [mem_and, hOp C hC, hpC]; rfl
      rw [h0, ite_eq_right (show ¬(false = true) by simp), and_of_not_mem hsub hpC]
    · have h0 : mem O (C &&& S) = true := by rw [mem_and, hOp C hC, hpC, H.OS]; rfl
      rw [h0, ite_eq_left rfl, ins_and_of_mem hsub hpC]
  have hc : (p != O && mem O S && T.leafO.isNone) = true := by
    simp [H.p_ne_O, H.OS, hTlo]
  refine ⟨T.atO p, ?_, ⟨?_, by simp [TS.atO, hlo]⟩, ?_⟩
  · unfold TS.options
    rw [ite_eq_left hc]
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2
      (Or.inl (List.mem_singleton.2 rfl))))))
  · ext D
    rw [List.mem_toFinset, List.mem_toFinset]
    show D ∈ T.nodes.map _ ↔ _
    simp only [List.mem_map]
    constructor
    · rintro ⟨E, hE, rfl⟩
      obtain ⟨C, hC, rfl, _⟩ := mem_restrict.1 ((H.memT E).1 hE)
      rw [hf C hC]; exact hC
    · intro hD
      refine ⟨D &&& S, (H.memT _).2 (mem_restrict.2 ⟨D, hD, rfl, ?_⟩), hf D hD⟩
      -- two points of `D ∖ {p}`: the representatives of two points of `D` on different leaves
      rw [← H.lo, hTlo, twoLeaves_iff]
      obtain ⟨a, b, ha, hb, haD, hbD, hab⟩ := (twoLeaves_iff _ _).1 (H.wf.two D hD)
      have hsub := H.wf.sub D hD
      have key : ∀ x, x < 7 → mem x D = true → T'.lrep x < 7 ∧ mem (T'.lrep x) (D &&& S) = true := by
        intro x hx hxD
        rw [lrep_eq, hlo]
        by_cases hxp : p = x
        · rw [ite_eq_left (show some p = some x by rw [hxp])]
          refine ⟨by unfold O; norm_num, ?_⟩
          rw [mem_and, hOp D hD, hxp, hxD, H.OS]; rfl
        · rw [ite_eq_right (show ¬ some p = some x by simpa using hxp)]
          exact ⟨hx, mem_and_of_ne hsub hxD (Ne.symm hxp)⟩
      obtain ⟨ha', haS⟩ := key a ha haD
      obtain ⟨hb', hbS⟩ := key b hb hbD
      exact ⟨T'.lrep a, T'.lrep b, ha', hb', haS, hbS, hab⟩
  · show (T.nodes.map _).Nodup
    exact nodup_map_of_and H.nodup fun E hE => ite_ins_and _ (H.sub hE) H.pS

/-- When `p` is not the body on the leaf of `O`, the restriction keeps the body on the leaf of `O`. -/
theorem lo_eq (H : InsSetting T' T S p) (hlo : T'.leafO ≠ some p) : T.leafO = T'.leafO := by
  rw [H.lo]
  cases h : T'.leafO with
  | none => rfl
  | some k =>
    have hk := H.wf.leafO k h
    have hkp : k ≠ p := fun e => hlo (by rw [h, e])
    have hkS : mem k S = true := by
      have := hk.2.1; rw [mem_ins] at this; simpa [Ne.symm hkp] using this
    simp [restrictLeafO, hkS]

theorem memT' (H : InsSetting T' T S p) (hlo : T'.leafO ≠ some p) (D : Nat) :
    D ∈ T.nodes ↔ ∃ C ∈ T'.nodes, D = C &&& S ∧ twoLeaves T' D = true := by
  rw [H.memT, mem_restrict]
  have : (⟨[], restrictLeafO T'.leafO S⟩ : TS).leafO = T'.leafO := by
    show restrictLeafO T'.leafO S = T'.leafO
    rw [← H.lo]; exact H.lo_eq hlo
  simp only [twoLeaves_congr this]

/-- The smallest node containing `p` (the whole set `S ∪ {p}` is a node, since `p` and `O` are on different
leaves). -/
theorem exists_cstar (H : InsSetting T' T S p) (hlo : T'.leafO ≠ some p) :
    ∃ Cs ∈ T'.nodes, mem p Cs = true ∧ ∀ C ∈ T'.nodes, mem p C = true → subset Cs C = true := by
  have chain : ∀ C ∈ T'.nodes, ∀ D ∈ T'.nodes, mem p C = true → mem p D = true →
      subset C D = true ∨ subset D C = true := fun C hC D hD hpC hpD => H.wf.nested hC hD hpC hpD
  rcases pickMin_spec (fun C => mem p C) T'.nodes chain with ⟨_, hnone⟩ | ⟨M, _, hM, hpM, hmin⟩
  · exfalso
    have hroot : ins p S ∈ T'.nodes := by
      apply H.wf.root
      rw [twoLeaves_iff]
      refine ⟨p, O, by have := H.p6; omega, by unfold O; norm_num, mem_ins_self p S, ?_, ?_⟩
      · rw [mem_ins, H.OS]; rfl
      · rw [lrep_eq, lrep_eq, ite_eq_right hlo, ite_eq_right H.lo_ne_O]
        exact H.p_ne_O
    have := hnone _ hroot
    simp [mem_ins_self] at this
  · exact ⟨M, hM, hpM, hmin⟩

/-- `subdivide S p` has the nodes of `newRoot S p`. -/
theorem newRoot_eq_subdivide (H : InsSetting T' T S p) : (T.subdivide S p).nodes = (T.newRoot S p).nodes := by
  show T.nodes.map _ ++ [ins p S] = T.nodes ++ [ins p S]
  congr 1
  conv_rhs => rw [← List.map_id T.nodes]
  apply List.map_congr_left
  intro C hC
  have : ¬ ssubset S C = true := by
    rw [ssubset_iff]; intro h; exact h.2 (subset_antisymm h.1 (H.sub hC))
  show (if ssubset S C = true then ins p C else C) = C
  rw [ite_eq_right this]

end InsSetting

/-- Case (b): `p` not on the leaf of `O`, and `Cs` the smallest node of `T'` containing `p`. -/
structure CsSetting (T' T : TS) (S p Cs : Nat) : Prop extends InsSetting T' T S p where
  lo' : T'.leafO ≠ some p
  cs_mem : Cs ∈ T'.nodes
  p_cs : mem p Cs = true
  cs_min : ∀ C ∈ T'.nodes, mem p C = true → subset Cs C = true

namespace CsSetting

variable {T' T : TS} {S p Cs C : Nat}

theorem and_eq (H : CsSetting T' T S p Cs) (hC : C ∈ T'.nodes) (hpC : mem p C = false) : C &&& S = C :=
  and_of_not_mem (H.wf.sub C hC) hpC

theorem ins_and (H : CsSetting T' T S p Cs) (hC : C ∈ T'.nodes) (hpC : mem p C = true) : ins p (C &&& S) = C :=
  ins_and_of_mem (H.wf.sub C hC) hpC

/-- `Y = Cs ∖ {p}` is not empty. -/
theorem Y_nonempty (H : CsSetting T' T S p Cs) : ∃ q, mem q (Cs &&& S) = true := by
  obtain ⟨a, b, _, _, haC, hbC, hab⟩ := (twoLeaves_iff _ _).1 (H.wf.two Cs H.cs_mem)
  by_cases hap : a = p
  · have hbp : b ≠ p := fun h => hab (by rw [hap, h])
    exact ⟨b, mem_and_of_ne (H.wf.sub Cs H.cs_mem) hbC hbp⟩
  · exact ⟨a, mem_and_of_ne (H.wf.sub Cs H.cs_mem) haC hap⟩

/-- A node without `p` containing `Y` is `Y`. -/
theorem eq_Y (H : CsSetting T' T S p Cs) (hC : C ∈ T'.nodes) (hpC : mem p C = false)
    (hYC : subset (Cs &&& S) C = true) : C = Cs &&& S := by
  obtain ⟨q, hq⟩ := H.Y_nonempty
  have hqC := mem_of_subset hYC hq
  have hqCs := mem_of_subset (and_subset_left Cs S) hq
  rcases H.wf.nested hC H.cs_mem hqC hqCs with h | h
  · apply subset_antisymm _ hYC
    rw [← H.and_eq hC hpC]; exact and_subset_and h
  · rw [mem_of_subset h H.p_cs] at hpC; exact absurd hpC (by simp)

/-- A node containing `p`, other than `Cs`, minus `p` strictly contains `Y`. -/
theorem ssubset_Y (H : CsSetting T' T S p Cs) (hC : C ∈ T'.nodes) (hpC : mem p C = true) (hne : C ≠ Cs) :
    ssubset (Cs &&& S) (C &&& S) = true := by
  refine ssubset_of (and_subset_and (H.cs_min C hC hpC)) fun h => hne ?_
  rw [← H.ins_and hC hpC, ← h, H.ins_and H.cs_mem H.p_cs]

theorem two_of_not_mem (H : CsSetting T' T S p Cs) (hC : C ∈ T'.nodes) (hpC : mem p C = false) :
    twoLeaves T' (C &&& S) = true := by
  rw [H.and_eq hC hpC]; exact H.wf.two C hC

/-- A node containing `p`, other than `Cs`, minus `p` has two leaves (else it would be inside `Cs`). -/
theorem two_of_ne (H : CsSetting T' T S p Cs) (hC : C ∈ T'.nodes) (hpC : mem p C = true) (hne : C ≠ Cs) :
    twoLeaves T' (C &&& S) = true := by
  by_contra h2
  apply hne
  apply subset_antisymm _ (H.cs_min C hC hpC)
  obtain ⟨q, hq⟩ := H.Y_nonempty
  have hqCS : mem q (C &&& S) = true := mem_of_subset (and_subset_and (H.cs_min C hC hpC)) hq
  have hqCs : mem q Cs = true := mem_of_subset (and_subset_left Cs S) hq
  have hq7 : q < 7 := lt7_of_mem H.wf.S_lt (mem_of_subset (H.wf.sub Cs H.cs_mem) hqCs)
  apply (subset_iff _ _).2
  intro x hx
  by_cases hxp : x = p
  · rw [hxp]; exact H.p_cs
  · have hxCS : mem x (C &&& S) = true := mem_and_of_ne (H.wf.sub C hC) hx hxp
    have hx7 : x < 7 := lt7_of_mem H.wf.S_lt (mem_of_subset (H.wf.sub C hC) hx)
    have hxq : T'.lrep x = T'.lrep q := by
      by_contra hne'
      exact h2 ((twoLeaves_iff _ _).2 ⟨x, q, hx7, hq7, hxCS, hqCS, hne'⟩)
    exact H.wf.mem_of_lrep_eq H.cs_mem hqCs hxq

/-- Without two leaves, `Y` is a leaf class of `T`. -/
theorem mem_classes (H : CsSetting T' T S p Cs) (h2 : ¬ twoLeaves T' (Cs &&& S) = true) :
    Cs &&& S ∈ T.classes S := by
  have hlo := H.lo_eq H.lo'
  obtain ⟨q, hq⟩ := H.Y_nonempty
  have hqS : mem q S = true := mem_of_subset (and_subset_right Cs S) hq
  have hqCs : mem q Cs = true := mem_of_subset (and_subset_left Cs S) hq
  have hq7 : q < 7 := lt7_of_mem H.S_lt hqS
  have hk : ∀ k, T.leafO = some k → k ≠ O := fun k hk' => by
    rw [hlo] at hk'; have := (H.wf.leafO k hk').1; unfold O; omega
  have hr : T.lrep (T.lrep q) = T.lrep q := by
    rw [lrep_eq T q]
    by_cases hq' : T.leafO = some q
    · rw [ite_eq_left hq', lrep_eq, ite_eq_right (fun h => hk O h rfl)]
    · rw [ite_eq_right hq', lrep_eq, ite_eq_right hq']
  have hrS : T.lrep q < 7 ∧ mem (T.lrep q) S = true := by
    rw [lrep_eq]
    by_cases hq' : T.leafO = some q
    · rw [ite_eq_left hq']; exact ⟨by unfold O; norm_num, H.OS⟩
    · rw [ite_eq_right hq']; exact ⟨hq7, hqS⟩
  have hY : T.leafClass (T.lrep q) = Cs &&& S := by
    apply mask_ext; intro x
    apply Bool.eq_iff_iff.2
    rw [mem_leafClass hk hr x]
    constructor
    · intro hx
      have hx' : T'.lrep x = T'.lrep q := by rw [← lrep_congr hlo x, ← lrep_congr hlo q]; exact hx
      have hxCs := H.wf.mem_of_lrep_eq H.cs_mem hqCs hx'
      have hxp : x ≠ p := by
        intro hxp
        rw [hxp, lrep_eq T' p, ite_eq_right H.lo', lrep_eq T' q] at hx'
        by_cases hq' : T'.leafO = some q
        · rw [ite_eq_left hq'] at hx'; exact H.p_ne_O hx'
        · rw [ite_eq_right hq'] at hx'
          have := H.pS; rw [hx', hqS] at this; exact absurd this (by simp)
      exact mem_and_of_ne (H.wf.sub Cs H.cs_mem) hxCs hxp
    · intro hx
      by_contra hne
      have hx7 : x < 7 := lt7_of_mem H.S_lt (mem_of_subset (and_subset_right Cs S) hx)
      exact h2 ((twoLeaves_iff _ _).2 ⟨x, q, hx7, hq7, hx, hq, fun e => hne (by
        rw [lrep_congr hlo x, lrep_congr hlo q]; exact e)⟩)
  show Cs &&& S ∈ ((toList S).filter fun p => T.lrep p == p).map T.leafClass
  exact List.mem_map.2 ⟨T.lrep q, List.mem_filter.2 ⟨(mem_toList _ _).2 hrS, beq_iff_eq.2 hr⟩, hY⟩

/-- `Y` a node of `T'` or without two leaves: the nodes of the subdivision of the edge above `Y`. -/
theorem subdivide_nodes (H : CsSetting T' T S p Cs) (hY : twoLeaves T' (Cs &&& S) = true → Cs &&& S ∈ T'.nodes) :
    (∀ D, D ∈ (T.subdivide (Cs &&& S) p).nodes ↔ D ∈ T'.nodes) ∧ (T.subdivide (Cs &&& S) p).nodes.Nodup := by
  have hg : ∀ C ∈ T'.nodes, C ≠ Cs →
      (if ssubset (Cs &&& S) (C &&& S) = true then ins p (C &&& S) else C &&& S) = C := by
    intro C hC hne
    cases hpC : mem p C
    · have hCS := H.and_eq hC hpC
      have hns : ¬ ssubset (Cs &&& S) (C &&& S) = true := by
        intro hs
        rw [ssubset_iff, hCS] at hs
        exact hs.2 (H.eq_Y hC hpC hs.1).symm
      rw [ite_eq_right hns, hCS]
    · rw [ite_eq_left (H.ssubset_Y hC hpC hne), H.ins_and hC hpC]
  have hgY : (if ssubset (Cs &&& S) (Cs &&& S) = true then ins p (Cs &&& S) else Cs &&& S) = Cs &&& S := by
    have : ¬ ssubset (Cs &&& S) (Cs &&& S) = true := by rw [ssubset_iff]; exact fun h => h.2 rfl
    rw [ite_eq_right this]
  have hYS : subset (Cs &&& S) S = true := and_subset_right Cs S
  have hpY : mem p (Cs &&& S) = false := not_mem_of_subset hYS H.pS
  have hinsY : ins p (Cs &&& S) = Cs := H.ins_and H.cs_mem H.p_cs
  constructor
  · intro D
    show D ∈ T.nodes.map _ ++ [ins p (Cs &&& S)] ↔ _
    simp only [List.mem_append, List.mem_map, List.mem_singleton]
    constructor
    · rintro (⟨E, hE, rfl⟩ | rfl)
      · obtain ⟨C, hC, rfl, h2⟩ := (H.memT' H.lo' E).1 hE
        by_cases hne : C = Cs
        · rw [hne] at h2 ⊢; rw [hgY]; exact hY h2
        · rw [hg C hC hne]; exact hC
      · rw [hinsY]; exact H.cs_mem
    · intro hD
      by_cases hne : D = Cs
      · right; rw [hne, hinsY]
      · left
        refine ⟨D &&& S, (H.memT' H.lo' _).2 ⟨D, hD, rfl, ?_⟩, hg D hD hne⟩
        cases hpD : mem p D
        · exact H.two_of_not_mem hD hpD
        · exact H.two_of_ne hD hpD hne
  · show (T.nodes.map _ ++ [ins p (Cs &&& S)]).Nodup
    rw [List.nodup_append]
    refine ⟨nodup_map_of_and H.nodup fun E hE => ite_ins_and _ (H.sub hE) H.pS, List.nodup_singleton _, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    obtain ⟨E, hE, hEa⟩ := List.mem_map.1 ha
    have hab' : (if ssubset (Cs &&& S) E = true then ins p E else E) = ins p (Cs &&& S) :=
      hEa.trans (hab.trans hb)
    have h1 := ite_ins_and (ssubset (Cs &&& S) E) (H.sub hE) H.pS
    rw [hab', ins_and_eq hYS H.pS] at h1
    rw [← h1, hgY] at hab'
    have := congrArg (mem p) hab'
    rw [hpY, mem_ins_self] at this
    exact absurd this (by simp)

/-- `Y` with two leaves and not a node of `T'`: the nodes of the attachment of `p` to `Y`. -/
theorem attach_nodes (H : CsSetting T' T S p Cs) (h2 : twoLeaves T' (Cs &&& S) = true)
    (hnot : Cs &&& S ∉ T'.nodes) :
    (∀ D, D ∈ (T.attach (Cs &&& S) p).nodes ↔ D ∈ T'.nodes) ∧ (T.attach (Cs &&& S) p).nodes.Nodup := by
  have hh : ∀ C ∈ T'.nodes, (if subset (Cs &&& S) (C &&& S) = true then ins p (C &&& S) else C &&& S) = C := by
    intro C hC
    cases hpC : mem p C
    · have hCS := H.and_eq hC hpC
      have hns : ¬ subset (Cs &&& S) (C &&& S) = true := by
        intro hs
        rw [hCS] at hs
        apply hnot
        rw [← H.eq_Y hC hpC hs]; exact hC
      rw [ite_eq_right hns, hCS]
    · rw [ite_eq_left (and_subset_and (H.cs_min C hC hpC)), H.ins_and hC hpC]
  constructor
  · intro D
    show D ∈ T.nodes.map _ ↔ _
    simp only [List.mem_map]
    constructor
    · rintro ⟨E, hE, rfl⟩
      obtain ⟨C, hC, rfl, _⟩ := (H.memT' H.lo' E).1 hE
      rw [hh C hC]; exact hC
    · intro hD
      refine ⟨D &&& S, (H.memT' H.lo' _).2 ⟨D, hD, rfl, ?_⟩, hh D hD⟩
      cases hpD : mem p D
      · exact H.two_of_not_mem hD hpD
      · by_cases hne : D = Cs
        · rw [hne]; exact h2
        · exact H.two_of_ne hD hpD hne
  · show (T.nodes.map _).Nodup
    exact nodup_map_of_and H.nodup fun E hE => ite_ins_and _ (H.sub hE) H.pS

/-- Case (b). -/
theorem complete (H : CsSetting T' T S p Cs) : ∃ T'' ∈ T.options S p, T''.Equiv T' ∧ T''.nodes.Nodup := by
  have hlo := H.lo_eq H.lo'
  have equiv_of : ∀ T'' : TS, T''.leafO = T.leafO → (∀ D, D ∈ T''.nodes ↔ D ∈ T'.nodes) → T''.Equiv T' := by
    intro T'' hl hm
    refine ⟨?_, hl.trans hlo⟩
    ext D; rw [List.mem_toFinset, List.mem_toFinset]; exact hm D
  have newRoot_case : Cs &&& S = S → (∀ D, D ∈ (T.subdivide (Cs &&& S) p).nodes ↔ D ∈ T'.nodes) →
      (T.subdivide (Cs &&& S) p).nodes.Nodup → ∃ T'' ∈ T.options S p, T''.Equiv T' ∧ T''.nodes.Nodup := by
    intro hYS hm hn
    rw [hYS] at hm hn
    refine ⟨T.newRoot S p, List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)), equiv_of _ rfl ?_, ?_⟩
    · intro D; rw [← H.newRoot_eq_subdivide]; exact hm D
    · rw [← H.newRoot_eq_subdivide]; exact hn
  have subdivide_mem : Cs &&& S ∈ T.edges S → T.subdivide (Cs &&& S) p ∈ T.options S p := fun he =>
    List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_map.2 ⟨_, he, rfl⟩))))
  by_cases h2 : twoLeaves T' (Cs &&& S) = true
  · by_cases hY : Cs &&& S ∈ T'.nodes
    · obtain ⟨hm, hn⟩ := H.subdivide_nodes fun _ => hY
      by_cases hYS : Cs &&& S = S
      · exact newRoot_case hYS hm hn
      · refine ⟨T.subdivide (Cs &&& S) p, subdivide_mem ?_, equiv_of _ rfl hm, hn⟩
        unfold TS.edges
        apply List.mem_append.2; left
        rw [List.mem_filter]
        exact ⟨(H.memT' H.lo' _).2 ⟨Cs, H.cs_mem, rfl, h2⟩, by simpa using hYS⟩
    · obtain ⟨hm, hn⟩ := H.attach_nodes h2 hY
      refine ⟨T.attach (Cs &&& S) p, ?_, equiv_of _ rfl hm, hn⟩
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
        (List.mem_map.2 ⟨Cs &&& S, (H.memT' H.lo' _).2 ⟨Cs, H.cs_mem, rfl, h2⟩, rfl⟩))))))
  · obtain ⟨hm, hn⟩ := H.subdivide_nodes fun h => absurd h h2
    by_cases hYS : Cs &&& S = S
    · exact newRoot_case hYS hm hn
    · refine ⟨T.subdivide (Cs &&& S) p, subdivide_mem ?_, equiv_of _ rfl hm, hn⟩
      unfold TS.edges
      apply List.mem_append.2; right
      rw [List.mem_filter]
      exact ⟨H.mem_classes h2, by simpa using hYS⟩

end CsSetting

/-- **Insertion completeness.** -/
theorem insert_complete {T' : TS} {S p : Nat} (hT' : WF T' (ins p S)) (hp : p < 6) (hpS : mem p S = false)
    (hO : mem O S = true) {T : TS} (hT : T.Equiv (restrict T' S)) (hTn : T.nodes.Nodup) :
    ∃ T'' ∈ T.options S p, T''.Equiv T' ∧ T''.nodes.Nodup := by
  have H : InsSetting T' T S p := ⟨hT', hp, hpS, hO, mem_of_equiv hT, hT.2, hTn⟩
  by_cases hlo : T'.leafO = some p
  · exact H.atO_case hlo
  · obtain ⟨Cs, hCs, hpCs, hmin⟩ := H.exists_cstar hlo
    exact (CsSetting.mk H hlo hCs hpCs hmin).complete

theorem ins_lt {S p : Nat} (hS : S < 128) (hp : p < 6) : ins p S < 128 := by
  unfold ins single
  have h1 : 1 <<< p < 2 ^ 7 := by
    rw [Nat.shiftLeft_eq, one_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2 : S < 2 ^ 7 := by norm_num; omega
  have := Nat.or_lt_two_pow h2 h1
  norm_num at this
  exact this

/-- The restriction of a good complete tree to `S ∪ {p}` is one of the insertions of `p` into any tree equivalent to
its restriction to `S`. -/
theorem options_complete' {X : ExpTree} (hX : X.Good) {S p : Nat} (hS : S < 128) (hO : mem O S = true) (hp : p < 6)
    (hpS : mem p S = false) {T : TS} (hT : T.Equiv (restrict X.T S)) (hTn : T.nodes.Nodup) :
    ∃ T' ∈ T.options S p, T'.Equiv (restrict X.T (ins p S)) ∧ T'.nodes.Nodup := by
  have hS' : ins p S < 128 := ins_lt hS hp
  have hO' : mem O (ins p S) = true := by rw [mem_ins, hO]; rfl
  have hwf := restrict_wf_of_good hX hS' hO'
  have hT2 : T.Equiv (restrict (restrict X.T (ins p S)) S) :=
    equiv_trans hT (equiv_symm (restrict_restrict (subset_ins_self p S)))
  exact insert_complete hwf hp hpS hO hT2 hTn

end L6.F2S.TreeAux
