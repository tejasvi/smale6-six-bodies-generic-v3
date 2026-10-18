import L6Sound.F2S.TreeAux1

/-!
# Trees of the specification search: restrictions of a good complete tree

* `WF.of_equiv`: a tree with the nodes (as a set) and the body on the leaf of `O` of a well-formed tree, without
  repetition, is well formed;
* `cover_restrict`: the smallest node of a good complete tree containing a node `D` of its restriction to `S` meets
  `S` in `D`;
* `lca_aux`: for two points on different leaves of the restriction, their lowest common ancestor in the restriction
  is the restriction of their lowest common ancestor in the complete tree, which is its smallest cover;
* `levelFacts'`, `restrict_init'`, `restrict_all'`, `comOk_equiv'`, `key_equiv'`.
-/

namespace L6.F2S.TreeAux

theorem _root_.L6.F2S.WF.of_equiv {T R : TS} {S : Nat} (hR : WF R S) (h : T.Equiv R) (hn : T.nodes.Nodup) :
    WF T S := by
  have hm := mem_of_equiv h
  have h2 : ∀ C, twoLeaves T C = twoLeaves R C := twoLeaves_congr h.2
  refine ⟨hR.S_lt, hR.O_mem, hn, fun C hC => hR.sub C ((hm C).1 hC),
    fun C hC => (h2 C).trans (hR.two C ((hm C).1 hC)),
    fun C hC D hD => hR.lam C ((hm C).1 hC) D ((hm D).1 hD),
    fun h' => (hm S).2 (hR.root ((h2 S).symm.trans h')), fun k hk => ?_⟩
  obtain ⟨a, b, c⟩ := hR.leafO k (h.2.symm.trans hk)
  exact ⟨a, b, fun C hC => c C ((hm C).1 hC)⟩

/-- The smallest node of a good complete tree containing a node `D` of its restriction to `S` meets `S` in `D`. -/
theorem cover_restrict {X : ExpTree} (hX : X.Good) {S D : Nat} (hD : D ∈ (restrict X.T S).nodes) :
    ∃ K ∈ X.T.nodes, X.T.cover D = some K ∧ K &&& S = D ∧ subset D K = true ∧
      ∀ C ∈ X.T.nodes, subset D C = true → subset K C = true := by
  obtain ⟨C0, hC0, rfl, h2⟩ := mem_restrict.1 hD
  obtain ⟨q, hq⟩ := exists_mem_of_twoLeaves h2
  rcases pickMin_spec (fun C => subset (C0 &&& S) C) X.T.nodes (hX.1.chain_cover hq) with
    ⟨_, hnone⟩ | ⟨K, hK, hKT, hDK, hmin⟩
  · have := hnone C0 hC0
    simp [and_subset_left] at this
  · refine ⟨K, hKT, (cover_eq_pickMin _ _).trans hK, ?_, hDK, hmin⟩
    apply subset_antisymm
    · exact and_subset_and (hmin C0 hC0 (and_subset_left C0 S))
    · exact subset_and hDK (and_subset_right C0 S)

/-- The lowest common ancestor of two points of `S` on different leaves of a tree equivalent to the restriction. -/
theorem lca_aux {X : ExpTree} (hX : X.Good) {S : Nat} {T : TS} (hT : T.Equiv (restrict X.T S)) (hTw : WF T S)
    {a b : Nat} (ha : a < 7) (hb : b < 7) (haS : mem a S = true) (hbS : mem b S = true)
    (hab : T.lrep a ≠ T.lrep b) : ∃ D ∈ T.nodes, T.lca a b = some D ∧ X.hc D = X.e a b := by
  have hm := mem_of_equiv hT
  have hall := all_mem_nodes hX.1
  have hmemall : ∀ x, x < 7 → mem x all = true := by
    intro x hx; unfold mem all; interval_cases x <;> decide
  rcases pickMin_spec (fun C => mem a C && mem b C) X.T.nodes (hX.1.chain_lca a b) with
    ⟨_, hnone⟩ | ⟨M, hM, hMT, habM, hminM⟩
  · have := hnone all hall
    simp [hmemall a ha, hmemall b hb] at this
  · have haM : mem a M = true := by simp only [Bool.and_eq_true] at habM; exact habM.1
    have hbM : mem b M = true := by simp only [Bool.and_eq_true] at habM; exact habM.2
    have haD : mem a (M &&& S) = true := by rw [mem_and, haM, haS]; rfl
    have hbD : mem b (M &&& S) = true := by rw [mem_and, hbM, hbS]; rfl
    have hD : M &&& S ∈ (restrict X.T S).nodes := by
      apply mem_restrict'.2
      refine ⟨M, hMT, rfl, (twoLeaves_iff _ _).2 ⟨a, b, ha, hb, haD, hbD, ?_⟩⟩
      rwa [← lrep_congr hT.2, ← lrep_congr hT.2]
    have hDT := (hm _).2 hD
    refine ⟨M &&& S, hDT, ?_, ?_⟩
    · rw [lca_eq_pickMin]
      apply pickMin_eq_some (hTw.chain_lca a b) hDT
      · show (mem a (M &&& S) && mem b (M &&& S)) = true
        rw [haD, hbD]; rfl
      · intro E hE habE
        obtain ⟨C, hC, rfl, _⟩ := mem_restrict.1 ((hm E).1 hE)
        simp only [Bool.and_eq_true, mem_and] at habE
        exact and_subset_and (hminM C hC (by simp [habE.1.1, habE.2.1]))
    · obtain ⟨K, hKT, hK, _, hDK, hminK⟩ := cover_restrict hX hD
      have hKM : subset K M = true := hminK M hMT (and_subset_left M S)
      have hMK : subset M K = true := hminM K hKT (by
        show (mem a K && mem b K) = true
        rw [mem_of_subset hDK haD, mem_of_subset hDK hbD]; rfl)
      have hKeq := subset_antisymm hKM hMK
      have hlca : X.T.lca a b = some M := (lca_eq_pickMin X.T a b).trans hM
      simp only [ExpTree.hc, ExpTree.e, hK, hlca, hKeq, Option.getD_some]

/-- **The facts of a tree equivalent to the restriction of a good complete tree.** -/
theorem levelFacts' {X : ExpTree} (hX : X.Good) (hroot : -2 ≤ X.h all) {S : Nat} (hS : S < 128)
    (hO : mem O S = true) {T : TS} (hT : T.Equiv (restrict X.T S)) (hTn : T.nodes.Nodup) : LevelFacts X T S := by
  have hR := restrict_wf_of_good hX hS hO
  have hTw : WF T S := hR.of_equiv hT hTn
  have hm := mem_of_equiv hT
  have hall : all ∈ X.T.nodes := all_mem_nodes hX.1
  have hge : ∀ K ∈ X.T.nodes, -2 ≤ X.h K := by
    intro K hK
    by_cases hKa : K = all
    · rw [hKa]; exact hroot
    · have := hX.2 K hK all hall (ssubset_of (hX.1.sub K hK) hKa)
      linarith
  have hhc : ∀ D K, X.T.cover D = some K → X.hc D = X.h K := by
    intro D K h; simp only [ExpTree.hc, h, Option.getD_some]
  have hlr : ∀ x, mem x S = true → T.lrep x = X.T.lrep x := by
    intro x hx
    rw [lrep_eq, lrep_eq, hT.2, restrict_leafO]
    have e : restrictLeafO X.T.leafO S = some x ↔ X.T.leafO = some x := by
      rw [restrictLeafO_eq_some]; exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩
    by_cases h : X.T.leafO = some x
    · rw [ite_eq_left (e.2 h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (e.1 h')), ite_eq_right h]
  refine ⟨hTn, ?_, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨KC, hKCT, hKC, hKCS, _, hminC⟩ := cover_restrict hX ((hm C).1 hC)
    obtain ⟨q, hq⟩ := exists_mem_of_twoLeaves (hTw.two C hC)
    rcases pickMin_spec (fun E => ssubset C E) T.nodes (hTw.chain_parent hq) with
      ⟨hnone, _⟩ | ⟨P, hP, hPT, hCP, _⟩
    · left
      exact ⟨(parent_eq_pickMin T C).trans hnone, by rw [hhc C KC hKC]; exact hge KC hKCT⟩
    · right
      refine ⟨P, hPT, (parent_eq_pickMin T C).trans hP, ?_⟩
      obtain ⟨KP, hKPT, hKP, hKPS, hPKP, _⟩ := cover_restrict hX ((hm P).1 hPT)
      rw [hhc C KC hKC, hhc P KP hKP]
      have hCP' := (ssubset_iff _ _).1 hCP
      have hsub : subset KC KP = true := hminC KP hKPT (subset_trans hCP'.1 hPKP)
      have hne : KC ≠ KP := by
        intro e; apply hCP'.2; rw [← hKCS, ← hKPS, e]
      exact hX.2 KC hKCT KP hKPT (ssubset_of hsub hne)
  · intro k l hk hl hkl hkS hlS
    apply lca_aux hX hT hTw (by omega) (by omega) hkS hlS
    rw [lrep_eq, lrep_eq]
    by_cases h1 : T.leafO = some k
    · have h2 : ¬ T.leafO = some l := by rw [h1]; simp [hkl]
      rw [ite_eq_left h1, ite_eq_right h2]; unfold O; omega
    · by_cases h2 : T.leafO = some l
      · rw [ite_eq_right h1, ite_eq_left h2]; unfold O; omega
      · rw [ite_eq_right h1, ite_eq_right h2]; exact hkl
  · intro k _ hkS _
    unfold TS.sameLeaf
    rw [hlr k hkS, hlr O hO]
  · intro k hk hkS _ hsame
    apply lca_aux hX hT hTw (by omega) (by unfold O; norm_num) hkS hO
    intro e
    unfold TS.sameLeaf at hsame
    rw [e] at hsame
    simp at hsame

/-- Restricted to `{O}`, a good complete tree is the tree of the start of the search. -/
theorem restrict_init' {X : ExpTree} (hX : X.Good) : TS.init.Equiv (restrict X.T (single O)) := by
  have hlo : restrictLeafO X.T.leafO (single O) = none := by
    cases h : X.T.leafO with
    | none => rfl
    | some k =>
      have hk := (hX.1.leafO k h).1
      have : mem k (single O) = false := by
        rw [mem_single]; unfold O; simp only [decide_eq_false_iff_not]; omega
      simp [restrictLeafO, this]
  refine ⟨?_, hlo.symm⟩
  have : (restrict X.T (single O)).nodes = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro D hD
    obtain ⟨C, _, rfl, h2⟩ := mem_restrict.1 hD
    rw [hlo, twoLeaves_iff] at h2
    obtain ⟨a, b, _, _, ha, hb, hab⟩ := h2
    rw [mem_and, mem_single] at ha hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha hb
    apply hab
    rw [← ha.2, ← hb.2]
  exact congrArg List.toFinset this.symm

/-- Restricted to all seven points, a good complete tree is itself. -/
theorem restrict_all' {X : ExpTree} (hX : X.Good) : (restrict X.T all).Equiv X.T := by
  have hlo : restrictLeafO X.T.leafO all = X.T.leafO := by
    cases h : X.T.leafO with
    | none => rfl
    | some k =>
      have hk := (hX.1.leafO k h).2.1
      simp [restrictLeafO, hk]
  refine ⟨?_, hlo⟩
  ext D
  rw [List.mem_toFinset, List.mem_toFinset, mem_restrict, hlo]
  constructor
  · rintro ⟨C, hC, rfl, _⟩
    rw [and_eq_self (hX.1.sub C hC)]; exact hC
  · intro hD
    refine ⟨D, hD, (and_eq_self (hX.1.sub D hD)).symm, ?_⟩
    exact (twoLeaves_congr (T := ⟨[], X.T.leafO⟩) (T' := X.T) rfl D).trans (hX.1.two D hD)

theorem classes_congr {T T' : TS} (h : T.leafO = T'.leafO) (S : Nat) : T.classes S = T'.classes S := by
  have e1 : T.lrep = T'.lrep := funext (lrep_congr h)
  have e2 : T.leafClass = T'.leafClass := funext fun p => by unfold TS.leafClass; rw [h]
  unfold TS.classes
  rw [e1, e2]

theorem perm_any_eq {L L' : List Nat} (hp : L.Perm L') (f : Nat → Bool) : L.any f = L'.any f := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hp.mem_iff.1 hx, h⟩, fun ⟨x, hx, h⟩ => ⟨x, hp.mem_iff.2 hx, h⟩⟩

theorem numChildren_perm {T T' : TS} {S : Nat} (hp : T.nodes.Perm T'.nodes) (hcl : T.classes S = T'.classes S)
    (C : Nat) : numChildren T S C = numChildren T' S C := by
  unfold numChildren
  have hs := hp.filter (fun D => ssubset D C)
  have e1 : ∀ x, ((T.nodes.filter fun D => ssubset D C).any fun E => ssubset x E) =
      ((T'.nodes.filter fun D => ssubset D C).any fun E => ssubset x E) := fun x => perm_any_eq hs _
  have e2 : ∀ x, ((T.nodes.filter fun D => ssubset D C).any fun D => subset x D) =
      ((T'.nodes.filter fun D => ssubset D C).any fun D => subset x D) := fun x => perm_any_eq hs _
  simp only [e1, e2, hcl]
  rw [(hs.filter _).length_eq]

/-- The root rule depends only on the nodes as a set. -/
theorem comOk_equiv' {T T' : TS} (h : T.Equiv T') (hn : T.nodes.Nodup) (hn' : T'.nodes.Nodup) (S : Nat) :
    comOk T S = comOk T' S := by
  have hp := List.perm_of_nodup_nodup_toFinset_eq hn hn' h.1
  unfold comOk
  rw [numChildren_perm hp (classes_congr h.2 S) S]
  congr 1
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem, List.contains_iff_mem]
  exact hp.mem_iff

/-- The key depends only on the nodes as a set. -/
theorem key_equiv' {T T' : TS} (h : T.Equiv T') (hn : T.nodes.Nodup) (hn' : T'.nodes.Nodup) : T.key = T'.key := by
  have hp := List.perm_of_nodup_nodup_toFinset_eq hn hn' h.1
  have trans : ∀ a b c : Nat, decide (a ≤ b) = true → decide (b ≤ c) = true → decide (a ≤ c) = true := by
    intro a b c h1 h2; simp only [decide_eq_true_eq] at h1 h2 ⊢; omega
  have total : ∀ a b : Nat, (decide (a ≤ b) || decide (b ≤ a)) = true := by
    intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  have hs : ∀ L : List Nat, (L.mergeSort (· ≤ ·)).SortedLE := fun L => by
    rw [List.sortedLE_iff_pairwise]
    exact (List.pairwise_mergeSort trans total L).imp fun h => by simpa using h
  unfold TS.key
  rw [h.2]
  congr 1
  exact List.Perm.eq_of_sortedLE (hs _) (hs _)
    ((List.mergeSort_perm _ _).trans (hp.trans (List.mergeSort_perm _ _).symm))

end L6.F2S.TreeAux
