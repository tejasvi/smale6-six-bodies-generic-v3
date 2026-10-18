import L6Sound.F2S.Mask

/-!
# Trees of the specification search: basic facts

* inclusion of masks: reflexive, transitive, antisymmetric, compatible with the numerical order;
* `pickMin`: the folds `TS.lca`, `TS.parent`, `TS.cover` pick the least element (for inclusion) among the nodes with
  a property, when those nodes form a chain (`pickMin_spec`, `pickMin_eq_some`, `pickMin_congr`);
* `twoLeaves_iff`, and the restriction of a tree (`mem_restrict`), its well-formedness (`restrict_wf_of_good`) and the
  restriction of a restriction (`restrict_restrict`).
-/

namespace L6.F2S.TreeAux

/-! ## Inclusion of masks -/

theorem subset_refl (c : Nat) : subset c c = true :=
  (subset_iff c c).2 fun _ h => h

theorem subset_trans {a b c : Nat} (hab : subset a b = true) (hbc : subset b c = true) : subset a c = true :=
  (subset_iff a c).2 fun p hp => (subset_iff b c).1 hbc p ((subset_iff a b).1 hab p hp)

theorem subset_antisymm {a b : Nat} (hab : subset a b = true) (hba : subset b a = true) : a = b := by
  apply mask_ext
  intro p
  cases ha : mem p a <;> cases hb : mem p b
  · rfl
  · rw [(subset_iff b a).1 hba p hb] at ha; exact absurd ha (by simp)
  · rw [(subset_iff a b).1 hab p ha] at hb; exact absurd hb (by simp)
  · rfl

theorem subset_le {a b : Nat} (h : subset a b = true) : a ≤ b := by
  unfold subset at h
  rw [beq_iff_eq] at h
  calc a = a &&& b := h.symm
    _ ≤ b := Nat.and_le_right

theorem and_subset_left (c S : Nat) : subset (c &&& S) c = true :=
  (subset_iff _ _).2 fun p hp => by rw [mem_and] at hp; exact (Bool.and_eq_true _ _ ▸ hp).1

theorem and_subset_right (c S : Nat) : subset (c &&& S) S = true :=
  (subset_iff _ _).2 fun p hp => by rw [mem_and] at hp; exact (Bool.and_eq_true _ _ ▸ hp).2

theorem disjoint_iff {a b : Nat} : a &&& b = 0 ↔ ∀ p, ¬ (mem p a = true ∧ mem p b = true) := by
  constructor
  · intro h p ⟨ha, hb⟩
    have := congrArg (fun x => mem p x) h
    simp only [mem_and, ha, hb] at this
    exact absurd this (by unfold mem; simp)
  · intro h
    apply mask_ext
    intro p
    rw [mem_and]
    have h0 : mem p 0 = false := by unfold mem; simp
    rw [h0]
    cases ha : mem p a <;> cases hb : mem p b
    · rfl
    · rfl
    · rfl
    · exact absurd ⟨ha, hb⟩ (h p)

theorem mem_of_subset {a b p : Nat} (h : subset a b = true) (hp : mem p a = true) : mem p b = true :=
  (subset_iff a b).1 h p hp

theorem ssubset_of {a b : Nat} (h : subset a b = true) (hne : a ≠ b) : ssubset a b = true :=
  (ssubset_iff a b).2 ⟨h, hne⟩

theorem mem_ins_self (p c : Nat) : mem p (ins p c) = true := by
  rw [mem_ins]; simp

theorem mem_ins_of_ne {p q c : Nat} (h : q ≠ p) : mem p (ins q c) = mem p c := by
  rw [mem_ins]; simp [h]

theorem subset_ins_self (p c : Nat) : subset c (ins p c) = true :=
  (subset_iff _ _).2 fun x hx => by rw [mem_ins, hx]; rfl

theorem not_mem_of_subset {E S p : Nat} (hE : subset E S = true) (hpS : mem p S = false) : mem p E = false := by
  cases h : mem p E
  · rfl
  · rw [mem_of_subset hE h] at hpS; exact absurd hpS (by simp)

theorem and_subset_and {C D S : Nat} (h : subset C D = true) : subset (C &&& S) (D &&& S) = true :=
  (subset_iff _ _).2 fun x hx => by
    rw [mem_and] at hx ⊢
    simp only [Bool.and_eq_true] at hx ⊢
    exact ⟨mem_of_subset h hx.1, hx.2⟩

theorem subset_and {D C S : Nat} (h1 : subset D C = true) (h2 : subset D S = true) :
    subset D (C &&& S) = true :=
  (subset_iff _ _).2 fun x hx => by
    rw [mem_and, mem_of_subset h1 hx, mem_of_subset h2 hx]; rfl

/-- A point of a subset of `S ∪ {p}` other than `p` is in `S`. -/
theorem mem_and_of_ne {D S p x : Nat} (hD : subset D (ins p S) = true) (hx : mem x D = true) (hxp : x ≠ p) :
    mem x (D &&& S) = true := by
  have h := mem_of_subset hD hx
  rw [mem_ins] at h
  rw [mem_and, hx]
  simpa [Ne.symm hxp] using h

/-! ## Picking the least element -/

/-- The step of the folds `TS.lca`, `TS.parent`, `TS.cover`. -/
def pickStep (P : Nat → Bool) (acc : Option Nat) (C : Nat) : Option Nat :=
  if P C then
    match acc with
    | none => some C
    | some D => if subset C D then some C else some D
  else acc

/-- The fold that picks the least element (for inclusion) among the elements satisfying `P`. -/
def pickMin (P : Nat → Bool) (L : List Nat) : Option Nat := L.foldl (pickStep P) none

theorem lca_eq_pickMin (T : TS) (p q : Nat) : T.lca p q = pickMin (fun C => mem p C && mem q C) T.nodes := rfl

theorem parent_eq_pickMin (T : TS) (c : Nat) : T.parent c = pickMin (fun C => ssubset c C) T.nodes := rfl

theorem cover_eq_pickMin (T : TS) (D : Nat) : T.cover D = pickMin (fun C => subset D C) T.nodes := rfl

/-- The invariant of the fold of `pickMin`. -/
def PickInv (P : Nat → Bool) (seen : List Nat) (acc : Option Nat) : Prop :=
  (acc = none ∧ ∀ C ∈ seen, P C = false) ∨
    (∃ M, acc = some M ∧ M ∈ seen ∧ P M = true ∧ ∀ C ∈ seen, P C = true → subset M C = true)

theorem pickInv_step (P : Nat → Bool) {U : List Nat}
    (chain : ∀ C ∈ U, ∀ D ∈ U, P C = true → P D = true → subset C D = true ∨ subset D C = true)
    {seen : List Nat} {acc : Option Nat} {C : Nat} (hseen : ∀ x ∈ seen, x ∈ U) (hC : C ∈ U)
    (h : PickInv P seen acc) : PickInv P (seen ++ [C]) (pickStep P acc C) := by
  unfold pickStep
  by_cases hPC : P C = true
  · rw [ite_eq_left hPC]
    rcases h with ⟨hacc, hnone⟩ | ⟨M, hacc, hM, hPM, hmin⟩
    · subst hacc
      refine Or.inr ⟨C, rfl, by simp, hPC, fun x hx hPx => ?_⟩
      rcases List.mem_append.mp hx with hx | hx
      · rw [hnone x hx] at hPx; exact absurd hPx (by simp)
      · rw [List.mem_singleton.mp hx]; exact subset_refl C
    · subst hacc
      show PickInv P (seen ++ [C]) (if subset C M = true then some C else some M)
      split_ifs with hCM
      · refine Or.inr ⟨C, rfl, by simp, hPC, fun x hx hPx => ?_⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact subset_trans hCM (hmin x hx hPx)
        · rw [List.mem_singleton.mp hx]; exact subset_refl C
      · refine Or.inr ⟨M, rfl, List.mem_append_left _ hM, hPM, fun x hx hPx => ?_⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact hmin x hx hPx
        · rw [List.mem_singleton.mp hx]
          rcases chain C hC M (hseen M hM) hPC hPM with h1 | h1
          · exact absurd h1 hCM
          · exact h1
  · rw [ite_eq_right hPC]
    have hPC' : P C = false := by simpa using hPC
    rcases h with ⟨hacc, hnone⟩ | ⟨M, hacc, hM, hPM, hmin⟩
    · refine Or.inl ⟨hacc, fun x hx => ?_⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact hnone x hx
      · rw [List.mem_singleton.mp hx]; exact hPC'
    · refine Or.inr ⟨M, hacc, List.mem_append_left _ hM, hPM, fun x hx hPx => ?_⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact hmin x hx hPx
      · rw [List.mem_singleton.mp hx] at hPx; rw [hPC'] at hPx; exact absurd hPx (by simp)

theorem pickInv_foldl (P : Nat → Bool) {U : List Nat}
    (chain : ∀ C ∈ U, ∀ D ∈ U, P C = true → P D = true → subset C D = true ∨ subset D C = true) :
    ∀ (L seen : List Nat) (acc : Option Nat), (∀ x ∈ seen, x ∈ U) → (∀ x ∈ L, x ∈ U) →
      PickInv P seen acc → PickInv P (seen ++ L) (L.foldl (pickStep P) acc)
  | [], seen, acc, _, _, h => by simpa using h
  | C :: L, seen, acc, hs, hL, h => by
    rw [List.foldl_cons]
    have hC : C ∈ U := hL C (by simp)
    have := pickInv_foldl P chain L (seen ++ [C]) (pickStep P acc C)
      (fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact hs x hx
        · rw [List.mem_singleton.mp hx]; exact hC)
      (fun x hx => hL x (by simp [hx])) (pickInv_step P chain hs hC h)
    simpa [List.append_assoc] using this

/-- **The least element.** If the elements of `L` satisfying `P` form a chain, `pickMin P L` is `none` exactly when
none satisfies `P`, and otherwise their least element. -/
theorem pickMin_spec (P : Nat → Bool) (L : List Nat)
    (chain : ∀ C ∈ L, ∀ D ∈ L, P C = true → P D = true → subset C D = true ∨ subset D C = true) :
    (pickMin P L = none ∧ ∀ C ∈ L, P C = false) ∨
      (∃ M, pickMin P L = some M ∧ M ∈ L ∧ P M = true ∧ ∀ C ∈ L, P C = true → subset M C = true) := by
  have := pickInv_foldl P chain L [] none (by simp) (fun x hx => hx) (Or.inl ⟨rfl, by simp⟩)
  simpa [PickInv, pickMin] using this

theorem pickMin_eq_some {P : Nat → Bool} {L : List Nat}
    (chain : ∀ C ∈ L, ∀ D ∈ L, P C = true → P D = true → subset C D = true ∨ subset D C = true)
    {M : Nat} (hM : M ∈ L) (hPM : P M = true) (hmin : ∀ C ∈ L, P C = true → subset M C = true) :
    pickMin P L = some M := by
  rcases pickMin_spec P L chain with ⟨_, hnone⟩ | ⟨M', hM', hM'L, hPM', hmin'⟩
  · rw [hnone M hM] at hPM; exact absurd hPM (by simp)
  · rw [hM', subset_antisymm (hmin' M hM hPM) (hmin M' hM'L hPM')]

theorem pickMin_eq_none {P : Nat → Bool} {L : List Nat}
    (chain : ∀ C ∈ L, ∀ D ∈ L, P C = true → P D = true → subset C D = true ∨ subset D C = true)
    (h : ∀ C ∈ L, P C = false) : pickMin P L = none := by
  rcases pickMin_spec P L chain with ⟨h1, _⟩ | ⟨M, _, hML, hPM, _⟩
  · exact h1
  · rw [h M hML] at hPM; exact absurd hPM (by simp)

theorem pickMin_congr {P : Nat → Bool} {L L' : List Nat} (hLL : ∀ C, C ∈ L ↔ C ∈ L')
    (chain : ∀ C ∈ L, ∀ D ∈ L, P C = true → P D = true → subset C D = true ∨ subset D C = true) :
    pickMin P L = pickMin P L' := by
  have chain' : ∀ C ∈ L', ∀ D ∈ L', P C = true → P D = true → subset C D = true ∨ subset D C = true :=
    fun C hC D hD => chain C ((hLL C).2 hC) D ((hLL D).2 hD)
  rcases pickMin_spec P L chain with ⟨h1, hnone⟩ | ⟨M, hM, hML, hPM, hmin⟩
  · rw [h1, pickMin_eq_none chain' fun C hC => hnone C ((hLL C).2 hC)]
  · rw [hM, pickMin_eq_some chain' ((hLL M).1 hML) hPM fun C hC hPC => hmin C ((hLL C).2 hC) hPC]

/-! ## Equivalent trees -/

theorem equiv_symm {T T' : TS} (h : T.Equiv T') : T'.Equiv T := ⟨h.1.symm, h.2.symm⟩

theorem equiv_trans {T T' T'' : TS} (h : T.Equiv T') (h' : T'.Equiv T'') : T.Equiv T'' :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

theorem mem_of_equiv {T T' : TS} (h : T.Equiv T') (D : Nat) : D ∈ T.nodes ↔ D ∈ T'.nodes := by
  rw [← List.mem_toFinset, h.1, List.mem_toFinset]

/-! ## Leaves -/

theorem twoLeaves_iff (T : TS) (C : Nat) :
    twoLeaves T C = true ↔ ∃ p q, p < 7 ∧ q < 7 ∧ mem p C = true ∧ mem q C = true ∧ T.lrep p ≠ T.lrep q := by
  unfold twoLeaves
  simp only [List.any_eq_true, mem_toList, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨p, ⟨hp, hpC⟩, q, ⟨hq, hqC⟩, hne⟩
    exact ⟨p, q, hp, hq, hpC, hqC, hne⟩
  · rintro ⟨p, q, hp, hq, hpC, hqC, hne⟩
    exact ⟨p, ⟨hp, hpC⟩, q, ⟨hq, hqC⟩, hne⟩

theorem lrep_congr {T T' : TS} (h : T.leafO = T'.leafO) (p : Nat) : T.lrep p = T'.lrep p := by
  unfold TS.lrep; rw [h]

theorem twoLeaves_congr {T T' : TS} (h : T.leafO = T'.leafO) (C : Nat) : twoLeaves T C = twoLeaves T' C := by
  unfold twoLeaves
  simp only [lrep_congr h]

theorem twoLeaves_mono {T : TS} {C D : Nat} (hCD : subset C D = true) (h : twoLeaves T C = true) :
    twoLeaves T D = true := by
  rw [twoLeaves_iff] at h ⊢
  obtain ⟨p, q, hp, hq, hpC, hqC, hne⟩ := h
  exact ⟨p, q, hp, hq, mem_of_subset hCD hpC, mem_of_subset hCD hqC, hne⟩

theorem exists_mem_of_twoLeaves {T : TS} {C : Nat} (h : twoLeaves T C = true) : ∃ p, mem p C = true := by
  rw [twoLeaves_iff] at h
  obtain ⟨p, _, _, _, hpC, _⟩ := h
  exact ⟨p, hpC⟩

/-- `lrep` of a point: the body on the leaf of `O` goes to `O`. -/
theorem lrep_eq (T : TS) (p : Nat) : T.lrep p = if T.leafO = some p then O else p := by
  unfold TS.lrep
  cases h : T.leafO with
  | none => simp
  | some k =>
    by_cases hk : p = k
    · subst hk; simp
    · simp [hk, Ne.symm hk]

/-! ## Well-formed trees -/

theorem _root_.L6.F2S.WF.laminar {T : TS} {S : Nat} (hT : WF T S) {C D : Nat} (hC : C ∈ T.nodes) (hD : D ∈ T.nodes) :
    subset C D = true ∨ subset D C = true ∨ ∀ p, ¬ (mem p C = true ∧ mem p D = true) := by
  rcases hT.lam C hC D hD with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (disjoint_iff.1 h))

/-- Nodes sharing a point are nested. -/
theorem _root_.L6.F2S.WF.nested {T : TS} {S : Nat} (hT : WF T S) {C D p : Nat} (hC : C ∈ T.nodes) (hD : D ∈ T.nodes)
    (hpC : mem p C = true) (hpD : mem p D = true) : subset C D = true ∨ subset D C = true := by
  rcases hT.laminar hC hD with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd ⟨hpC, hpD⟩ (h p)

theorem _root_.L6.F2S.WF.lt128 {T : TS} {S : Nat} (hT : WF T S) {C : Nat} (hC : C ∈ T.nodes) : C < 128 :=
  lt_of_le_of_lt (subset_le (hT.sub C hC)) hT.S_lt

/-- The chain condition for "contains the set `D`", for a nonempty `D`. -/
theorem _root_.L6.F2S.WF.chain_cover {T : TS} {S : Nat} (hT : WF T S) {D p : Nat} (hp : mem p D = true) :
    ∀ C ∈ T.nodes, ∀ E ∈ T.nodes, subset D C = true → subset D E = true →
      subset C E = true ∨ subset E C = true :=
  fun _ hC _ hE hDC hDE => hT.nested hC hE (mem_of_subset hDC hp) (mem_of_subset hDE hp)

theorem _root_.L6.F2S.WF.chain_lca {T : TS} {S : Nat} (hT : WF T S) (p q : Nat) :
    ∀ C ∈ T.nodes, ∀ E ∈ T.nodes, (mem p C && mem q C) = true → (mem p E && mem q E) = true →
      subset C E = true ∨ subset E C = true := by
  intro C hC E hE h1 h2
  simp only [Bool.and_eq_true] at h1 h2
  exact hT.nested hC hE h1.1 h2.1

theorem _root_.L6.F2S.WF.chain_parent {T : TS} {S : Nat} (hT : WF T S) {c p : Nat} (hp : mem p c = true) :
    ∀ C ∈ T.nodes, ∀ E ∈ T.nodes, ssubset c C = true → ssubset c E = true →
      subset C E = true ∨ subset E C = true := by
  intro C hC E hE h1 h2
  rw [ssubset_iff] at h1 h2
  exact hT.nested hC hE (mem_of_subset h1.1 hp) (mem_of_subset h2.1 hp)

/-! ## Restriction -/

theorem restrict_leafO (T : TS) (S : Nat) : (restrict T S).leafO = restrictLeafO T.leafO S := rfl

theorem mem_restrict {T : TS} {S D : Nat} :
    D ∈ (restrict T S).nodes ↔
      ∃ C ∈ T.nodes, D = C &&& S ∧ twoLeaves (⟨[], restrictLeafO T.leafO S⟩ : TS) D = true := by
  show D ∈ ((T.nodes.map (· &&& S)).filter fun D => twoLeaves ⟨[], restrictLeafO T.leafO S⟩ D).dedup ↔ _
  rw [List.mem_dedup, List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨⟨C, hC, rfl⟩, h2⟩
    exact ⟨C, hC, rfl, h2⟩
  · rintro ⟨C, hC, rfl, h2⟩
    exact ⟨⟨C, hC, rfl⟩, h2⟩

theorem mem_restrict' {T : TS} {S D : Nat} :
    D ∈ (restrict T S).nodes ↔ ∃ C ∈ T.nodes, D = C &&& S ∧ twoLeaves (restrict T S) D = true := by
  rw [mem_restrict]
  simp only [twoLeaves_congr (show (⟨[], restrictLeafO T.leafO S⟩ : TS).leafO = (restrict T S).leafO from rfl)]

theorem and_eq_self {S c : Nat} (h : subset c S = true) : c &&& S = c := by
  unfold subset at h
  exact (beq_iff_eq.mp h)

theorem mem_and_self {S c p : Nat} : mem p (c &&& S) = (mem p c && mem p S) := mem_and p c S

/-- The whole set `all` is a node of a well-formed complete tree. -/
theorem all_mem_nodes {T : TS} (hT : WF T all) : all ∈ T.nodes := by
  apply hT.root
  rw [twoLeaves_iff]
  have hall : ∀ p, p < 7 → mem p all = true := by
    intro p hp; unfold mem all; interval_cases p <;> decide
  by_cases h0 : T.leafO = some 0
  · refine ⟨6, 1, by norm_num, by norm_num, hall 6 (by norm_num), hall 1 (by norm_num), ?_⟩
    rw [lrep_eq, lrep_eq, h0]; simp
  · refine ⟨6, 0, by norm_num, by norm_num, hall 6 (by norm_num), hall 0 (by norm_num), ?_⟩
    rw [lrep_eq, lrep_eq, ite_eq_right h0]
    by_cases h6 : T.leafO = some 6
    · rw [ite_eq_left h6]
      have := (hT.leafO 6 h6).1
      omega
    · rw [ite_eq_right h6]; decide

theorem all_and {S : Nat} (hS : S < 128) : all &&& S = S := by
  apply mask_ext
  intro p
  rw [mem_and]
  cases hp : mem p S
  · simp
  · have := lt7_of_mem hS hp
    have hall : mem p all = true := by unfold mem all; interval_cases p <;> decide
    rw [hall]; rfl

/-- **The restriction of a good complete tree is well formed.** -/
theorem restrict_wf_of_good {X : ExpTree} (hX : X.Good) {S : Nat} (hS : S < 128) (hO : mem O S = true) :
    WF (restrict X.T S) S := by
  have hXwf := hX.1
  refine ⟨hS, hO, List.nodup_dedup _, ?_, ?_, ?_, ?_, ?_⟩
  · intro D hD
    obtain ⟨C, _, rfl, _⟩ := mem_restrict'.1 hD
    exact and_subset_right C S
  · intro D hD
    obtain ⟨_, _, _, h2⟩ := mem_restrict'.1 hD
    exact h2
  · intro D hD E hE
    obtain ⟨C, hC, rfl, _⟩ := mem_restrict'.1 hD
    obtain ⟨C', hC', rfl, _⟩ := mem_restrict'.1 hE
    rcases hXwf.laminar hC hC' with h | h | h
    · left
      exact (subset_iff _ _).2 fun p hp => by
        rw [mem_and] at hp ⊢
        simp only [Bool.and_eq_true] at hp ⊢
        exact ⟨mem_of_subset h hp.1, hp.2⟩
    · right; left
      exact (subset_iff _ _).2 fun p hp => by
        rw [mem_and] at hp ⊢
        simp only [Bool.and_eq_true] at hp ⊢
        exact ⟨mem_of_subset h hp.1, hp.2⟩
    · right; right
      apply disjoint_iff.2
      intro p ⟨h1, h2⟩
      rw [mem_and] at h1 h2
      simp only [Bool.and_eq_true] at h1 h2
      exact h p ⟨h1.1, h2.1⟩
  · intro h2
    apply mem_restrict'.2
    exact ⟨all, all_mem_nodes hXwf, (all_and hS).symm, h2⟩
  · intro k hk
    rw [restrict_leafO] at hk
    unfold restrictLeafO at hk
    cases hlo : X.T.leafO with
    | none => rw [hlo] at hk; exact absurd hk (by simp)
    | some k' =>
      rw [hlo] at hk
      change (if mem k' S = true then some k' else none) = some k at hk
      split_ifs at hk with hkS
      · cases hk
        obtain ⟨hk6, _, hkC⟩ := hXwf.leafO k hlo
        refine ⟨hk6, hkS, fun D hD => ?_⟩
        obtain ⟨C, hC, rfl, _⟩ := mem_restrict'.1 hD
        rw [mem_and, mem_and, hO, hkS, hkC C hC]

theorem restrictLeafO_eq_some {lo : Option Nat} {S k : Nat} :
    restrictLeafO lo S = some k ↔ lo = some k ∧ mem k S = true := by
  unfold restrictLeafO
  cases lo with
  | none => simp
  | some k' =>
    by_cases h : mem k' S = true
    · simp only [h, ite_true, Option.some.injEq]
      exact ⟨fun e => ⟨e, e ▸ h⟩, fun e => e.1⟩
    · have h' : mem k' S = false := by simpa using h
      simp only [h', Bool.false_eq_true, ite_false, reduceCtorEq, false_iff, not_and, Option.some.injEq]
      rintro rfl; rw [h']; simp

/-- The representative of a point of `S₁` is the same for the leaf of `O` restricted to `S₁` or to `S₂ ⊇ S₁`. -/
theorem lrep_restrict_eq {T : TS} {S1 S2 r : Nat} (h12 : subset S1 S2 = true) (hr : mem r S1 = true) :
    (⟨[], restrictLeafO T.leafO S1⟩ : TS).lrep r = (⟨[], restrictLeafO T.leafO S2⟩ : TS).lrep r := by
  rw [lrep_eq, lrep_eq]
  have e : restrictLeafO T.leafO S1 = some r ↔ restrictLeafO T.leafO S2 = some r := by
    rw [restrictLeafO_eq_some, restrictLeafO_eq_some]
    exact ⟨fun h => ⟨h.1, mem_of_subset h12 hr⟩, fun h => ⟨h.1, hr⟩⟩
  by_cases h : restrictLeafO T.leafO S1 = some r
  · simp [h, e.1 h]
  · have h' : ¬ restrictLeafO T.leafO S2 = some r := fun h' => h (e.2 h')
    simp [h, h']

/-- **The restriction of a restriction** (for `S₁ ⊆ S₂`). -/
theorem restrict_restrict {T : TS} {S1 S2 : Nat} (h12 : subset S1 S2 = true) :
    (restrict (restrict T S2) S1).Equiv (restrict T S1) := by
  have hlo : restrictLeafO (restrictLeafO T.leafO S2) S1 = restrictLeafO T.leafO S1 := by
    unfold restrictLeafO
    cases T.leafO with
    | none => rfl
    | some k =>
      by_cases h1 : mem k S1 = true
      · simp [h1, mem_of_subset h12 h1]
      · by_cases h2 : mem k S2 = true
        · simp [h1, h2]
        · simp [h1, h2]
  refine ⟨?_, by rw [restrict_leafO, restrict_leafO, restrict_leafO, hlo]⟩
  ext D
  rw [List.mem_toFinset, List.mem_toFinset, mem_restrict, mem_restrict]
  rw [restrict_leafO, hlo]
  constructor
  · rintro ⟨E, hE, rfl, h2⟩
    obtain ⟨C, hC, rfl, _⟩ := mem_restrict.1 hE
    refine ⟨C, hC, ?_, h2⟩
    apply mask_ext; intro p
    simp only [mem_and]
    cases h1 : mem p S1
    · simp
    · rw [mem_of_subset h12 h1]; simp
  · rintro ⟨C, hC, rfl, h2⟩
    refine ⟨C &&& S2, ?_, ?_, h2⟩
    · apply mem_restrict.2
      refine ⟨C, hC, rfl, ?_⟩
      -- two leaves of `C ∩ S₁` (w.r.t. the restriction to `S₁`) are two leaves of `C ∩ S₂`
      rw [twoLeaves_iff] at h2 ⊢
      obtain ⟨p, q, hp, hq, hpC, hqC, hne⟩ := h2
      rw [mem_and] at hpC hqC
      simp only [Bool.and_eq_true] at hpC hqC
      refine ⟨p, q, hp, hq, ?_, ?_, ?_⟩
      · rw [mem_and, hpC.1, mem_of_subset h12 hpC.2]; rfl
      · rw [mem_and, hqC.1, mem_of_subset h12 hqC.2]; rfl
      · rwa [← lrep_restrict_eq (T := T) h12 hpC.2, ← lrep_restrict_eq (T := T) h12 hqC.2]
    · apply mask_ext; intro p
      simp only [mem_and]
      cases h1 : mem p S1
      · simp
      · rw [mem_of_subset h12 h1]; simp

end L6.F2S.TreeAux
