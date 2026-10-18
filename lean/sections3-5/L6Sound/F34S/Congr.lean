import L6Sound.F34S.Defs
import L6Sound.F2S.TreeAux3

/-!
# The values of the initial forms depend only on the nodes of the trees as a set

For a well-formed tree, the lowest common ancestor (`TS.lca`, the least node containing two points) and the child of
a node containing a point (`childOf`, the largest node strictly inside it containing the point, or its leaf class)
do not depend on the order of the nodes; so neither do `lcVal`, `termVal2` and `itemVal` (`itemVal_congr`).
-/

namespace L6.F34S

open L6.F2S L6.F2S.TreeAux

/-! ## The largest element -/

/-- The invariant of the fold of `pickMax`. -/
def PickMaxInv (P : Nat → Bool) (seen : List Nat) (acc : Option Nat) : Prop :=
  (acc = none ∧ ∀ C ∈ seen, P C = false) ∨
    (∃ M, acc = some M ∧ M ∈ seen ∧ P M = true ∧ ∀ C ∈ seen, P C = true → subset C M = true)

theorem pickMaxInv_step (P : Nat → Bool) {U : List Nat}
    (chain : ∀ C ∈ U, ∀ D ∈ U, P C = true → P D = true → subset C D = true ∨ subset D C = true)
    {seen : List Nat} {acc : Option Nat} {C : Nat} (hseen : ∀ x ∈ seen, x ∈ U) (hC : C ∈ U)
    (h : PickMaxInv P seen acc) : PickMaxInv P (seen ++ [C]) (pickMaxStep P acc C) := by
  unfold pickMaxStep
  by_cases hPC : P C = true
  · rw [ite_eq_left hPC]
    rcases h with ⟨hacc, hnone⟩ | ⟨M, hacc, hM, hPM, hmax⟩
    · subst hacc
      refine Or.inr ⟨C, rfl, by simp, hPC, fun x hx hPx => ?_⟩
      rcases List.mem_append.mp hx with hx | hx
      · rw [hnone x hx] at hPx; exact absurd hPx (by simp)
      · rw [List.mem_singleton.mp hx]; exact subset_refl C
    · subst hacc
      show PickMaxInv P (seen ++ [C]) (if subset M C = true then some C else some M)
      split_ifs with hMC
      · refine Or.inr ⟨C, rfl, by simp, hPC, fun x hx hPx => ?_⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact subset_trans (hmax x hx hPx) hMC
        · rw [List.mem_singleton.mp hx]; exact subset_refl C
      · refine Or.inr ⟨M, rfl, List.mem_append_left _ hM, hPM, fun x hx hPx => ?_⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact hmax x hx hPx
        · rw [List.mem_singleton.mp hx]
          rcases chain C hC M (hseen M hM) hPC hPM with h1 | h1
          · exact h1
          · exact absurd h1 hMC
  · rw [ite_eq_right hPC]
    have hPC' : P C = false := by simpa using hPC
    rcases h with ⟨hacc, hnone⟩ | ⟨M, hacc, hM, hPM, hmax⟩
    · refine Or.inl ⟨hacc, fun x hx => ?_⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact hnone x hx
      · rw [List.mem_singleton.mp hx]; exact hPC'
    · refine Or.inr ⟨M, hacc, List.mem_append_left _ hM, hPM, fun x hx hPx => ?_⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact hmax x hx hPx
      · rw [List.mem_singleton.mp hx] at hPx; rw [hPC'] at hPx; exact absurd hPx (by simp)

theorem pickMaxInv_foldl (P : Nat → Bool) {U : List Nat}
    (chain : ∀ C ∈ U, ∀ D ∈ U, P C = true → P D = true → subset C D = true ∨ subset D C = true) :
    ∀ (L seen : List Nat) (acc : Option Nat), (∀ x ∈ seen, x ∈ U) → (∀ x ∈ L, x ∈ U) →
      PickMaxInv P seen acc → PickMaxInv P (seen ++ L) (L.foldl (pickMaxStep P) acc)
  | [], seen, acc, _, _, h => by simpa using h
  | C :: L, seen, acc, hs, hL, h => by
    rw [List.foldl_cons]
    have hC : C ∈ U := hL C (by simp)
    have := pickMaxInv_foldl P chain L (seen ++ [C]) (pickMaxStep P acc C)
      (fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact hs x hx
        · rw [List.mem_singleton.mp hx]; exact hC)
      (fun x hx => hL x (by simp [hx])) (pickMaxInv_step P chain hs hC h)
    simpa [List.append_assoc] using this

theorem pickMax_spec (P : Nat → Bool) (L : List Nat)
    (chain : ∀ C ∈ L, ∀ D ∈ L, P C = true → P D = true → subset C D = true ∨ subset D C = true) :
    (pickMax P L = none ∧ ∀ C ∈ L, P C = false) ∨
      (∃ M, pickMax P L = some M ∧ M ∈ L ∧ P M = true ∧ ∀ C ∈ L, P C = true → subset C M = true) := by
  have := pickMaxInv_foldl P chain L [] none (by simp) (fun x hx => hx) (Or.inl ⟨rfl, by simp⟩)
  simpa [PickMaxInv, pickMax] using this

theorem pickMax_congr {P : Nat → Bool} {L L' : List Nat} (hLL : ∀ C, C ∈ L ↔ C ∈ L')
    (chain : ∀ C ∈ L, ∀ D ∈ L, P C = true → P D = true → subset C D = true ∨ subset D C = true) :
    pickMax P L = pickMax P L' := by
  have chain' : ∀ C ∈ L', ∀ D ∈ L', P C = true → P D = true → subset C D = true ∨ subset D C = true :=
    fun C hC D hD => chain C ((hLL C).2 hC) D ((hLL D).2 hD)
  rcases pickMax_spec P L chain with ⟨h1, hnone⟩ | ⟨M, hM, hML, hPM, hmax⟩
  · rcases pickMax_spec P L' chain' with ⟨h2, _⟩ | ⟨M', _, hM'L, hPM', _⟩
    · rw [h1, h2]
    · rw [hnone M' ((hLL M').2 hM'L)] at hPM'; exact absurd hPM' (by simp)
  · rcases pickMax_spec P L' chain' with ⟨_, hnone'⟩ | ⟨M', hM', hM'L, hPM', hmax'⟩
    · rw [hnone' M ((hLL M).1 hML)] at hPM; exact absurd hPM (by simp)
    · rw [hM, hM', subset_antisymm (hmax' M ((hLL M).1 hML) hPM) (hmax M' ((hLL M').2 hM'L) hPM')]

/-! ## Equivalent well-formed trees -/

theorem lca_congr {T T' : TS} {S : Nat} (hT : WF T S) (h : T.Equiv T') (p q : Nat) : T.lca p q = T'.lca p q := by
  rw [lca_eq_pickMin, lca_eq_pickMin]
  exact pickMin_congr (mem_of_equiv h) (hT.chain_lca p q)

theorem leafClass_congr {T T' : TS} (h : T.leafO = T'.leafO) (p : Nat) : T.leafClass p = T'.leafClass p := by
  unfold TS.leafClass
  rw [h]

theorem childOf_congr {T T' : TS} {S : Nat} (hT : WF T S) (h : T.Equiv T') (v p : Nat) :
    childOf T v p = childOf T' v p := by
  unfold childOf
  have hc : ∀ C ∈ T.nodes, ∀ D ∈ T.nodes, (L6.F2S.ssubset C v && L6.F2S.mem p C) = true →
      (L6.F2S.ssubset D v && L6.F2S.mem p D) = true → subset C D = true ∨ subset D C = true := by
    intro C hC D hD h1 h2
    simp only [Bool.and_eq_true] at h1 h2
    exact hT.nested hC hD h1.2 h2.2
  rw [pickMax_congr (mem_of_equiv h) hc, leafClass_congr h.2]

section Values

variable {R : Type*} [CommRing R]

theorem lcVal_congr {T T' : TS} {S : Nat} (hT : WF T S) (h : T.Equiv T') (X : Nat → Nat → R) (pq : Nat × Nat) :
    lcVal T X pq = lcVal T' X pq := by
  unfold lcVal
  rw [lca_congr hT h]
  cases T'.lca pq.1 pq.2 with
  | none => rfl
  | some v => dsimp only; rw [childOf_congr hT h, childOf_congr hT h]

theorem termVal2_congr {Tz Tz' Tw Tw' : TS} {Sz Sw : Nat} (hz : WF Tz Sz) (hz' : Tz.Equiv Tz') (hw : WF Tw Sw)
    (hw' : Tw.Equiv Tw') (X Y P : Nat → Nat → R) (E : R) (m : Nat → R) (t : XTerm) :
    termVal2 Tz Tw X Y P E m t = termVal2 Tz' Tw' X Y P E m t := by
  unfold termVal2
  congr 3
  · exact congrArg List.prod (List.map_congr_left fun pq _ => lcVal_congr hz hz' X pq)
  · exact congrArg List.prod (List.map_congr_left fun pq _ => lcVal_congr hw hw' Y pq)

/-- **The value of an item depends only on the nodes of the trees as a set.** -/
theorem itemVal_congr {Tz Tz' Tw Tw' : TS} {Sz Sw : Nat} (hz : WF Tz Sz) (hz' : Tz.Equiv Tz') (hw : WF Tw Sw)
    (hw' : Tw.Equiv Tw') (X Y P : Nat → Nat → R) (E : R) (m : Nat → R) (it : ItemX) :
    itemVal Tz Tw X Y P E m it = itemVal Tz' Tw' X Y P E m it := by
  cases it with
  | init I S =>
    simp only [itemVal]
    congr 1
    exact congrArg List.sum (List.map_congr_left fun i _ => termVal2_congr hz hz' hw hw' X Y P E m _)
  | dist k l =>
    simp only [itemVal]
    rw [lcVal_congr hz hz' X, lcVal_congr hw hw' Y]

end Values

end L6.F34S
