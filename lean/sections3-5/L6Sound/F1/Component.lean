import L6Sound.F1.Basic

/-!
# The components of rule (C3) are the connected components

`mem_component_iff`: for a body `k < n`, the list `component n s k` used in (C3) contains exactly the bodies joined to
`k` by a walk of strokes on the bodies `0, …, n - 1` (the reflexive-transitive closure of the stroke relation). The
growth stops as soon as a round adds nothing, and each round that adds something adds a new body, so `n` rounds
suffice (`grow_closed`).
-/

namespace L6F1

/-- The relation "`ab` is a stroke" on the bodies `< n`. -/
def strokeRel (n : ℕ) (s : ℕ → ℕ → Bool) (a b : ℕ) : Prop := a < n ∧ b < n ∧ s a b = true

/-- A list of bodies closed under the strokes. -/
def StrokeClosed (n : ℕ) (s : ℕ → ℕ → Bool) (S : List ℕ) : Prop := ∀ i ∈ S, ∀ j < n, s i j = true → j ∈ S

theorem length_le_of_nodup_lt {S : List ℕ} {n : ℕ} (hnd : S.Nodup) (hlt : ∀ x ∈ S, x < n) : S.length ≤ n := by
  have h1 : S.toFinset ⊆ Finset.range n := fun x hx => Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx))
  have h2 := Finset.card_le_card h1
  rwa [List.toFinset_card_of_nodup hnd, Finset.card_range] at h2

theorem mem_newBodies {n : ℕ} {s : ℕ → ℕ → Bool} {S : List ℕ} {j : ℕ} :
    j ∈ (List.range n).filter (fun j => !S.contains j && S.any fun i => s i j) ↔
      j < n ∧ j ∉ S ∧ ∃ i ∈ S, s i j = true := by
  simp [List.mem_filter, List.mem_range, List.any_eq_true]

theorem subset_grow {n : ℕ} {s : ℕ → ℕ → Bool} : ∀ (r : ℕ) (S : List ℕ), S ⊆ grow n s r S
  | 0, S => by simp [grow]
  | r + 1, S => by
    simp only [grow]
    split_ifs
    · exact List.Subset.refl S
    · intro x hx
      exact subset_grow r _ (List.mem_append_left _ hx)

/-- The bodies found by the growth are reached by walks of strokes. -/
theorem reach_of_mem_grow {n : ℕ} {s : ℕ → ℕ → Bool} {k : ℕ} :
    ∀ (r : ℕ) (S : List ℕ), (∀ x ∈ S, x < n ∧ Relation.ReflTransGen (strokeRel n s) k x) →
      ∀ x ∈ grow n s r S, x < n ∧ Relation.ReflTransGen (strokeRel n s) k x
  | 0, S, hS => by simpa [grow] using hS
  | r + 1, S, hS => by
    simp only [grow]
    split_ifs with hN
    · exact hS
    · apply reach_of_mem_grow r
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hS x hx
      · obtain ⟨hxn, -, i, hi, his⟩ := mem_newBodies.mp hx
        obtain ⟨hin, hki⟩ := hS i hi
        exact ⟨hxn, hki.tail ⟨hin, hxn, his⟩⟩

/-- After enough rounds the growth is closed under the strokes. -/
theorem grow_closed {n : ℕ} {s : ℕ → ℕ → Bool} :
    ∀ (r : ℕ) (S : List ℕ), S.Nodup → (∀ x ∈ S, x < n) → n + 1 ≤ S.length + r → StrokeClosed n s (grow n s r S)
  | 0, S, hnd, hlt, hlen => by
    have := length_le_of_nodup_lt hnd hlt
    omega
  | r + 1, S, hnd, hlt, hlen => by
    simp only [grow]
    split_ifs with hN
    · intro i hi j hj hs
      by_contra hjS
      have hmem : j ∈ (List.range n).filter (fun j => !S.contains j && S.any fun i => s i j) :=
        mem_newBodies.mpr ⟨hj, hjS, i, hi, hs⟩
      rw [List.isEmpty_iff] at hN
      rw [hN] at hmem
      exact List.not_mem_nil hmem
    · apply grow_closed r
      · refine List.Nodup.append hnd (List.nodup_range.filter _) ?_
        intro x hx hx'
        exact (mem_newBodies.mp hx').2.1 hx
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hlt x hx
        · exact (mem_newBodies.mp hx).1
      · have : 0 < ((List.range n).filter (fun j => !S.contains j && S.any fun i => s i j)).length := by
          cases h : (List.range n).filter (fun j => !S.contains j && S.any fun i => s i j) with
          | nil => rw [h] at hN; exact absurd rfl hN
          | cons a l => simp
        rw [List.length_append]
        omega

/-- **The component of `k` is the set of bodies joined to `k` by a walk of strokes.** -/
theorem mem_component_iff {n : ℕ} {s : ℕ → ℕ → Bool} {k j : ℕ} (hk : k < n) :
    j ∈ component n s k ↔ Relation.ReflTransGen (strokeRel n s) k j := by
  constructor
  · intro h
    exact (reach_of_mem_grow n [k] (by simpa using ⟨hk, Relation.ReflTransGen.refl⟩) j h).2
  · intro h
    have hcl : StrokeClosed n s (component n s k) :=
      grow_closed n [k] (List.nodup_singleton k) (by simp [hk]) (by simp)
    have hk' : k ∈ component n s k := subset_grow n [k] (List.mem_singleton_self k)
    induction h with
    | refl => exact hk'
    | tail _ hbc ih => exact hcl _ ih _ hbc.2.1 hbc.2.2

/-- For the `z`-strokes of an edge code: the `z`-component of `k` in rule (C3) is the set of bodies joined to `k` by
a walk of `z`-strokes (the relation is symmetric, `kind_comm`, so this is the connected component of `k` in the graph
of the `z`-strokes). -/
theorem mem_zComponent_iff {n e k j : ℕ} (hk : k < n) :
    j ∈ component n (zStroke e) k ↔ Relation.ReflTransGen (strokeRel n (zStroke e)) k j :=
  mem_component_iff hk

theorem zStroke_comm (e a b : ℕ) : zStroke e a b = zStroke e b a := by simp [zStroke, kind_comm e a b]

theorem wStroke_comm (e a b : ℕ) : wStroke e a b = wStroke e b a := by simp [wStroke, kind_comm e a b]

end L6F1
