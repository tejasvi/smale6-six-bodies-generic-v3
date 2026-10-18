import Lean6.Special.D88.Count.Bridge
import Lean6.Special.D88.Count.Dim

/-!
# Soundness of the dimension check

**`dimCheck_sound`**: if `dimCheck p n B N = true` (`p` prime) and every `toMv n p g`, `g ∈ B`, lies in an ideal `I`
of `(ZMod p)[x₀, …, x_{n-1}]`, then the quotient by `I` is finite-dimensional of dimension at most `N`. The checked
polynomials are nonzero with leading monomials their first terms (`lead_toMv`), the staircase `S` contains `0` and is
closed under the border of these leading monomials, and `finrank_le_of_border` concludes.
-/

namespace Lean6.Special.D88.Count

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.Count MvPolynomial Finsupp
open scoped MonomialOrder

variable {n p : ℕ}

theorem addVar_length : ∀ (s : Mono) (i : ℕ), (addVar s i).length = s.length
  | [], _ => rfl
  | a :: s, 0 => rfl
  | a :: s, i + 1 => by simp [addVar, addVar_length s i]

theorem addVar_getD : ∀ (s : Mono) (i j : ℕ), i < s.length →
    (addVar s i).getD j 0 = s.getD j 0 + if j = i then 1 else 0
  | [], _, _, h => by simp at h
  | a :: s, 0, 0, _ => by simp [addVar]
  | a :: s, 0, j + 1, _ => by simp [addVar]
  | a :: s, i + 1, 0, _ => by simp [addVar]
  | a :: s, i + 1, j + 1, h => by
    simp only [addVar, List.getD_cons_succ]
    rw [addVar_getD s i j (by simpa using h)]
    simp

theorem vec_addVar {s : Mono} (hs : s.length = n) (i : Fin n) :
    vec n (addVar s i) = vec n s + single i 1 := by
  ext j
  rw [vec_apply, Finsupp.add_apply, vec_apply, addVar_getD s i j (by omega), single_apply]
  congr 1
  by_cases hji : j = i
  · subst hji; simp
  · simp [Fin.val_ne_of_ne hji, Ne.symm hji]

theorem mdvdS_spec : ∀ {l m : Mono}, mdvdS l m = true → ∀ j, l.getD j 0 ≤ m.getD j 0
  | [], [], _, j => by simp
  | a :: l, b :: m, h, j => by
    simp only [mdvdS, Bool.and_eq_true, decide_eq_true_eq] at h
    cases j with
    | zero => simpa using h.1
    | succ j => simpa using mdvdS_spec h.2 j
  | [], _ :: _, h, _ => by simp [mdvdS] at h
  | _ :: _, [], h, _ => by simp [mdvdS] at h

theorem vec_le_of_mdvdS {l m : Mono} (h : mdvdS l m = true) : vec n l ≤ vec n m := by
  intro j
  simpa using mdvdS_spec h j

theorem mdvdS_nil_left {m : Mono} (h : mdvdS [] m = true) : m = [] := by
  cases m with
  | nil => rfl
  | cons b m => simp [mdvdS] at h

theorem vec_zeroMono : vec n (zeroMono n) = 0 := by
  ext j
  simp [vec_apply, zeroMono]

theorem mem_of_hs_contains {S : List Mono} {x : Mono} (h : (Std.HashSet.ofList S).contains x = true) : x ∈ S := by
  rw [Std.HashSet.contains_ofList] at h
  exact List.contains_iff_mem.mp h

/-- **The dimension check is sound.** -/
theorem dimCheck_sound (p n : ℕ) [Fact p.Prime] (B : List (Poly ℕ)) (N : ℕ) (h : dimCheck p n B N = true)
    (I : Ideal (MvPolynomial (Fin n) (ZMod p))) (hB : ∀ g ∈ B, toMv n p g ∈ I) :
    Module.Finite (ZMod p) (MvPolynomial (Fin n) (ZMod p) ⧸ I) ∧
      Module.finrank (ZMod p) (MvPolynomial (Fin n) (ZMod p) ⧸ I) ≤ N := by
  classical
  unfold dimCheck at h
  set L : Array Mono := (B.map leadOf).toArray with hL
  set r := staircase n L N (N + 2) with hr
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨hpoly, ⟨⟨⟨hz, hlen⟩, hcard⟩, hbord⟩⟩ := h
  -- the polynomials and their leading monomials
  set G : Set (MvPolynomial (Fin n) (ZMod p)) := {q | ∃ g ∈ B, toMv n p g = q} with hG
  have hGI : G ⊆ I := by
    rintro q ⟨g, hg, rfl⟩
    exact hB g hg
  have hG0 : ∀ q ∈ G, q ≠ 0 := by
    rintro q ⟨g, hg, rfl⟩
    exact (lead_toMv (hpoly g hg)).2
  -- the staircase as a finite set of exponents
  set S : Finset (Fin n →₀ ℕ) := (r.1.map (vec n)).toFinset with hS
  have h0 : (0 : Fin n →₀ ℕ) ∈ S := by
    rw [hS, List.mem_toFinset, List.mem_map]
    exact ⟨zeroMono n, mem_of_hs_contains hz, vec_zeroMono⟩
  have hb : ∀ s ∈ S, ∀ i, s + single i 1 ∈ S ∨
      ∃ g ∈ G, (degRevLex (Fin n)).degree g ≤ s + single i 1 := by
    intro s hs i
    rw [hS, List.mem_toFinset, List.mem_map] at hs
    obtain ⟨sl, hsl, rfl⟩ := hs
    have hsln : sl.length = n := hlen sl hsl
    have hbi := hbord sl hsl i.1 (List.mem_range.mpr i.2)
    rw [← vec_addVar hsln i]
    unfold borderAt at hbi
    simp only [Bool.or_eq_true] at hbi
    rcases hbi with hin | hwit
    · left
      rw [hS, List.mem_toFinset, List.mem_map]
      exact ⟨addVar sl i, mem_of_hs_contains hin, rfl⟩
    · right
      split at hwit
      · rename_i w _
        by_cases hw : w < L.size
        · have hwB : w < B.length := by simpa [hL] using hw
          have hLw : L.getD w [] = leadOf (B[w]'hwB) := by
            simp [hL, Array.getD, hwB]
          rw [hLw] at hwit
          refine ⟨toMv n p (B[w]'hwB), ⟨_, List.getElem_mem _, rfl⟩, ?_⟩
          rw [(lead_toMv (hpoly _ (List.getElem_mem _))).1]
          exact vec_le_of_mdvdS hwit
        · have hLw : L.getD w [] = [] := by simp [Array.getD, hw]
          rw [hLw] at hwit
          have := mdvdS_nil_left hwit
          have hl := addVar_length sl i
          rw [this, hsln] at hl
          exact absurd i.2 (by simp at hl; omega)
      · exact absurd hwit (by simp)
  have hScard : S.card ≤ N := by
    refine (List.toFinset_card_le _).trans ?_
    rw [List.length_map]
    exact hcard
  obtain ⟨hfin, hrank⟩ := finrank_le_of_border (degRevLex (Fin n)) I G hGI hG0 S h0 hb
  exact ⟨hfin, hrank.trans hScard⟩

end Lean6.Special.D88.Count
