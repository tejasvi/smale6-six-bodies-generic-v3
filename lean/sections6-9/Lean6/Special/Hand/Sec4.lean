import Mathlib

/-!
# Computations inside the hand proofs of Section 4

* `root_coefficient` (Lemma 4.3(b)): the coefficient of exponent `h_r` in `Σ_k m_k z_k = 0`, summed over the bodies that
  do not lie below the `O`-child `c_O` of the root, regrouped by the children: `Σ_k m_k (X_{c(k)} − X_{c_O}) =
  Σ_c (X_c − X_{c_O}) M_c` with `M_c` the sum of the masses below `c`.
* `root_two_children`, `root_two_children_ne_zero`: if the root had only the children `c_O` and `c`, the coefficient
  would be `(X_c − X_{c_O}) M_c`, which is not zero for positive masses, a body below `c` and `X_c ≠ X_{c_O}`.
-/

namespace Lean6.Special.Hand

open Finset

variable {ι C R : Type*} [DecidableEq C] [CommRing R]

/-- **Lemma 4.3(b)**: regrouping by the children of the root. -/
theorem root_coefficient (S : Finset ι) (m : ι → R) (ch : ι → C) (X : C → R) (c0 : C) :
    ∑ k ∈ S.filter (fun k => ch k ≠ c0), m k * (X (ch k) - X c0) =
      ∑ c ∈ (S.filter (fun k => ch k ≠ c0)).image ch, (X c - X c0) * ∑ k ∈ S.filter (fun k => ch k = c), m k := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := ch) (t := (S.filter (fun k => ch k ≠ c0)).image ch)
    (fun k hk => Finset.mem_image_of_mem ch hk)]
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨k0, hk0, rfl⟩ := Finset.mem_image.mp hc
  have hne : ch k0 ≠ c0 := (Finset.mem_filter.mp hk0).2
  have hS : (S.filter (fun k => ch k ≠ c0)).filter (fun k => ch k = ch k0) = S.filter (fun k => ch k = ch k0) := by
    ext k
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hk, _⟩, he⟩
      exact ⟨hk, he⟩
    · rintro ⟨hk, he⟩
      exact ⟨⟨hk, he ▸ hne⟩, he⟩
  rw [hS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [(Finset.mem_filter.mp hk).2]
  ring

/-- **Lemma 4.3(b)**, two children: if every body of `S` lies below `c_O` or below `c`, the coefficient is
`(X_c − X_{c_O}) M_c`. -/
theorem root_two_children (S : Finset ι) (m : ι → R) (ch : ι → C) (X : C → R) (c0 c : C)
    (h2 : ∀ k ∈ S, ch k = c0 ∨ ch k = c) :
    ∑ k ∈ S.filter (fun k => ch k ≠ c0), m k * (X (ch k) - X c0) =
      (X c - X c0) * ∑ k ∈ S.filter (fun k => ch k = c), m k := by
  by_cases hc : c = c0
  · subst hc
    have : S.filter (fun k => ch k ≠ c) = ∅ := by
      ext k
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_not]
      intro hk
      rcases h2 k hk with h | h <;> exact h
    rw [this, Finset.sum_empty, sub_self, zero_mul]
  · have hS : S.filter (fun k => ch k ≠ c0) = S.filter (fun k => ch k = c) := by
      ext k
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hk, hne⟩
        exact ⟨hk, (h2 k hk).resolve_left hne⟩
      · rintro ⟨hk, he⟩
        exact ⟨hk, he ▸ hc⟩
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [(Finset.mem_filter.mp hk).2]
    ring

/-- With positive masses and a body below `c`, the coefficient `(X_c − X_{c_O}) M_c` is not zero. -/
theorem root_two_children_ne_zero (S : Finset ι) (m : ι → ℝ) (hm : ∀ k, 0 < m k) (ch : ι → C) (X : C → ℂ) (c0 c : C)
    (hX : X c ≠ X c0) (hne : (S.filter (fun k => ch k = c)).Nonempty) :
    (X c - X c0) * ∑ k ∈ S.filter (fun k => ch k = c), (m k : ℂ) ≠ 0 := by
  refine mul_ne_zero (sub_ne_zero.mpr hX) ?_
  have hpos : (0 : ℝ) < ∑ k ∈ S.filter (fun k => ch k = c), m k := Finset.sum_pos (fun k _ => hm k) hne
  have h' : ((∑ k ∈ S.filter (fun k => ch k = c), m k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  push_cast at h'
  exact h'

end Lean6.Special.Hand
