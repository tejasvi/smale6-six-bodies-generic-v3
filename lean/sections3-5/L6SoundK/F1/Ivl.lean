import L6K.F1.Ivl
import L6SoundK.F1.SortR
import L6Sound.F1.Basic

/-!
# Comparison by intervals gives the global comparison

`nodup_perm_of_ivls`: if the intervals cover the natural numbers and `ivlCheck C R` holds on each of them, then `C`
has no repetition and is a permutation of `R` (counts agree on every interval).
-/

namespace L6K.F1

theorem chainOK_cover : ∀ (L : List (ℕ × ℕ)) (lo : ℕ), chainOK lo L = true →
    ∀ c, lo ≤ c → ∃ lh ∈ L, inIvl lh.1 lh.2 c = true
  | [], _, h, _, _ => by simp [chainOK] at h
  | [(a, b)], lo, h, c, hc => by
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨(a, b), List.mem_singleton_self _, ?_⟩
    simp [inIvl, h.1, h.2, hc]
  | (a, b) :: (a', b') :: rest, lo, h, c, hc => by
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hab⟩, hr⟩ := h
    by_cases hcb : c < b
    · refine ⟨(a, b), List.mem_cons_self, ?_⟩
      have hb : b ≠ 0 := by omega
      simp [inIvl, hc, hcb, hb]
    · obtain ⟨lh, hm, hin⟩ := chainOK_cover ((a', b') :: rest) b hr c (by omega)
      exact ⟨lh, List.mem_cons_of_mem _ hm, hin⟩

theorem ivlCheck_spec {C R : List ℕ} {lo hi : ℕ} (h : ivlCheck C R lo hi = true) :
    (C.filter (inIvl lo hi)).Nodup ∧ (C.filter (inIvl lo hi)).Perm (R.filter (inIvl lo hi)) := by
  unfold ivlCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨(msortR_perm 20 _).nodup_iff.mp (L6F1.nodup_of_strictSorted h1), ?_⟩
  refine (msortR_perm 20 _).symm.trans ?_
  rw [h2]
  exact msortR_perm 20 _

/-- **The intervals give the global comparison.** -/
theorem nodup_perm_of_ivls {C R : List ℕ} {L : List (ℕ × ℕ)} (hc : chainOK 0 L = true)
    (h : L.all (fun lh => ivlCheck C R lh.1 lh.2) = true) : C.Nodup ∧ C.Perm R := by
  have hspec : ∀ lh ∈ L, (C.filter (inIvl lh.1 lh.2)).Nodup ∧
      (C.filter (inIvl lh.1 lh.2)).Perm (R.filter (inIvl lh.1 lh.2)) :=
    fun lh hm => ivlCheck_spec (List.all_eq_true.mp h lh hm)
  refine ⟨List.nodup_iff_count_le_one.mpr fun c => ?_, List.perm_iff_count.mpr fun c => ?_⟩
  · obtain ⟨lh, hm, hin⟩ := chainOK_cover L 0 hc c (Nat.zero_le c)
    have := List.nodup_iff_count_le_one.mp (hspec lh hm).1 c
    rwa [List.count_filter hin] at this
  · obtain ⟨lh, hm, hin⟩ := chainOK_cover L 0 hc c (Nat.zero_le c)
    have := (hspec lh hm).2.count_eq c
    rwa [List.count_filter hin, List.count_filter hin] at this

end L6K.F1
