import L6Check.F1.Main
import L6Common.SHA256

/-!
# The 117 diagrams of Chang and Chen lie in 117 distinct classes

A claim made after Proposition 3.1 (not used in its proof): the 117 six-body diagrams of Chang and Chen satisfy the
rules and lie in 117 distinct classes of the 191 of `n6.json`. The input is `data/f1/chang_chen_117.txt` (converted
from a transcription of their figures by `scripts/f1/cc_convert.py`); `check_cc` reads it back identically and checks
the rules and the distinctness of the canonical keys, and `F1_chang_chen` turns this into an injective map from the 117
diagrams to the classes of `n6.json`, each diagram lying in the orbit of the representative of its class.
-/

namespace L6F1

set_option profiler true in
/-- The checks of the list of Chang and Chen. -/
theorem check_cc : checkCC ccData = true := by native_decide

theorem ccData_sha256 :
    L6.SHA256.sha256Hex ccData = "f01acbf5bc6a9bb876bad078d5484cba15595342a6f10802a8c576a604fdfe86" := by
  native_decide

/-- **The 117 diagrams of Chang and Chen satisfy the rules and lie in 117 distinct classes of `n6.json`.** -/
theorem F1_chang_chen :
    ∃ xs : List CCDiagram, parseCC ccData = some xs ∧ xs.map renderCCLine = ccLines ccData ∧ xs.length = 117 ∧
      (∀ x ∈ xs, ccToDiagram x ∈ allDiagrams 6 ∧ okRules 6 (ccToDiagram x) = true) ∧
      ∃ f : Fin xs.length → Fin classes6.length, Function.Injective f ∧
        ∀ i, ccToDiagram (xs.get i) ∈ orbit 6 (classes6.get (f i)).1 := by
  have h := check_cc
  unfold checkCC at h
  split at h
  · exact absurd h (by simp)
  · rename_i xs hxs
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h5⟩, h6⟩ := h
    have hok : ∀ x ∈ xs, ccToDiagram x ∈ allDiagrams 6 ∧ okRules 6 (ccToDiagram x) = true := by
      intro x hx
      have := h5 x hx
      exact ⟨mem_allDiagrams.mpr this.1, this.2⟩
    refine ⟨xs, hxs, h1, h2, hok, ?_⟩
    obtain ⟨-, -, -, -, -, hu, -⟩ := F1_main
    have hex : ∀ i : Fin xs.length, ∃ j : Fin classes6.length,
        ccToDiagram (xs.get i) ∈ orbit 6 (classes6.get j).1 := by
      intro i
      obtain ⟨x, hx, hdx⟩ := (hu _).mp (hok _ (List.get_mem _ _))
      obtain ⟨j, rfl⟩ := List.get_of_mem hx
      exact ⟨j, hdx⟩
    choose f hf using hex
    refine ⟨f, fun i j hij => ?_, hf⟩
    have hnd : (xs.map fun x => canonKey 6 false (ccToDiagram x)).Nodup := nodup_of_strictSorted_sortNat h6
    have hki := canonKey_eq_of_mem_orbit (by norm_num) perms6 false
      (classes6_inRange _ (List.get_mem _ _)) (hf i)
    have hkj := canonKey_eq_of_mem_orbit (by norm_num) perms6 false
      (classes6_inRange _ (List.get_mem _ _)) (hf j)
    rw [hij] at hki
    have heq : xs.get i = xs.get j :=
      List.inj_on_of_nodup_map hnd (List.get_mem _ _) (List.get_mem _ _) (hki.trans hkj.symm)
    exact (hnd.of_map _).get_inj_iff.mp heq

end L6F1
