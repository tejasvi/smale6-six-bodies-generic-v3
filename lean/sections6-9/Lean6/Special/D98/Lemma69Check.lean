import Lean6.Special.D98.Lemma69

/-!
# Lemma 6.9: the check of the eliminants at `(1,2,7)`, `(1,2,8)`, `(2,3,11)`

`lemma69_check_*`: in `ℚ[X]`, the stored eliminant `g` (`elim_*.txt`) and `S_μ` have the square-free part `g₀`
(`g₀ ∣ g ∣ g₀³`, `g₀ ∣ S_μ ∣ g₀²`, `g₀` squarefree of degree `32`); over `ℂ`, `g` and `S_μ` have the same roots, and
`S_μ` has degree `34`, `34` roots counted with multiplicity and `32` distinct roots.
-/

namespace Lean6.Special.D98

open Polynomial Lean6.Special.Comp.D98

/-- The statement of the check at one mass point. -/
def Lemma69Check (m1 m2 m3 : ℤ) (g g0 : UP) (kg ks : ℕ) : Prop :=
  ((toPoly g0).map (Int.castRingHom ℚ) ∣ (toPoly g).map (Int.castRingHom ℚ)) ∧
  ((toPoly g).map (Int.castRingHom ℚ) ∣ ((toPoly g0).map (Int.castRingHom ℚ)) ^ kg) ∧
  ((toPoly g0).map (Int.castRingHom ℚ) ∣ (Spol ![(m1 : ℚ), m2, m3])) ∧
  ((Spol ![(m1 : ℚ), m2, m3]) ∣ ((toPoly g0).map (Int.castRingHom ℚ)) ^ ks) ∧
  Squarefree ((toPoly g0).map (Int.castRingHom ℚ)) ∧ (toPoly g0).natDegree = 32 ∧
  (∀ t : ℂ, ((toPoly g).map (Int.castRingHom ℂ)).eval t = 0 ↔ S ![(m1 : ℂ), m2, m3] t = 0) ∧
  (Spol ![(m1 : ℂ), m2, m3]).natDegree = 34 ∧ (Spol ![(m1 : ℂ), m2, m3]).roots.card = 34 ∧
  (Spol ![(m1 : ℂ), m2, m3]).roots.toFinset.card = 32

theorem map_toPoly_SUP {K : Type*} [CommRing K] (m1 m2 m3 : ℤ) :
    (toPoly (SUP m1 m2 m3)).map (Int.castRingHom K) = Spol ![(m1 : K), m2, m3] := by
  rw [toPoly_SUP, map_Spol]
  congr 1
  funext i
  fin_cases i <;> simp

theorem lemma69Check_of {m1 m2 m3 : ℤ} {g g0 : UP} {C : SqfCert} (h : sqfOK (SUP m1 m2 m3) g g0 C = true)
    {lc lg : ℤ} (hS : UP.degLead (SUP m1 m2 m3) 34 lc = true) (hg0 : UP.degLead g0 32 lg = true) :
    Lemma69Check m1 m2 m3 g g0 C.kg C.ks := by
  obtain ⟨d1, d2, d3, d4, hK⟩ := sqfOK_sound h
  obtain ⟨hSn, hSl⟩ := degLead_sound hS
  obtain ⟨hgn, hgl⟩ := degLead_sound hg0
  have hlc : lc ≠ 0 := by
    simp only [UP.degLead, Bool.and_eq_true, bne_iff_ne, ne_eq] at hS; exact hS.2
  have hlg : lg ≠ 0 := by
    simp only [UP.degLead, Bool.and_eq_true, bne_iff_ne, ne_eq] at hg0; exact hg0.2
  have inj : ∀ (K : Type) [Field K] [CharZero K], Function.Injective (Int.castRingHom K) :=
    fun K _ _ => (Int.castRingHom K).injective_int
  -- degrees over ℂ
  have hSC : (Spol ![(m1 : ℂ), m2, m3]).natDegree = 34 := by
    rw [← map_toPoly_SUP, natDegree_map_eq_of_injective (inj ℂ), hSn]
  have hgC : ((toPoly g0).map (Int.castRingHom ℂ)).natDegree = 32 := by
    rw [natDegree_map_eq_of_injective (inj ℂ), hgn]
  have hSC0 : Spol ![(m1 : ℂ), m2, m3] ≠ 0 := by
    intro h0; rw [h0, natDegree_zero] at hSC; exact absurd hSC (by norm_num)
  have hgC0 : (toPoly g0).map (Int.castRingHom ℂ) ≠ 0 := by
    intro h0; rw [h0, natDegree_zero] at hgC; exact absurd hgC (by norm_num)
  obtain ⟨hsep, hroots⟩ := hK ℂ
  refine ⟨d1, d2, ?_, ?_, ?_, hgn, ?_, hSC, ?_, ?_⟩
  · rw [← map_toPoly_SUP]; exact d3
  · rw [← map_toPoly_SUP]; exact d4
  · exact ((hK ℚ).1).squarefree
  · intro t
    rw [(hroots t).1, ← (hroots t).2, map_toPoly_SUP, eval_Spol]
  · rw [IsAlgClosed.card_roots_eq_natDegree, hSC]
  · have e : (Spol ![(m1 : ℂ), m2, m3]).roots.toFinset = ((toPoly g0).map (Int.castRingHom ℂ)).roots.toFinset := by
      ext t
      simp only [Multiset.mem_toFinset, mem_roots hSC0, mem_roots hgC0, IsRoot.def]
      rw [← (hroots t).2, map_toPoly_SUP]
    rw [e, Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree, hgC]

/-- **Lemma 6.9, check at `μ = (1,2,7)`.** -/
theorem lemma69_check_1_2_7 : Lemma69Check 1 2 7 g_1_2_7 g0_1_2_7 3 2 :=
  lemma69Check_of (C := cert_1_2_7) sqf_1_2_7 deg_1_2_7.1 deg_1_2_7.2.1

/-- **Lemma 6.9, check at `μ = (1,2,8)`.** -/
theorem lemma69_check_1_2_8 : Lemma69Check 1 2 8 g_1_2_8 g0_1_2_8 3 2 :=
  lemma69Check_of (C := cert_1_2_8) sqf_1_2_8 deg_1_2_8.1 deg_1_2_8.2.1

/-- **Lemma 6.9, check at `μ = (2,3,11)`.** -/
theorem lemma69_check_2_3_11 : Lemma69Check 2 3 11 g_2_3_11 g0_2_3_11 3 2 :=
  lemma69Check_of (C := cert_2_3_11) sqf_2_3_11 deg_2_3_11.1 deg_2_3_11.2.1

end Lean6.Special.D98
