import L6CheckKSpec.E4.All
import L6SoundKSpec.E4
import Lean6.Special.K4.E4.Final

/-!
# Lemma 7.7 and the check after Proposition 7.8, checked by the kernel

`Lean6.Special.K4.E4K.lemma_7_7` and `check_3_5_7_11` have the statements of lean6_special's
`Lean6.Special.K4.E4.lemma_7_7` and `check_3_5_7_11` (checked by the `example`s at the end), with the standard axioms
only: the Macaulay check of every pattern by the kernel (`L6CheckKSpec.E4`, `macCheckK`) and its soundness
(`macCheckK_sound`) in place of the compiled runs `allF_*`, `allG_*` and `macCheck_sound`, and the membership of the
patterns by the kernel (`mem_patsF_auxK`, `mem_patsG_auxK`). The forms `G_σ` enter
unnormalized (`formsGK`); they have the values of lean6_special's `formsG`.
-/

namespace Lean6.Special.K4.E4K

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.E4 Lean6.Special.K4.E4 L6KSpec.E4 L6CheckKSpec.E4

theorem patsF_length : patsF.length = 729 := by simp [patsF]

/-! The membership of the patterns (lean6_special's `mem_patsF_aux`, `mem_patsG_aux` are `native_decide`). -/

set_option maxRecDepth 100000 in
theorem mem_patsF_auxK : ∀ a b c d f g : Fin 3,
    [(a : ℕ), (b : ℕ), (c : ℕ), (d : ℕ), (f : ℕ), (g : ℕ)] ∈ patsF := by
  decide +kernel

theorem mem_patsG_auxK : ∀ a b c d f g : Bool,
    [cond a 1 (-1), cond b 1 (-1), cond c 1 (-1), cond d 1 (-1), cond f 1 (-1), cond g 1 (-1)] ∈ patsG := by
  decide +kernel

theorem vOf_memK (e : Fin 4 → Fin 4 → ℕ) : vOf e ∈ patsF :=
  mem_patsF_auxK ⟨_, Nat.mod_lt (e 0 1) (by norm_num)⟩ ⟨_, Nat.mod_lt (e 0 2) (by norm_num)⟩
    ⟨_, Nat.mod_lt (e 0 3) (by norm_num)⟩ ⟨_, Nat.mod_lt (e 1 2) (by norm_num)⟩
    ⟨_, Nat.mod_lt (e 1 3) (by norm_num)⟩ ⟨_, Nat.mod_lt (e 2 3) (by norm_num)⟩

theorem wOf_memK (σ : Fin 4 → Fin 4 → ℤ) (hσ : ∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) : wOf σ ∈ patsG := by
  have h := mem_patsG_auxK (decide (σ 0 1 = 1)) (decide (σ 0 2 = 1)) (decide (σ 0 3 = 1)) (decide (σ 1 2 = 1))
    (decide (σ 1 3 = 1)) (decide (σ 2 3 = 1))
  rwa [← sign_cond (hσ 0 1 (by decide)), ← sign_cond (hσ 0 2 (by decide)), ← sign_cond (hσ 0 3 (by decide)),
    ← sign_cond (hσ 1 2 (by decide)), ← sign_cond (hσ 1 3 (by decide)), ← sign_cond (hσ 2 3 (by decide))] at h

theorem patsG_length : patsG.length = 64 := by simp [patsG]

theorem formsGK_vanish {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) (μl : List ℤ) (σ : Fin 4 → Fin 4 → ℤ)
    (hσ : ∀ k l, σ l k = -σ k l) (ξ : Fin 3 → ℂ) (hξ : GZero (muOf μl) σ ξ) :
    ∀ f ∈ formsGK μl (wOf σ), Poly.eval (zjHom ℂ ω hω) (xq ξ) f.1 = 0 := by
  intro f hf
  simp only [formsGK, List.mem_map, List.mem_range] at hf
  obtain ⟨k, hk, rfl⟩ := hf
  have hmem : (Gform μl (wOf σ) k, 4) ∈ formsG μl (wOf σ) := by
    simp only [formsG, List.mem_map, List.mem_range]
    exact ⟨k, hk, rfl⟩
  have h := formsG_vanish hω μl σ hσ ξ hξ _ hmem
  have e : Gform μl (wOf σ) k = Poly.normalize zjC (GformK μl (wOf σ) k) := rfl
  rw [e, Poly.eval_normalize] at h
  exact h

theorem F_of_allFK {μl : List ℤ}
    (hc : ∀ i, i < 729 → ∃ sel B, macCheckK 4 7 pE sE (formsF μl (patsF.getD i [])) sel B = true) (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (e : Fin 4 → Fin 4 → ℕ) (he : ∀ k l, e k l = e l k) (q : Fin 4 → ℂ)
    (hq : FZero ω (muOf μl) e q) : q = 0 := by
  obtain ⟨i, hi, hv⟩ := List.mem_iff_getElem.mp (vOf_memK e)
  obtain ⟨sel, B, hcheck⟩ := hc i (by rw [← patsF_length]; exact hi)
  rw [List.getD_eq_getElem _ _ hi, hv] at hcheck
  have h := macCheckK_sound (by norm_num) sE_sq hcheck ω hω (xq q) (formsF_vanish hω μl e he q hq)
  funext k
  have := h k k.2
  simpa [xq] using this

theorem G_of_allGK {μl : List ℤ}
    (hc : ∀ i, i < 64 → ∃ sel B, macCheckK 3 8 pE sE (formsGK μl (patsG.getD i [])) sel B = true) (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (σ : Fin 4 → Fin 4 → ℤ) (hσa : ∀ k l, σ l k = -σ k l)
    (hσ : ∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) (ξ : Fin 3 → ℂ) (hξ : GZero (muOf μl) σ ξ) : ξ = 0 := by
  obtain ⟨i, hi, hv⟩ := List.mem_iff_getElem.mp (wOf_memK σ hσ)
  obtain ⟨sel, B, hcheck⟩ := hc i (by rw [← patsG_length]; exact hi)
  rw [List.getD_eq_getElem _ _ hi, hv] at hcheck
  have h := macCheckK_sound (by norm_num) sE_sq hcheck ω hω (xq ξ) (formsGK_vanish hω μl σ hσa ξ hξ)
  funext k
  have := h k k.2
  simpa [xq] using this

/-- **Lemma 7.7**, checked by the kernel. -/
theorem lemma_7_7 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    (∀ e : Fin 4 → Fin 4 → ℕ, (∀ k l, e k l = e l k) → ∀ q : Fin 4 → ℂ, FZero ω (fun _ => 1) e q → q = 0) ∧
    (∀ σ : Fin 4 → Fin 4 → ℤ, (∀ k l, σ l k = -σ k l) → (∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) →
      ∀ ξ : Fin 3 → ℂ, GZero (fun _ => 1) σ ξ → ξ = 0) := by
  have hμ : muOf [1, 1, 1, 1] = fun _ => 1 := by
    funext k; fin_cases k <;> simp [muOf]
  refine ⟨fun e he q hq => F_of_allFK allF1111 ω hω e he q (hμ ▸ hq),
    fun σ hσa hσ ξ hξ => G_of_allGK allG1111 ω hω σ hσa hσ ξ (hμ ▸ hξ)⟩

/-- **The check after Proposition 7.8**, checked by the kernel. -/
theorem check_3_5_7_11 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    (∀ e : Fin 4 → Fin 4 → ℕ, (∀ k l, e k l = e l k) → ∀ q : Fin 4 → ℂ, FZero ω ![3, 5, 7, 11] e q → q = 0) ∧
    (∀ σ : Fin 4 → Fin 4 → ℤ, (∀ k l, σ l k = -σ k l) → (∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) →
      ∀ ξ : Fin 3 → ℂ, GZero ![3, 5, 7, 11] σ ξ → ξ = 0) := by
  have hμ : muOf [3, 5, 7, 11] = ![3, 5, 7, 11] := by
    funext k; fin_cases k <;> simp [muOf]
  refine ⟨fun e he q hq => F_of_allFK allF3_5_7_11 ω hω e he q (hμ ▸ hq),
    fun σ hσa hσ ξ hξ => G_of_allGK allG3_5_7_11 ω hω σ hσa hσ ξ (hμ ▸ hξ)⟩

example : type_of% Lean6.Special.K4.E4.lemma_7_7 := Lean6.Special.K4.E4K.lemma_7_7
example : type_of% Lean6.Special.K4.E4.check_3_5_7_11 := Lean6.Special.K4.E4K.check_3_5_7_11

end Lean6.Special.K4.E4K
