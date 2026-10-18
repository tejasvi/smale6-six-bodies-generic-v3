import Lean6.Special.K4.E4.Final
import Lean6.Special.Comp.K4.E4.Rem

/-!
# Remark 7.14

**`remark_7_14`**: at each of `μ = (1, 1, 1, 2), (5, 2, 11, 3), (1, 2, 3, 4), (2, 3, 5, 7)`, for every antisymmetric
sign pattern `σ`: if the construction of the remark applies, `G_σ` has a nonzero common zero, and every nonzero common
zero has two coinciding points `ξ_k = ξ_l` (so none survives the saturation by `∏ (ξ_k − ξ_l)`); otherwise `G_σ` has
no nonzero common zero. The construction applies to exactly 36, 16, 28, 28 of the 64 sign lists.
-/

namespace Lean6.Special.K4.E4

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.E4

theorem eval_monoEvalZ (x : List ℤ) : ∀ (m : Mono) (i : ℕ),
    ((monoEvalZ x m i : ℤ) : ℂ) = Mono.eval (fun j => (x.getD j 0 : ℂ)) m i
  | [], i => by simp [monoEvalZ, Mono.eval]
  | e :: m, i => by
    simp only [monoEvalZ, Mono.eval, Int.cast_mul, Int.cast_pow, eval_monoEvalZ x m (i + 1)]

theorem eval_sumZJ {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) :
    ∀ l : List ZJ, (zjHom ℂ ω hω).f (evalZJ.Poly.sumZJ l) = (l.map (zjHom ℂ ω hω).f).sum
  | [] => by
    simp only [evalZJ.Poly.sumZJ, List.map_nil, List.sum_nil]
    exact (zjHom ℂ ω hω).map_zero
  | a :: l => by
    simp only [evalZJ.Poly.sumZJ, (zjHom ℂ ω hω).map_add, eval_sumZJ hω l, List.map_cons, List.sum_cons]

theorem eval_evalZJ {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) (x : List ℤ) (p : Poly ZJ) :
    (zjHom ℂ ω hω).f (evalZJ x p) = Poly.eval (zjHom ℂ ω hω) (fun j => (x.getD j 0 : ℂ)) p := by
  rw [evalZJ, eval_sumZJ hω, Poly.eval, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp, (zjHom ℂ ω hω).map_mul]
  rw [← eval_monoEvalZ]
  simp [zjHom]

theorem eval_combo {R : Type*} [CommRing R] (h : zjC.Hom R) (x : ℕ → R) (rows : List (Poly ZJ)) (c : List ℤ)
    (h0 : ∀ r ∈ rows, Poly.eval h x r = 0) : Poly.eval h x (combo rows c) = 0 := by
  unfold combo
  rw [Poly.eval_sum]
  apply List.sum_eq_zero
  intro v hv
  simp only [List.mem_map] at hv
  obtain ⟨rc, ⟨b, hb, rfl⟩, rfl⟩ := hv
  rw [Poly.eval_mulTerm, h0 _ (List.of_mem_zip hb).1, mul_zero]

theorem eval_Dpoly {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) (ξ : Fin 3 → ℂ) :
    Poly.eval (zjHom ℂ ω hω) (xq ξ) Dpoly =
      ∏ kl ∈ ({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} : Finset (Fin 4 × Fin 4)),
        ((![0, ξ 0, ξ 1, ξ 2] : Fin 4 → ℂ) kl.1 - (![0, ξ 0, ξ 1, ξ 2] : Fin 4 → ℂ) kl.2) := by
  have hx : ∀ k : Fin 4, Poly.eval (zjHom ℂ ω hω) (xq ξ) (xiP k) = (![0, ξ 0, ξ 1, ξ 2] : Fin 4 → ℂ) k :=
    eval_xiP ξ hω
  simp only [Dpoly, List.foldr_cons, List.foldr_nil, Poly.eval_normalize, Poly.eval_mul, Poly.eval_sub]
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2; have h3 := hx 3
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  have h3' : Poly.eval (zjHom ℂ ω hω) (xq ξ) (xiP 3) = ξ 2 := by simpa using h3
  rw [h0, h1, h2, h3']
  simp [Finset.prod_insert, Poly.eval_cons, (zjHom ℂ ω hω).map_one]

/-- The statement of Remark 7.14 at the masses `μl`, with `n` patterns to which the construction applies. -/
def Rem714Statement (μl : List ℤ) (n : ℕ) : Prop :=
    (patsG.filter (consApplies μl)).length = n ∧
    ∀ (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (σ : Fin 4 → Fin 4 → ℤ), (∀ k l, σ l k = -σ k l) →
      (∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) →
      (consApplies μl (wOf σ) = true →
        (∃ ξ : Fin 3 → ℂ, ξ ≠ 0 ∧ GZero (muOf μl) σ ξ) ∧
        ∀ ξ : Fin 3 → ℂ, ξ ≠ 0 → GZero (muOf μl) σ ξ →
          ∃ k l : Fin 4, k ≠ l ∧ (![0, ξ 0, ξ 1, ξ 2] : Fin 4 → ℂ) k = (![0, ξ 0, ξ 1, ξ 2] : Fin 4 → ℂ) l) ∧
      (consApplies μl (wOf σ) = false → ∀ ξ : Fin 3 → ℂ, GZero (muOf μl) σ ξ → ξ = 0)

/-- **Remark 7.14** at the masses `μl`, from the compiled check `rem714 μl n`. -/
theorem remark_7_14_of {μl : List ℤ} {n : ℕ} (hc : rem714 μl n = true) : Rem714Statement μl n := by
  unfold Rem714Statement
  simp only [rem714, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨hcount, hall⟩ := hc
  refine ⟨hcount, fun ω hω σ hσa hσ => ?_⟩
  have hw := hall _ (wOf_mem σ hσ)
  constructor
  · intro hcons
    rw [hcons] at hw
    simp only [if_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨hl, hpt⟩, hsat⟩ := hw
    constructor
    · -- the point of the construction
      set x := consPoint μl (wOf σ) with hxdef
      have hlen : x.length = 3 := by
        rw [hxdef, consPoint]; split <;> simp
      refine ⟨fun i => (x.getD i 0 : ℂ), ?_, ?_⟩
      · intro h0
        have hl4 := hl
        rw [hxdef, consPoint] at h0
        by_cases hl0 : consL μl (wOf σ) = 0
        · have := congrFun h0 0
          simp [hl0] at this
        · have hl3 : consL μl (wOf σ) - 1 < 3 := by omega
          have := congrFun h0 ⟨consL μl (wOf σ) - 1, hl3⟩
          simp only [hl0, beq_iff_eq, if_false, Pi.zero_apply] at this
          rw [List.getD_eq_getElem _ _ (by simpa using hl3)] at this
          simp only [List.getElem_map, List.getElem_range] at this
          rw [if_pos (by omega)] at this
          norm_num at this
      · intro k
        have hxq : xq (fun i : Fin 3 => (x.getD i 0 : ℂ)) = fun j => (x.getD j 0 : ℂ) := by
          funext j
          by_cases hj : j < 3
          · simp [xq, hj]
          · simp only [xq, hj, dite_false]
            rw [List.getD_eq_default _ _ (by omega)]
            simp
        have hf := hpt (Gform μl (wOf σ) k, 4)
          (by simp only [formsG, List.mem_map, List.mem_range]; exact ⟨k, k.2, rfl⟩)
        have hf' : evalZJ x (Gform μl (wOf σ) k) = (0, 0) := by simpa using hf
        have he := eval_evalZJ hω x (Gform μl (wOf σ) k)
        rw [hf', ← hxq, eval_Gform hω μl σ hσa _ k] at he
        rw [← he]
        simp [zjHom]
    · -- every common zero has two coinciding points
      intro ξ hξ0 hξ
      have hrows : ∀ r ∈ macRows 3 7 (formsG μl (wOf σ)), Poly.eval (zjHom ℂ ω hω) (xq ξ) r = 0 :=
        eval_macRows_mem _ _ (formsG_vanish hω μl σ hσa ξ hξ)
      have key : ∀ (d : ℤ) (y : ℂ), d ≠ 0 → 0 = (zjHom ℂ ω hω).f (d, 0) * Mono.eval (xq ξ) [] 0 * y → y = 0 := by
        intro d y hd h
        simp only [zjHom, Int.cast_zero, zero_mul, add_zero, Mono.eval, mul_one] at h
        exact (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast hd)
      have hD : ∀ i : Fin 3, Poly.eval (zjHom ℂ ω hω) (xq ξ) Dpoly * ξ i = 0 := by
        intro i
        have hs := hsat i (List.mem_range.mpr i.2)
        simp only [satCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
        obtain ⟨hd, heq⟩ := hs
        have e := Poly.eqv_sound (zjHom ℂ ω hω) (xq ξ) heq
        rw [eval_combo _ _ _ _ hrows, Poly.eval_mulTerm] at e
        have e2 := key _ _ hd e
        rw [Poly.eval_normalize, Poly.eval_mul, Poly.eval_var] at e2
        have hxi : xq ξ i = ξ i := by simp [xq, i.2]
        rw [hxi] at e2
        exact e2
      obtain ⟨i, hi⟩ : ∃ i, ξ i ≠ 0 := by
        by_contra hno
        push_neg at hno
        exact hξ0 (funext hno)
      have hD0 := (mul_eq_zero.mp (hD i)).resolve_right hi
      rw [eval_Dpoly hω ξ, Finset.prod_eq_zero_iff] at hD0
      obtain ⟨kl, hkl, hz⟩ := hD0
      refine ⟨kl.1, kl.2, ?_, sub_eq_zero.mp hz⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hkl
      rcases hkl with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro hcons ξ hξ
    rw [hcons] at hw
    simp only [Bool.false_eq_true, if_false] at hw
    have h := macCheck_sound (by norm_num) sE_sq hw ω hω (xq ξ) (formsG_vanish hω μl σ hσa ξ hξ)
    funext k
    have := h k k.2
    simpa [xq] using this

theorem remark_7_14_1112 : Rem714Statement [1, 1, 1, 2] 36 := remark_7_14_of rem714_1112
theorem remark_7_14_5_2_11_3 : Rem714Statement [5, 2, 11, 3] 16 := remark_7_14_of rem714_5_2_11_3
theorem remark_7_14_1234 : Rem714Statement [1, 2, 3, 4] 28 := remark_7_14_of rem714_1234
theorem remark_7_14_2357 : Rem714Statement [2, 3, 5, 7] 28 := remark_7_14_of rem714_2357

end Lean6.Special.K4.E4
