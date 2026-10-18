import Lean6.Special.K4.E4.Defs
import Lean6.Special.K4.E4.Sound
import Lean6.Special.Comp.K4.E4.Run

/-!
# Lemma 7.7 and the check after Proposition 7.8, as complete computations

The forms of Lemma 7.6 are written here as in the paper: for a symmetric pattern `e` (`ε_{kl} = ω^{e_{kl}}`, `ω` a
primitive cube root of unity, i.e. `ω² + ω + 1 = 0`), `A_k = Σ_{l ≠ k} ε_{kl} μ_l q_l` and the seven cubic forms
`F_ε = {q_j² A_k − q_k² A_j (j < k), Σ_k μ_k q_k³}` (`FZero`); for an antisymmetric sign pattern `σ` the four quartic
forms `G_σ,k = Σ_{l ≠ k} σ_{kl} μ_l ∏_{j ≠ k, l} (ξ_k − ξ_j)²` with `ξ_1 = 0` (`GZero`, Lean's bodies `0, …, 3`).

* **`lemma_7_7`**: at `μ = (1, 1, 1, 1)` no `F_ε` has a common zero in `P³(ℂ)` and no `G_σ` has a common zero in
  `P²(ℂ)`: the only common zero is `0`.
* **`check_3_5_7_11`**: the same at `μ₀ = (3, 5, 7, 11)`, i.e. `μ₀ ∉ B_E` (Proposition 7.8).

Both follow from the compiled runs `Comp.E4.allF_*`, `Comp.E4.allG_*` (Macaulay matrices in degrees 7 and 8 modulo
`p = 2147483629`, `j ↦ 882503254`) through `macCheck_sound`, which carries the transfer from `ℤ/p` to `ℂ`.
-/

namespace Lean6.Special.K4.E4

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.E4

theorem mem_patsF_aux : ∀ a b c d f g : Fin 3,
    [(a : ℕ), (b : ℕ), (c : ℕ), (d : ℕ), (f : ℕ), (g : ℕ)] ∈ patsF := by
  native_decide

theorem vOf_mem (e : Fin 4 → Fin 4 → ℕ) : vOf e ∈ patsF :=
  mem_patsF_aux ⟨_, Nat.mod_lt (e 0 1) (by norm_num)⟩ ⟨_, Nat.mod_lt (e 0 2) (by norm_num)⟩
    ⟨_, Nat.mod_lt (e 0 3) (by norm_num)⟩ ⟨_, Nat.mod_lt (e 1 2) (by norm_num)⟩
    ⟨_, Nat.mod_lt (e 1 3) (by norm_num)⟩ ⟨_, Nat.mod_lt (e 2 3) (by norm_num)⟩

theorem mem_patsG_aux : ∀ a b c d f g : Bool,
    [cond a 1 (-1), cond b 1 (-1), cond c 1 (-1), cond d 1 (-1), cond f 1 (-1), cond g 1 (-1)] ∈ patsG := by
  native_decide

theorem sign_cond {z : ℤ} (hz : z = 1 ∨ z = -1) : z = cond (decide (z = 1)) 1 (-1) := by
  rcases hz with rfl | rfl <;> rfl

theorem wOf_mem (σ : Fin 4 → Fin 4 → ℤ) (hσ : ∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) : wOf σ ∈ patsG := by
  have h := mem_patsG_aux (decide (σ 0 1 = 1)) (decide (σ 0 2 = 1)) (decide (σ 0 3 = 1)) (decide (σ 1 2 = 1))
    (decide (σ 1 3 = 1)) (decide (σ 2 3 = 1))
  rwa [← sign_cond (hσ 0 1 (by decide)), ← sign_cond (hσ 0 2 (by decide)), ← sign_cond (hσ 0 3 (by decide)),
    ← sign_cond (hσ 1 2 (by decide)), ← sign_cond (hσ 1 3 (by decide)), ← sign_cond (hσ 2 3 (by decide))] at h

theorem omega_cube {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * hω

theorem eval_jpow {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) (n : ℕ) : (zjHom ℂ ω hω).f (jpow n) = ω ^ n := by
  have h3 := omega_cube hω
  have hn : ω ^ n = ω ^ (n % 3) := by
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, h3, one_pow, one_mul]
  rw [hn]
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h | h | h
  · simp [jpow, h, zjHom]
  · simp [jpow, h, zjHom]
  · simp [jpow, h, zjHom]
    linear_combination -hω

@[simp] theorem mono_eval_nil (x : ℕ → ℂ) (i : ℕ) : Mono.eval x [] i = 1 := rfl

theorem range4 : List.range 4 = [0, 1, 2, 3] := rfl

theorem eval_mu (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (z : ℤ) : (zjHom ℂ ω hω).f (z, 0) = (z : ℂ) := by
  simp [zjHom]

theorem eval_powMono (x : ℕ → ℂ) (k e : ℕ) : Mono.eval x (powMono k e) 0 = x k ^ e := by
  simp [powMono, Mono.eval_replicate_zero, Mono.eval]

theorem eval_Apoly {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) (μl : List ℤ) (e : Fin 4 → Fin 4 → ℕ)
    (he : ∀ k l, e k l = e l k) (q : Fin 4 → ℂ) (k : Fin 4) :
    Poly.eval (zjHom ℂ ω hω) (xq q) (Apoly μl (vOf e) k) = Aeps ω (muOf μl) e q k := by
  have h3 := omega_cube hω
  have hmod : ∀ n : ℕ, ω ^ (n % 3) = ω ^ n := fun n => by
    conv_rhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, h3, one_pow, one_mul]
  fin_cases k <;>
    simp [Apoly, Aeps, Fin.sum_univ_four, vOf, pairIdx, xq, muOf, Poly.eval_cons, Mono.eval_var,
      (zjHom ℂ ω hω).map_mul, eval_jpow hω, eval_mu, hmod, he 1 0, he 2 0, he 3 0, he 2 1, he 3 1, he 3 2,
      range4] <;> ring

theorem formsF_vanish {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) (μl : List ℤ) (e : Fin 4 → Fin 4 → ℕ)
    (he : ∀ k l, e k l = e l k) (q : Fin 4 → ℂ) (hq : FZero ω (muOf μl) e q) :
    ∀ f ∈ formsF μl (vOf e), Poly.eval (zjHom ℂ ω hω) (xq q) f.1 = 0 := by
  obtain ⟨hpair, hcub⟩ := hq
  have hA := eval_Apoly hω μl e he q
  intro f hf
  simp only [formsF, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  have hP : ∀ j k : Fin 4, j < k →
      Poly.eval (zjHom ℂ ω hω) (xq q) (Poly.sub zjC (Poly.mulTerm zjC zjC.one (powMono j 2) (Apoly μl (vOf e) k))
        (Poly.mulTerm zjC zjC.one (powMono k 2) (Apoly μl (vOf e) j))) = 0 := by
    intro j k hjk
    rw [Poly.eval_sub, Poly.eval_mulTerm, Poly.eval_mulTerm, (zjHom ℂ ω hω).map_one, eval_powMono,
      eval_powMono, hA, hA]
    simp only [xq, j.2, k.2, dite_true, one_mul]
    exact hpair j k hjk
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hP 0 1 (by decide)
  · exact hP 0 2 (by decide)
  · exact hP 0 3 (by decide)
  · exact hP 1 2 (by decide)
  · exact hP 1 3 (by decide)
  · exact hP 2 3 (by decide)
  · rw [range4]
    simp only [List.map_cons, List.map_nil, Poly.eval_cons, Poly.eval_nil, eval_mu, eval_powMono]
    simp only [Fin.sum_univ_four, muOf] at hcub
    simp only [xq]
    simpa [add_assoc] using hcub

theorem eval_xiP (ξ : Fin 3 → ℂ) (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 4) :
    Poly.eval (zjHom ℂ ω hω) (xq ξ) (xiP k) = (![0, ξ 0, ξ 1, ξ 2] : Fin 4 → ℂ) k := by
  fin_cases k <;> simp [xiP, xq, Poly.eval_var]

theorem eval_Gform {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) (μl : List ℤ) (σ : Fin 4 → Fin 4 → ℤ)
    (hσ : ∀ k l, σ l k = -σ k l) (ξ : Fin 3 → ℂ) (k : Fin 4) :
    Poly.eval (zjHom ℂ ω hω) (xq ξ) (Gform μl (wOf σ) k) = Gsig (muOf μl) σ ![0, ξ 0, ξ 1, ξ 2] k := by
  have hdsq : ∀ a b : Fin 4, Poly.eval (zjHom ℂ ω hω) (xq ξ) (dsq a b) =
      ((![0, ξ 0, ξ 1, ξ 2] : Fin 4 → ℂ) a - (![0, ξ 0, ξ 1, ξ 2] : Fin 4 → ℂ) b) ^ 2 := by
    intro a b
    rw [dsq, Poly.eval_mul, Poly.eval_sub, eval_xiP ξ hω a, eval_xiP ξ hω b]
    ring
  have hd : ∀ a b : ℕ, (ha : a < 4) → (hb : b < 4) → Poly.eval (zjHom ℂ ω hω) (xq ξ) (dsq a b) =
      ((![0, ξ 0, ξ 1, ξ 2] : Fin 4 → ℂ) ⟨a, ha⟩ - (![0, ξ 0, ξ 1, ξ 2] : Fin 4 → ℂ) ⟨b, hb⟩) ^ 2 :=
    fun a b ha hb => hdsq ⟨a, ha⟩ ⟨b, hb⟩
  fin_cases k <;>
    simp [Gform, Gsig, Fin.sum_univ_four, Fin.prod_univ_four, Poly.eval_normalize, Poly.eval_mul,
      Poly.eval_append, sigmaOf, wOf, pairIdx, muOf, range4, hd, hσ 1 0, hσ 2 0, hσ 3 0, hσ 2 1, hσ 3 1,
      hσ 3 2, eval_mu, (zjHom ℂ ω hω).map_one] <;> ring

theorem formsG_vanish {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) (μl : List ℤ) (σ : Fin 4 → Fin 4 → ℤ)
    (hσ : ∀ k l, σ l k = -σ k l) (ξ : Fin 3 → ℂ) (hξ : GZero (muOf μl) σ ξ) :
    ∀ f ∈ formsG μl (wOf σ), Poly.eval (zjHom ℂ ω hω) (xq ξ) f.1 = 0 := by
  intro f hf
  simp only [formsG, List.mem_map, List.mem_range] at hf
  obtain ⟨k, hk, rfl⟩ := hf
  have := eval_Gform hω μl σ hσ ξ ⟨k, hk⟩
  simp only at this ⊢
  rw [this]
  exact hξ ⟨k, hk⟩

/-! ## The theorems -/

theorem F_of_allF {μl : List ℤ} (hc : allF μl pE sE = true) (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (e : Fin 4 → Fin 4 → ℕ) (he : ∀ k l, e k l = e l k) (q : Fin 4 → ℂ) (hq : FZero ω (muOf μl) e q) : q = 0 := by
  have hcheck : macCheck 4 7 pE sE (formsF μl (vOf e)) = true := List.all_eq_true.mp hc _ (vOf_mem e)
  have h := macCheck_sound (by norm_num) sE_sq hcheck ω hω (xq q) (formsF_vanish hω μl e he q hq)
  funext k
  have := h k k.2
  simpa [xq] using this

theorem G_of_allG {μl : List ℤ} (hc : allG μl pE sE = true) (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (σ : Fin 4 → Fin 4 → ℤ) (hσa : ∀ k l, σ l k = -σ k l) (hσ : ∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1)
    (ξ : Fin 3 → ℂ) (hξ : GZero (muOf μl) σ ξ) : ξ = 0 := by
  have hcheck : macCheck 3 8 pE sE (formsG μl (wOf σ)) = true := List.all_eq_true.mp hc _ (wOf_mem σ hσ)
  have h := macCheck_sound (by norm_num) sE_sq hcheck ω hω (xq ξ) (formsG_vanish hω μl σ hσa ξ hξ)
  funext k
  have := h k k.2
  simpa [xq] using this

/-- **Lemma 7.7.** At `μ = (1, 1, 1, 1)`, for every symmetric pattern `e` (`ε_{kl} = ω^{e_{kl}}`) the forms `F_ε` have
no common zero in `P³(ℂ)`, and for every antisymmetric sign pattern `σ` the forms `G_σ` have no common zero in
`P²(ℂ)`. -/
theorem lemma_7_7 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    (∀ e : Fin 4 → Fin 4 → ℕ, (∀ k l, e k l = e l k) → ∀ q : Fin 4 → ℂ, FZero ω (fun _ => 1) e q → q = 0) ∧
    (∀ σ : Fin 4 → Fin 4 → ℤ, (∀ k l, σ l k = -σ k l) → (∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) →
      ∀ ξ : Fin 3 → ℂ, GZero (fun _ => 1) σ ξ → ξ = 0) := by
  have hμ : muOf [1, 1, 1, 1] = fun _ => 1 := by
    funext k; fin_cases k <;> simp [muOf]
  refine ⟨fun e he q hq => F_of_allF allF_1111 ω hω e he q (hμ ▸ hq),
    fun σ hσa hσ ξ hξ => G_of_allG allG_1111 ω hω σ hσa hσ ξ (hμ ▸ hξ)⟩

/-- **The check after Proposition 7.8**: the same at `μ₀ = (3, 5, 7, 11)`, so `μ₀ ∉ B_E`. -/
theorem check_3_5_7_11 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    (∀ e : Fin 4 → Fin 4 → ℕ, (∀ k l, e k l = e l k) → ∀ q : Fin 4 → ℂ, FZero ω ![3, 5, 7, 11] e q → q = 0) ∧
    (∀ σ : Fin 4 → Fin 4 → ℤ, (∀ k l, σ l k = -σ k l) → (∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) →
      ∀ ξ : Fin 3 → ℂ, GZero ![3, 5, 7, 11] σ ξ → ξ = 0) := by
  have hμ : muOf [3, 5, 7, 11] = ![3, 5, 7, 11] := by
    funext k; fin_cases k <;> simp [muOf]
  refine ⟨fun e he q hq => F_of_allF allF_3_5_7_11 ω hω e he q (hμ ▸ hq),
    fun σ hσa hσ ξ hξ => G_of_allG allG_3_5_7_11 ω hω σ hσa hσ ξ (hμ ▸ hξ)⟩

end Lean6.Special.K4.E4
