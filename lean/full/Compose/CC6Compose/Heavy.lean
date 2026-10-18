import CC6Full.Six.D98
import CC6Full.Six.D93
import Lean6.Special.D98.Heavy

/-!
# Bridge: the heavy-mass facts of Lemma 6.13 from the certificate project

`HeavyFact` and `HeavyFact3` (the hypotheses of `d98_poly` and `d93_poly`) from `heavy_signed_sums` of the
certificate project (`Lean6.Special.D98`), whose `S`, `Lam` and `μH` are the paper's formulas written as functions;
`Sμ`, `LamP` and `μH` here are the same formulas as polynomials (`eval_Sμ_eq`, `eval_LamP_eq`, `μH_eq`).

* `heavyFact`: `HeavyFact` is `heavy_signed_sums` with all signs `+1`.
* `heavyFact3`: `HeavyFact3` from `HeavyFact` with `t' = t` and `c_jl = c_j c_l`, square roots of
  `μ_j² μ_l² Λ_j(t) Λ_l(t)` whose sum is `(c₁ + c₂ + c₃)²`.
-/

namespace CC6Compose

open CC6Full CC6Full.Six Polynomial

variable {R : Type*} [CommRing R]

/-- The quintic `Q_σ` of the certificate project at the sign pattern `σ = (a, b, c)` is `Qσ μ a b c` evaluated. -/
theorem Q_triple (μ : Fin 3 → R) (a b c : ℤ) (x : R) :
    Lean6.Special.D98.Q μ (a, b, c) x = (Qσ μ (a : R) (b : R) (c : R)).eval x := by
  rw [eval_Qσ]
  rfl

/-- The product of the `Q_σ` over the four classes of sign patterns. -/
theorem prod_Q_eq (μ : Fin 3 → R) (x : R) :
    ∏ i : Fin 4, Lean6.Special.D98.Q μ (Lean6.Special.D98.sig i) x =
      (Qσ μ 1 1 1).eval x * (Qσ μ 1 1 (-1)).eval x * (Qσ μ 1 (-1) (-1)).eval x *
        (Qσ μ 1 (-1) 1).eval x := by
  rw [Fin.prod_univ_four]
  show Lean6.Special.D98.Q μ (1, 1, 1) x * Lean6.Special.D98.Q μ (1, 1, -1) x *
      Lean6.Special.D98.Q μ (1, -1, -1) x * Lean6.Special.D98.Q μ (1, -1, 1) x = _
  simp only [Q_triple, Int.cast_one, Int.cast_neg]

/-- `S_μ(t)`: the polynomial `Sμ μ` at `t` is the certificate project's `S μ t`. -/
theorem eval_Sμ_eq (μ : Fin 3 → R) (t : R) : (Sμ μ).eval t = Lean6.Special.D98.S μ t := by
  rw [eval_Sμ, eval_lagProd, Lean6.Special.D98.S, prod_Q_eq]
  rfl

/-- `Λ_j(t)`: the polynomial `LamP μ j` at `t` is the certificate project's `Lam μ t j`. -/
theorem eval_LamP_eq (μ : Fin 3 → R) (t : R) (j : Fin 3) :
    (LamP μ j).eval t = Lean6.Special.D98.Lam μ t j := by
  rcases fin3_cases j with rfl | rfl | rfl
  · rw [LamP_zero, eval_mul, eval_ellP_one, eval_ellP_two]
    rfl
  · rw [LamP_one, eval_mul, eval_ellP_zero, eval_ellP_two]
    rfl
  · rw [LamP_two, eval_mul, eval_ellP_zero, eval_ellP_one]
    rfl

/-- The masses `(1, 2, 40)` of the two projects agree. -/
theorem μH_eq : CC6Full.Six.μH = Lean6.Special.D98.μH := rfl

theorem S_μH_of_isRoot {t : ℂ} (ht : (Sμ μH).IsRoot t) :
    Lean6.Special.D98.S Lean6.Special.D98.μH t = 0 := by
  rw [← eval_Sμ_eq, ← μH_eq]
  exact ht

/-- **`HeavyFact`** from `heavy_signed_sums` (all signs `+1`). -/
theorem heavyFact : HeavyFact := by
  intro t t' ht ht' c hc
  have h := Lean6.Special.D98.heavy_signed_sums t t' (S_μH_of_isRoot ht) (S_μH_of_isRoot ht') c
    (fun j l => by rw [hc j l, eval_LamP_eq, eval_LamP_eq, μH_eq]) (fun _ _ => 1) (fun _ _ => Or.inl rfl)
  simpa using h

/-- **`HeavyFact3`** from `HeavyFact`: if `c₁ + c₂ + c₃ = 0`, then `c_jl = c_j c_l` are square roots of
`μ_j² μ_l² Λ_j(t) Λ_l(t)` with `Σ_{j,l} c_jl = (c₁ + c₂ + c₃)² = 0`, which `HeavyFact` (with `t' = t`) excludes. -/
theorem heavyFact3 : HeavyFact3 := by
  intro t ht c hc hsum
  refine heavyFact t t ht ht (fun j l => c j * c l) (fun j l => ?_) ?_
  · show (c j * c l) ^ 2 = _
    rw [mul_pow, hc j, hc l]
    ring
  · show ∑ j, ∑ l, c j * c l = 0
    rw [← Finset.sum_mul_sum, hsum, zero_mul]

end CC6Compose
