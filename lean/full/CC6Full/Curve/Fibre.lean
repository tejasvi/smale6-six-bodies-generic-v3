import CC6Full.Curve.SlicePoint
import Mathlib.Algebra.Polynomial.Roots

/-!
# The fibres of the squared distances on the slice are finite

The fibre count in the proof of Corollary 2.4 (`cor:curve`), following the five-body proof of
[Tom26, Corollary 2.5], in the coordinates `z, w, p` of `CC6Full.Curve.System`. Bodies `1, 2` of the paper are
`0, 1`.

* `body_z`, `body_w`: the equations of the bodies (2.2) (`eq:bodies`) at a point of `X_m`.
* `sum_mul_zc_eq_zero`, `sum_mul_wc_eq_zero`: on `X_m`, `Σ_k m_k z_k = Σ_k m_k w_k = 0` (sum the equations of the
  bodies with the weights `m_k`; the double sum is antisymmetric).
* `eval_pc_sq_mul_r2P`: on `X_m`, `p_kl² r²_kl = 1`, so `r²_kl` vanishes nowhere.
* `r2_fibre_finite`: if `M = Σ_k m_k ≠ 0`, then for every `c` the points of `Y_m` with `r²_kl = c_kl` for all `k, l`
  form a finite set. On such a point `z₁ − z₂ = 1` and `w₁ − w₂ = c₁₂`; for every `k`, `a = z_k − z₂` and
  `b = w_k − w₂` satisfy `a b = c_k2` and `(a − 1)(b − c₁₂) = c_k1`, so `b = c_k2 + c₁₂ − c_k1 − c₁₂ a` and `a` is a
  root of `−c₁₂ X² + (c_k2 + c₁₂ − c_k1) X − c_k2`, whose leading coefficient is nonzero since `c₁₂ = r²₁₂ ≠ 0`; the
  centre of mass gives `z₂ = −(Σ_k m_k a_k)/M` and `w₂ = −(Σ_k m_k b_k)/M`; and each `p_kl` is a root of
  `c_kl X² − 1`. So the fibre is the image of a finite set (`fibrePoint`).
-/

namespace CC6Full

open Finset MvPolynomial

section bodies

variable {N : ℕ} {m : Fin N → ℝ} {y : Coord N → ℂ}

/-- The equation of body `k` in the colour `z` at a point of `X_m`: `z_k = Σ_{l ≠ k} m_l p_kl³ (z_k − z_l)`. -/
theorem body_z (hy : y ∈ Xm m) (k : Fin N) :
    y (zc k) = ∑ l ∈ univ.erase k, (m l : ℂ) * eval y (pP k l) ^ 3 * (y (zc k) - y (zc l)) := by
  have h := hy _ (rowZ_mem_rows m k)
  rw [eval_rowZ] at h
  exact sub_eq_zero.mp h

/-- The equation of body `k` in the colour `w` at a point of `X_m`: `w_k = Σ_{l ≠ k} m_l p_kl³ (w_k − w_l)`. -/
theorem body_w (hy : y ∈ Xm m) (k : Fin N) :
    y (wc k) = ∑ l ∈ univ.erase k, (m l : ℂ) * eval y (pP k l) ^ 3 * (y (wc k) - y (wc l)) := by
  have h := hy _ (rowW_mem_rows m k)
  rw [eval_rowW] at h
  exact sub_eq_zero.mp h

/-- An equation `x_k = Σ_{l ≠ k} m_l p_kl³ (x_k − x_l)` for all `k`, with `p` symmetric, gives `Σ_k m_k x_k = 0`. -/
theorem sum_mul_eq_zero_of_body {x : Fin N → ℂ} {P : Fin N → Fin N → ℂ} (hP : ∀ k l, P k l = P l k)
    (hx : ∀ k, x k = ∑ l ∈ univ.erase k, (m l : ℂ) * P k l ^ 3 * (x k - x l)) : ∑ k, (m k : ℂ) * x k = 0 := by
  have h : ∀ k, (m k : ℂ) * x k = ∑ l, (m k : ℂ) * m l * P k l ^ 3 * (x k - x l) := by
    intro k
    conv_lhs => rw [hx k]
    rw [Finset.mul_sum, ← Finset.sum_erase univ (a := k)
      (f := fun l => (m k : ℂ) * m l * P k l ^ 3 * (x k - x l)) (by simp)]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun k _ => h k]
  exact sum_sum_mul_sub_of_symm (fun k l => by rw [hP k l, mul_comm (m k : ℂ)]) x

/-- The centre of mass in the colour `z`: `Σ_k m_k z_k = 0` on `X_m`. -/
theorem sum_mul_zc_eq_zero (hy : y ∈ Xm m) : ∑ k, (m k : ℂ) * y (zc k) = 0 :=
  sum_mul_eq_zero_of_body (P := fun k l => eval y (pP k l)) (fun k l => by simp only [pP_comm k l])
    (body_z hy)

/-- The centre of mass in the colour `w`: `Σ_k m_k w_k = 0` on `X_m`. -/
theorem sum_mul_wc_eq_zero (hy : y ∈ Xm m) : ∑ k, (m k : ℂ) * y (wc k) = 0 :=
  sum_mul_eq_zero_of_body (P := fun k l => eval y (pP k l)) (fun k l => by simp only [pP_comm k l])
    (body_w hy)

/-- The distance row: `p_e² r²_e = 1` on `X_m`. -/
theorem eval_pc_sq_mul_r2P (hy : y ∈ Xm m) (e : Pair N) : y (pc e) ^ 2 * eval y (r2P e.1.1 e.1.2) = 1 := by
  have h := hy _ (rowD_mem_rows m e)
  rw [eval_rowD] at h
  rw [eval_r2P]
  linear_combination h

/-- `r²_e` vanishes nowhere on `X_m`. -/
theorem eval_r2P_ne_zero (hy : y ∈ Xm m) (e : Pair N) : eval y (r2P e.1.1 e.1.2) ≠ 0 := by
  intro h
  have := eval_pc_sq_mul_r2P hy e
  rw [h, mul_zero] at this
  exact zero_ne_one this

end bodies

section fibre

variable {n : ℕ}

/-- The quadratic of which `z_k − z₂` is a root on the fibre over `c`. -/
noncomputable def fibreQuad (c : Fin (n + 2) → Fin (n + 2) → ℂ) (k : Fin (n + 2)) : Polynomial ℂ :=
  -Polynomial.C (c 0 1) * Polynomial.X ^ 2 + Polynomial.C (c k 1 + c 0 1 - c k 0) * Polynomial.X -
    Polynomial.C (c k 1)

/-- `w_k − w₂` on the fibre over `c`, as a function of `z_k − z₂`. -/
def fibreW (c : Fin (n + 2) → Fin (n + 2) → ℂ) (k : Fin (n + 2)) (a : ℂ) : ℂ :=
  c k 1 + c 0 1 - c k 0 - c 0 1 * a

/-- The point of the fibre over `c` with `z_k − z₂ = A k` and `p = P`: the positions are fixed by the centre of
mass. -/
noncomputable def fibrePoint (m : Fin (n + 2) → ℝ) (c : Fin (n + 2) → Fin (n + 2) → ℂ) (A : Fin (n + 2) → ℂ)
    (P : Pair (n + 2) → ℂ) : Coord (n + 2) → ℂ
  | Sum.inl k => A k - (∑ j, (m j : ℂ) * A j) / ∑ j, (m j : ℂ)
  | Sum.inr (Sum.inl k) => fibreW c k (A k) - (∑ j, (m j : ℂ) * fibreW c j (A j)) / ∑ j, (m j : ℂ)
  | Sum.inr (Sum.inr e) => P e

theorem fibreQuad_ne_zero {c : Fin (n + 2) → Fin (n + 2) → ℂ} (hc : c 0 1 ≠ 0) (k : Fin (n + 2)) :
    fibreQuad c k ≠ 0 := by
  intro h
  have h2 := congrArg (fun q => Polynomial.coeff q 2) h
  simp [fibreQuad] at h2
  exact hc h2

/-- **The fibres of the squared distances on `Y_m` are finite** (for `Σ_k m_k ≠ 0`). -/
theorem r2_fibre_finite {m : Fin (n + 2) → ℝ} (hM : ∑ i, m i ≠ 0) (c : Fin (n + 2) → Fin (n + 2) → ℂ) :
    {y | y ∈ Ym m ∧ ∀ k l, eval y (r2P k l) = c k l}.Finite := by
  have hM' : (∑ i, (m i : ℂ)) ≠ 0 := by exact_mod_cast hM
  by_cases hc : c 0 1 = 0
  · refine Set.finite_empty.subset fun y hy => ?_
    have h : eval y (r2P 0 1) ≠ 0 := eval_r2P_ne_zero hy.1.1 ⟨(0, 1), Fin.zero_lt_one⟩
    exact (h ((hy.2 0 1).trans hc)).elim
  have hP : ∀ e : Pair (n + 2), (Polynomial.C (c e.1.1 e.1.2) * Polynomial.X ^ 2 - 1 : Polynomial ℂ) ≠ 0 :=
    fun e h => by
      have h0 := congrArg (fun q => Polynomial.coeff q 0) h
      simp [Polynomial.coeff_C] at h0
  have hS : ((Set.pi Set.univ fun k => {a | (fibreQuad c k).IsRoot a}) ×ˢ
      (Set.pi Set.univ fun e : Pair (n + 2) =>
        {p | (Polynomial.C (c e.1.1 e.1.2) * Polynomial.X ^ 2 - 1 : Polynomial ℂ).IsRoot p})).Finite :=
    (Set.Finite.pi fun k => Polynomial.finite_setOfPred_isRoot (fibreQuad_ne_zero hc k)).prod
      (Set.Finite.pi fun e => Polynomial.finite_setOfPred_isRoot (hP e))
  refine (hS.image fun x => fibrePoint m c x.1 x.2).subset ?_
  rintro y ⟨hy, hr⟩
  have hs : y (zc 0) - y (zc 1) = 1 := by
    have h := hy.2
    rw [eval_sliceP] at h
    linear_combination h
  have h01 : y (wc 0) - y (wc 1) = c 0 1 := by
    have h := hr 0 1
    rw [eval_r2P, hs, one_mul] at h
    exact h
  have hW : ∀ k, y (wc k) - y (wc 1) = fibreW c k (y (zc k) - y (zc 1)) := by
    intro k
    have hk1 := hr k 1
    have hk0 := hr k 0
    rw [eval_r2P] at hk1 hk0
    simp only [fibreW]
    linear_combination hk1 - hk0 + (y (wc 0) - y (wc k)) * hs + (y (zc 1) + 1 - y (zc k)) * h01
  have hroot : ∀ k, (fibreQuad c k).IsRoot (y (zc k) - y (zc 1)) := by
    intro k
    have hk1 := hr k 1
    rw [eval_r2P] at hk1
    have hWk := hW k
    simp only [fibreW] at hWk
    simp only [fibreQuad, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    linear_combination hk1 - (y (zc k) - y (zc 1)) * hWk
  refine ⟨(fun k => y (zc k) - y (zc 1), fun e => y (pc e)),
    ⟨fun k _ => hroot k, fun e _ => ?_⟩, ?_⟩
  · have h := eval_pc_sq_mul_r2P hy.1 e
    rw [hr] at h
    show (Polynomial.C (c e.1.1 e.1.2) * Polynomial.X ^ 2 - 1 : Polynomial ℂ).IsRoot (y (pc e))
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    linear_combination h
  · have hz := sum_mul_zc_eq_zero hy.1
    have hw := sum_mul_wc_eq_zero hy.1
    funext x
    rcases x with k | k | e
    · show y (zc k) - y (zc 1) - (∑ j, (m j : ℂ) * (y (zc j) - y (zc 1))) / ∑ j, (m j : ℂ) = y (zc k)
      have h : ∑ j, (m j : ℂ) * (y (zc j) - y (zc 1)) = -(∑ j, (m j : ℂ)) * y (zc 1) := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hz]
        ring
      rw [h, neg_mul, neg_div, mul_div_cancel_left₀ _ hM']
      ring
    · show fibreW c k (y (zc k) - y (zc 1)) -
          (∑ j, (m j : ℂ) * fibreW c j (y (zc j) - y (zc 1))) / ∑ j, (m j : ℂ) = y (wc k)
      simp only [← hW]
      have h : ∑ j, (m j : ℂ) * (y (wc j) - y (wc 1)) = -(∑ j, (m j : ℂ)) * y (wc 1) := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw]
        ring
      rw [h, neg_mul, neg_div, mul_div_cancel_left₀ _ hM']
      ring
    · rfl

end fibre

end CC6Full
