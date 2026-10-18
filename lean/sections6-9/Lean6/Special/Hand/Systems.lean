import Lean6.Special.D88.Boxes.Systems

/-!
# The torque identity and the systems of Sec. 6.7

* **`torque_identity`**: for four bodies, `Σ_k μ_k (Y_k Xeq_k − X_k Yeq_k) = 0` identically (any commutative ring),
  and **`com_identity`**: `Σ_k μ_k Xeq_k = Σ_k μ_k X_k`.
* **`N4.yeq2_of_S11`**: a zero of `S11` (the system of Lemma 6.19(c), `Lean6.Special.D88.Boxes.N4.S11`) satisfies the
  Y-equation of body 3, so it is a zero of `S12`; this is the step "`μ₃ (X₄ − X₃) Yeq₃` lies in the ideal of `S11` and
  `X₄ − X₃` is invertible modulo the distance equation of `34`" of Sec. 6.7, on zero sets.
* **`KC.yeq2_of_KC12`**: a zero of `KC12` satisfies the Y-equation of body 3, so it is a zero of `KC` (which has no
  Y-equation of body 4).
-/

namespace Lean6.Special.Hand

open Lean6.Special.D88.Boxes

/-- The symmetric matrix of the six distances. -/
def symP {R : Type*} [Zero R] (a b c d e f : R) : Fin 4 → Fin 4 → R :=
  ![![0, a, b, c], ![a, 0, d, e], ![b, d, 0, f], ![c, e, f, 0]]

/-- The equation of body `k` in one colour: `V_k − Σ_{l≠k} μ_l p_kl³ (V_k − V_l)`. -/
def eqn {R : Type*} [CommRing R] (μ : Fin 4 → R) (p : Fin 4 → Fin 4 → R) (V : Fin 4 → R) (k : Fin 4) : R :=
  V k - ∑ l, if l = k then 0 else μ l * p k l ^ 3 * (V k - V l)

/-- **The torque identity** `Σ_k μ_k (Y_k Xeq_k − X_k Yeq_k) = 0`. -/
theorem torque_identity {R : Type*} [CommRing R] (μ X Y : Fin 4 → R) (a b c d e f : R) :
    ∑ k, μ k * (Y k * eqn μ (symP a b c d e f) X k - X k * eqn μ (symP a b c d e f) Y k) = 0 := by
  simp [eqn, symP, Fin.sum_univ_four]
  ring

/-- **The centre of mass identity** `Σ_k μ_k Xeq_k = Σ_k μ_k X_k`. -/
theorem com_identity {R : Type*} [CommRing R] (μ X : Fin 4 → R) (a b c d e f : R) :
    ∑ k, μ k * eqn μ (symP a b c d e f) X k = ∑ k, μ k * X k := by
  simp [eqn, symP, Fin.sum_univ_four]
  ring

namespace N4

theorem p_eq (v : Fin 11 → ℂ) : N4.p v = symP (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) := rfl

theorem Xeq_eq (v : Fin 11 → ℂ) (k : Fin 4) : N4.Xeq v k = eqn μ0 (N4.p v) (N4.X v) k := rfl

theorem Yeq_eq (v : Fin 11 → ℂ) (k : Fin 4) : N4.Yeq v k = eqn μ0 (N4.p v) (N4.Y v) k := rfl

/-- **A zero of `S11` is a zero of `S12`**: it satisfies the Y-equation of body 3. -/
theorem yeq2_of_S11 (v : Fin 11 → ℂ) (h : N4.S11 v = 0) : N4.Yeq v 2 = 0 := by
  have hr : ∀ i, N4.S11 v i = 0 := fun i => congrFun h i
  have x0 : N4.Xeq v 0 = 0 := hr 0
  have x1 : N4.Xeq v 1 = 0 := hr 1
  have x2 : N4.Xeq v 2 = 0 := hr 2
  have y0 : N4.Yeq v 0 = 0 := hr 3
  have y1 : N4.Yeq v 1 = 0 := hr 4
  have d23 : N4.dist v 2 3 = 0 := hr 10
  -- centre of mass in X: the X-equation of body 4
  have cx : ∑ k, μ0 k * N4.Xeq v k = ∑ k, μ0 k * N4.X v k := by
    simp only [Xeq_eq, p_eq]; exact com_identity _ _ _ _ _ _ _ _
  have cx0 : ∑ k, μ0 k * N4.X v k = 0 := by
    simp [N4.X, μ0, Fin.sum_univ_four]; ring
  have cy : ∑ k, μ0 k * N4.Yeq v k = ∑ k, μ0 k * N4.Y v k := by
    simp only [Yeq_eq, p_eq]; exact com_identity _ _ _ _ _ _ _ _
  have cy0 : ∑ k, μ0 k * N4.Y v k = 0 := by
    simp [N4.Y, μ0, Fin.sum_univ_four]; ring
  have tq : ∑ k, μ0 k * (N4.Y v k * N4.Xeq v k - N4.X v k * N4.Yeq v k) = 0 := by
    simp only [Xeq_eq, Yeq_eq, p_eq]; exact torque_identity _ _ _ _ _ _ _ _ _
  rw [cx0] at cx
  rw [cy0] at cy
  simp only [Fin.sum_univ_four] at cx cy tq
  have m3 : μ0 3 = 30 := rfl
  have m2 : μ0 2 = 3 := rfl
  rw [x0, x1, x2] at cx tq
  rw [y0, y1] at cy tq
  have x3 : N4.Xeq v 3 = 0 := by
    rw [m3] at cx; linear_combination cx / 30
  rw [x3] at tq
  -- tq: −μ₃ X₃ Yeq₃ − μ₄ X₄ Yeq₄ = 0 and cy: μ₃ Yeq₃ + μ₄ Yeq₄ = 0
  have key : (N4.X v 2 - N4.X v 3) * N4.Yeq v 2 = 0 := by
    rw [m2, m3] at cy tq
    linear_combination (-1 / 3 : ℂ) * tq + (-(N4.X v 3) / 3) * cy
  have hX : N4.X v 2 - N4.X v 3 ≠ 0 := by
    intro h0
    simp only [N4.dist, h0, mul_zero, zero_mul, zero_sub] at d23
    norm_num at d23
  exact (mul_eq_zero.mp key).resolve_left hX

end N4

namespace KC

theorem p_eq (v : Fin 12 → ℂ) : KC.p v = symP (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) := rfl

theorem Xeq_eq (v : Fin 12 → ℂ) (k : Fin 4) : KC.Xeq v k = eqn μ0 (KC.p v) (KC.X v) k := rfl

theorem Yeq_eq (v : Fin 12 → ℂ) (k : Fin 4) : KC.Yeq v k = eqn μ0 (KC.p v) (KC.Y v) k := rfl

/-- **A zero of `KC12` is a zero of `KC`**: it satisfies the Y-equation of body 3. -/
theorem yeq2_of_KC12 (v : Fin 12 → ℂ) (h : KC.KC12 v = 0) : KC.Yeq v 2 = 0 := by
  have hr : ∀ i, KC.KC12 v i = 0 := fun i => congrFun h i
  have x0 : KC.Xeq v 0 = 0 := hr 0
  have x1 : KC.Xeq v 1 = 0 := hr 1
  have x2 : KC.Xeq v 2 = 0 := hr 2
  have xc : KC.Xc v = 0 := hr 3
  have y0 : KC.Yeq v 0 = 0 := hr 4
  have y1 : KC.Yeq v 1 = 0 := hr 5
  have d23 : KC.dist v 2 3 = 0 := hr 11
  -- the X-equation of body 4 is minus the equation of the centre, since X₄ = 0
  have x3 : KC.Xeq v 3 = 0 := by
    have e : KC.Xeq v 3 = -KC.Xc v := by
      simp [KC.Xeq, KC.Xc, KC.X, Fin.sum_univ_four]
    rw [e, xc, neg_zero]
  have tq : ∑ k, μ0 k * (KC.Y v k * KC.Xeq v k - KC.X v k * KC.Yeq v k) = 0 := by
    simp only [Xeq_eq, Yeq_eq, p_eq]; exact torque_identity _ _ _ _ _ _ _ _ _
  simp only [Fin.sum_univ_four] at tq
  rw [x0, x1, x2, x3, y0, y1] at tq
  have hX3 : KC.X v 3 = 0 := rfl
  have m2 : μ0 2 = 3 := rfl
  rw [hX3, m2] at tq
  have key : KC.X v 2 * KC.Yeq v 2 = 0 := by linear_combination (-1 / 3 : ℂ) * tq
  have hX : KC.X v 2 ≠ 0 := by
    intro h0
    simp only [KC.dist, h0, hX3, sub_zero, mul_zero, zero_mul, zero_sub] at d23
    norm_num at d23
  exact (mul_eq_zero.mp key).resolve_left hX

end KC

end Lean6.Special.Hand
