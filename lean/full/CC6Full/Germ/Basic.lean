import CC6Full.Statement
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Germs: the expansions at a singular place

Paper §2.2 (`ss:places`, Lemma 2.5 `lem:place`) and §2.3 (`ss:identities`). At a singular place `P` of a curve
`C ⊆ Y_m`, after the rotation by `s = ϑ^{2γ}` of Lemma 2.5, every function `f` of the three kinds is
`ϑ^{d e(f)} y_f(ϑ)` with `y_f(0) ≠ 0`. In the variable `τ = ϑ^d` the functions `z_k`, `w_k`, `p_kl` become Hahn
series with rational exponents whose orders are the exponents `e(f)`. They satisfy the equations of the bodies
(2.2), the distance equations, and `U = E`, and the exponents of the components of `𝒵 = (z_k, Z_kl)` and of
`𝒲 = (w_k, W_kl)` are at least `−2`, with equality for some component of each (Lemma 2.5).

A `Germ n m` is such a family of series. Everything after Corollary 2.7 (`cor:sum`) is proved for germs:
exponents are orders (`HahnSeries.orderTop`), leading coefficients are `HahnSeries.leadingCoeff`, and the
coefficient `[f]_e` of the paper is `f.coeff e`.

* `Germ.relabel σ`: the germ of the relabelled place, for the masses `m ∘ σ` (Lemma 2.9 (a), `lem:symm`).
* `Germ.swap`: the germ of the image of the place under the involution `ι` of Lemma 2.2 (`lem:exchange`), which
  exchanges the colours (Lemma 2.9 (b)).
* `Germ.scale`: the germ for the masses `t m`, `t > 0` (Lemma 2.1 (b), `lem:slice`).
* `Germ.zeta`, `Germ.omega`, `Germ.x`, `Germ.ell`: `ζ_kl = e(z_kl)`, `ω_kl = e(w_kl)`, the type `x_kl` and
  `ℓ(x) = Σ_{k<l} x_kl`, written as half the sum over ordered pairs.
* The diagram: `zStroke`, `wStroke`, `zCircle`, `wCircle` (§2.4, `ss:rules`).
-/

namespace CC6Full

open Finset

noncomputable section

/-- Hahn series with rational exponents over `ℂ`, the ring of the expansions. -/
abbrev Ser := HahnSeries ℚ ℂ

/-- The constant series of a complex number. -/
abbrev cS (c : ℂ) : Ser := HahnSeries.C c

/-- The term `Z_kl = p_kl³ (z_k − z_l)` of a colour `h` (`h = z` or `h = w`). -/
def termZ (p : Fin n → Fin n → Ser) (h : Fin n → Ser) (k l : Fin n) : Ser := p k l ^ 3 * (h k - h l)

/-- The components of `𝒵_h` have exponents at least `−2`, and one of them has exponent `−2` (Lemma 2.5). -/
def LowAt (p : Fin n → Fin n → Ser) (h : Fin n → Ser) : Prop :=
  (∀ k, ((-2 : ℚ) : WithTop ℚ) ≤ (h k).orderTop) ∧
    (∀ k l, k ≠ l → ((-2 : ℚ) : WithTop ℚ) ≤ (termZ p h k l).orderTop) ∧
    ((∃ k, (h k).orderTop = ((-2 : ℚ) : WithTop ℚ)) ∨
      ∃ k l, k ≠ l ∧ (termZ p h k l).orderTop = ((-2 : ℚ) : WithTop ℚ))

/-- A *germ* for the masses `m`: the rotated expansions of `z_k`, `w_k`, `p_kl` at a singular place of a
nontrivial curve, in the variable `τ = ϑ^d`. -/
structure Germ (n : ℕ) (m : Fin n → ℝ) where
  /-- the positions in the colour `z` -/
  z : Fin n → Ser
  /-- the positions in the colour `w` -/
  w : Fin n → Ser
  /-- the inverse distances `p_kl` -/
  p : Fin n → Fin n → Ser
  p_symm : ∀ k l, p k l = p l k
  /-- the equations of the bodies (2.2) in `z` -/
  body_z : ∀ k, z k = ∑ l ∈ univ.erase k, cS (m l) * termZ p z k l
  /-- the equations of the bodies (2.2) in `w` -/
  body_w : ∀ k, w k = ∑ l ∈ univ.erase k, cS (m l) * termZ p w k l
  /-- the distance equations `p_kl² z_kl w_kl = 1` -/
  dist : ∀ k l, k ≠ l → p k l ^ 2 * (z k - z l) * (w k - w l) = 1
  /-- the constant value of `U` on the curve -/
  E : ℂ
  E_ne : E ≠ 0
  /-- `U = E`, written as `Σ_{k ≠ l} m_k m_l p_kl = 2E` -/
  pot : ∑ k, ∑ l ∈ univ.erase k, cS (m k * m l) * p k l = cS (2 * E)
  low_z : LowAt p z
  low_w : LowAt p w

namespace Germ

variable {n : ℕ} {m : Fin n → ℝ} (G : Germ n m)

/-! ## Basic facts -/

theorem z_sub_ne_zero {k l : Fin n} (h : k ≠ l) : G.z k - G.z l ≠ 0 := by
  intro h0
  have := G.dist k l h
  rw [h0, mul_zero, zero_mul] at this
  exact zero_ne_one this

theorem w_sub_ne_zero {k l : Fin n} (h : k ≠ l) : G.w k - G.w l ≠ 0 := by
  intro h0
  have := G.dist k l h
  rw [h0, mul_zero] at this
  exact zero_ne_one this

theorem p_ne_zero {k l : Fin n} (h : k ≠ l) : G.p k l ≠ 0 := by
  intro h0
  have := G.dist k l h
  rw [h0] at this
  simp at this

/-! ## Exponents -/

/-- `ζ_kl = e(z_kl)`, the order of `z_k − z_l` (junk `0` on the diagonal). -/
noncomputable def zeta (k l : Fin n) : ℚ := (G.z k - G.z l).order

/-- `ω_kl = e(w_kl)`. -/
noncomputable def omega (k l : Fin n) : ℚ := (G.w k - G.w l).order

/-- The type `x_kl = e(r_kl) = −e(p_kl)`. -/
noncomputable def x (k l : Fin n) : ℚ := -(G.p k l).order

/-- `ℓ(x) = Σ_{k<l} x_kl`, as half the sum over ordered pairs. -/
noncomputable def ell : ℚ := (∑ k, ∑ l ∈ univ.erase k, G.x k l) / 2

theorem orderTop_z_sub {k l : Fin n} (h : k ≠ l) : (G.z k - G.z l).orderTop = (G.zeta k l : WithTop ℚ) :=
  (HahnSeries.order_eq_orderTop_of_ne_zero (G.z_sub_ne_zero h)).symm

theorem orderTop_w_sub {k l : Fin n} (h : k ≠ l) : (G.w k - G.w l).orderTop = (G.omega k l : WithTop ℚ) :=
  (HahnSeries.order_eq_orderTop_of_ne_zero (G.w_sub_ne_zero h)).symm

theorem orderTop_p {k l : Fin n} (h : k ≠ l) : (G.p k l).orderTop = ((-G.x k l : ℚ) : WithTop ℚ) := by
  rw [x, neg_neg]
  exact (HahnSeries.order_eq_orderTop_of_ne_zero (G.p_ne_zero h)).symm

/-- `2 e(p_kl) + ζ_kl + ω_kl = 0`, i.e. `x_kl = (ζ_kl + ω_kl)/2`. -/
theorem x_eq {k l : Fin n} (h : k ≠ l) : G.x k l = (G.zeta k l + G.omega k l) / 2 := by
  have hd := congrArg HahnSeries.orderTop (G.dist k l h)
  rw [HahnSeries.orderTop_one, HahnSeries.orderTop_mul, HahnSeries.orderTop_mul, pow_two,
    HahnSeries.orderTop_mul, G.orderTop_z_sub h, G.orderTop_w_sub h, G.orderTop_p h] at hd
  have h2 : (-G.x k l) + (-G.x k l) + G.zeta k l + G.omega k l = 0 := by exact_mod_cast hd
  linarith

/-! ## The diagram (§2.4) -/

/-- `kl` is a `z`-stroke: `e(Z_kl) = −2`. -/
def zStroke (k l : Fin n) : Prop := k ≠ l ∧ (termZ G.p G.z k l).orderTop = ((-2 : ℚ) : WithTop ℚ)

/-- `kl` is a `w`-stroke: `e(W_kl) = −2`. -/
def wStroke (k l : Fin n) : Prop := k ≠ l ∧ (termZ G.p G.w k l).orderTop = ((-2 : ℚ) : WithTop ℚ)

/-- Body `k` is `z`-circled: `a_k = e(z_k) = −2`. -/
def zCircle (k : Fin n) : Prop := (G.z k).orderTop = ((-2 : ℚ) : WithTop ℚ)

/-- Body `k` is `w`-circled. -/
def wCircle (k : Fin n) : Prop := (G.w k).orderTop = ((-2 : ℚ) : WithTop ℚ)

end Germ

end

end CC6Full
