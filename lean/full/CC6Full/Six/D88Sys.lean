import CC6Full.Six.D88Gen
import CC6Full.Six.Three

/-!
# Diagram 88: the systems `S12` and `S11` of §6.7 with symbolic masses

For the computations of Lemma 6.19 (`lem:d88comp`) §6.7 of the paper (`ss:d88`) uses the slice `X₁ − X₂ = 1` of the
system `N₄(μ)`, the unknowns `v = (X₂, X₃, Y₁, Y₂, Y₃, p₁₂, p₁₃, p₁₄, p₂₃, p₂₄, p₃₄)` (`v₀, …, v₁₀` in Lean), and
`X₄`, `Y₄` eliminated by the centre of mass. The system `S12` consists of the `X`- and `Y`-equations of the bodies
`1, 2, 3` and the six distance equations; `S11` omits the `Y`-equation of body `3`. In Lean the bodies `1, …, 4` are
`0, …, 3`.

* `D88.X`, `D88.Y`, `D88.p`, `D88.Xeq`, `D88.Yeq`, `D88.dist`, `D88.S11`, `D88.S12`: the systems over `ℂ` for masses
  `μ : Fin 4 → ℂ`, with the division by `μ₄` in `X₄` and `Y₄`, written as in the checks of Lemma 6.19 (c) (at
  `μ = D88.μ0 = (1, 2, 3, 30)`).
* `D88.rows12`: the twelve equations of `S12` with the denominators cleared, over any commutative ring. The `X`- and
  `Y`-equations are polynomial as they stand, since `μ₄ p_k4³ (X_k − X₄) = p_k4³ (μ₄X_k + μ₁X₁ + μ₂X₂ + μ₃X₃)`; the
  distance equations of the pairs `14, 24, 34` are multiplied by `μ₄²`. `D88.S12P`: these as polynomials in `v` over
  `ℤ[μ]`. The evaluation lemmas: `D88.rows12_eq` (`rows12 μ v = sc12 μ · S12 μ v` when `μ₄ ≠ 0`), `D88.eval_S12P`,
  `D88.eval_S12P_eq`.
* `D88.torque_rows`: the identity `Σ_k μ_k (Y_k Xeq_k − X_k Yeq_k) = 0` of §6.7, combined with the centre of mass, in
  the form `μ₃ (μ₄X₃ − μ₄X₄) Yeq₃ = Σ_{k≤3} μ_k (μ₄Y_k − μ₄Y₄) Xeq_k − Σ_{k≤2} μ_k (μ₄X_k − μ₄X₄) Yeq_k`.
  `D88.S12_of_S11`: so a zero of `S11` with `X₃ − X₄ ≠ 0` is a zero of `S12` (when `μ₃, μ₄ ≠ 0`).
* `D88.slice`: a solution `(X, Y, P)` of `N₄(μ)` (`IsNSys`) moved to the slice by `X ↦ X/(X₁ − X₂)`,
  `Y ↦ (X₁ − X₂) Y`, under which `N₄(μ)` is invariant; `D88.S12_slice`: it is a zero of `S12`.
* `D88.Xh`: the positions multiplied by `μ₄` (polynomial), for the binary relations.
* `D88.μ0R`, `D88.eval_S12P_μ0`: the masses `μ₀` as reals (for the `T`-test), and `S12P` at `μ₀`.
-/

namespace CC6Full.Six.D88

open Finset

noncomputable section

/-! ## The systems over `ℂ` -/

/-- The masses `μ₀ = (1, 2, 3, 30)` of Lemma 6.19 (`lem:d88comp`). -/
def μ0 : Fin 4 → ℂ := ![1, 2, 3, 30]

/-- The positions `X` on the slice: `X₁ = v₀ + 1`, `X₂ = v₀`, `X₃ = v₁` and, from the centre of mass,
`X₄ = −(μ₁X₁ + μ₂X₂ + μ₃X₃)/μ₄`. -/
def X (μ : Fin 4 → ℂ) (v : Fin 11 → ℂ) : Fin 4 → ℂ :=
  ![v 0 + 1, v 0, v 1, -(μ 0 * (v 0 + 1) + μ 1 * v 0 + μ 2 * v 1) / μ 3]

/-- The positions `Y`: `Y₁ = v₂`, `Y₂ = v₃`, `Y₃ = v₄`, `Y₄ = −(μ₁Y₁ + μ₂Y₂ + μ₃Y₃)/μ₄`. -/
def Y (μ : Fin 4 → ℂ) (v : Fin 11 → ℂ) : Fin 4 → ℂ :=
  ![v 2, v 3, v 4, -(μ 0 * v 2 + μ 1 * v 3 + μ 2 * v 4) / μ 3]

/-- The unknowns `p_kl`: `p₁₂, p₁₃, p₁₄, p₂₃, p₂₄, p₃₄ = v₅, …, v₁₀` (symmetric, `0` on the diagonal). -/
def p (v : Fin 11 → ℂ) : Fin 4 → Fin 4 → ℂ :=
  ![![0, v 5, v 6, v 7], ![v 5, 0, v 8, v 9], ![v 6, v 8, 0, v 10], ![v 7, v 9, v 10, 0]]

/-- The `X`-equation of body `k`: `X_k − Σ_{l≠k} μ_l p_kl³ (X_k − X_l)`. -/
def Xeq (μ : Fin 4 → ℂ) (v : Fin 11 → ℂ) (k : Fin 4) : ℂ :=
  X μ v k - ∑ l, if l = k then 0 else μ l * p v k l ^ 3 * (X μ v k - X μ v l)

/-- The `Y`-equation of body `k`: `Y_k − Σ_{l≠k} μ_l p_kl³ (Y_k − Y_l)`. -/
def Yeq (μ : Fin 4 → ℂ) (v : Fin 11 → ℂ) (k : Fin 4) : ℂ :=
  Y μ v k - ∑ l, if l = k then 0 else μ l * p v k l ^ 3 * (Y μ v k - Y μ v l)

/-- The distance equation of the pair `ab`: `p_ab² (X_a − X_b)(Y_a − Y_b) − 1`. -/
def dist (μ : Fin 4 → ℂ) (v : Fin 11 → ℂ) (a b : Fin 4) : ℂ :=
  p v a b ^ 2 * (X μ v a - X μ v b) * (Y μ v a - Y μ v b) - 1

/-- **The system `S11`** of §6.7: the `X`-equations of the bodies `1, 2, 3`, the `Y`-equations of the bodies `1, 2`
and the distance equations of `12, 13, 14, 23, 24, 34`. -/
def S11 (μ : Fin 4 → ℂ) (v : Fin 11 → ℂ) : Fin 11 → ℂ :=
  ![Xeq μ v 0, Xeq μ v 1, Xeq μ v 2, Yeq μ v 0, Yeq μ v 1, dist μ v 0 1, dist μ v 0 2, dist μ v 0 3,
    dist μ v 1 2, dist μ v 1 3, dist μ v 2 3]

/-- **The system `S12`** of §6.7: `S11` and the `Y`-equation of body `3`. -/
def S12 (μ : Fin 4 → ℂ) (v : Fin 11 → ℂ) : Fin 12 → ℂ :=
  ![Xeq μ v 0, Xeq μ v 1, Xeq μ v 2, Yeq μ v 0, Yeq μ v 1, Yeq μ v 2, dist μ v 0 1, dist μ v 0 2,
    dist μ v 0 3, dist μ v 1 2, dist μ v 1 3, dist μ v 2 3]

section Basic

variable (μ : Fin 4 → ℂ) (v : Fin 11 → ℂ)

theorem X_zero : X μ v 0 = v 0 + 1 := rfl

theorem X_one : X μ v 1 = v 0 := rfl

theorem X_two : X μ v 2 = v 1 := rfl

theorem X_three : X μ v 3 = -(μ 0 * (v 0 + 1) + μ 1 * v 0 + μ 2 * v 1) / μ 3 := rfl

theorem Y_zero : Y μ v 0 = v 2 := rfl

theorem Y_one : Y μ v 1 = v 3 := rfl

theorem Y_two : Y μ v 2 = v 4 := rfl

theorem Y_three : Y μ v 3 = -(μ 0 * v 2 + μ 1 * v 3 + μ 2 * v 4) / μ 3 := rfl

/-- The `X`-equation through the force `Φ` of `CC6Full.force`. -/
theorem Xeq_eq_force (k : Fin 4) : Xeq μ v k = X μ v k - force μ (p v) (X μ v) k := by
  rw [Xeq, force, sum_ite_eq_sum_erase]

/-- The `Y`-equation through the force. -/
theorem Yeq_eq_force (k : Fin 4) : Yeq μ v k = Y μ v k - force μ (p v) (Y μ v) k := by
  rw [Yeq, force, sum_ite_eq_sum_erase]

end Basic

/-! ## The equations with cleared denominators, over a commutative ring -/

section Rows

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The positions `X₁ = v₀ + 1`, `X₂ = v₀`, `X₃ = v₁` of the bodies `1, 2, 3` on the slice. -/
def gX (v : Fin 11 → R) : Fin 3 → R := ![v 0 + 1, v 0, v 1]

/-- The positions `Y₁ = v₂`, `Y₂ = v₃`, `Y₃ = v₄`. -/
def gY (v : Fin 11 → R) : Fin 3 → R := ![v 2, v 3, v 4]

/-- The momenta `μ_l X_l`, with `μ₄X₄ = −(μ₁X₁ + μ₂X₂ + μ₃X₃)` (the centre of mass). -/
def gmX (μ : Fin 4 → R) (v : Fin 11 → R) : Fin 4 → R :=
  ![μ 0 * (v 0 + 1), μ 1 * v 0, μ 2 * v 1, -(μ 0 * (v 0 + 1) + μ 1 * v 0 + μ 2 * v 1)]

/-- The momenta `μ_l Y_l`, with `μ₄Y₄ = −(μ₁Y₁ + μ₂Y₂ + μ₃Y₃)`. -/
def gmY (μ : Fin 4 → R) (v : Fin 11 → R) : Fin 4 → R :=
  ![μ 0 * v 2, μ 1 * v 3, μ 2 * v 4, -(μ 0 * v 2 + μ 1 * v 3 + μ 2 * v 4)]

/-- The unknowns `p_kl`, over any commutative ring. -/
def gp (v : Fin 11 → R) : Fin 4 → Fin 4 → R :=
  ![![0, v 5, v 6, v 7], ![v 5, 0, v 8, v 9], ![v 6, v 8, 0, v 10], ![v 7, v 9, v 10, 0]]

/-- The `X`-equation of the body `k ∈ {1, 2, 3}` (`k : Fin 3`), polynomial:
`X_k − Σ_{l≠k} p_kl³ (μ_l X_k − μ_l X_l)`. -/
def rowX (μ : Fin 4 → R) (v : Fin 11 → R) (k : Fin 3) : R :=
  gX v k - ∑ l : Fin 4, if l = k.castSucc then 0 else gp v k.castSucc l ^ 3 * (μ l * gX v k - gmX μ v l)

/-- The `Y`-equation of the body `k ∈ {1, 2, 3}`, polynomial. -/
def rowY (μ : Fin 4 → R) (v : Fin 11 → R) (k : Fin 3) : R :=
  gY v k - ∑ l : Fin 4, if l = k.castSucc then 0 else gp v k.castSucc l ^ 3 * (μ l * gY v k - gmY μ v l)

/-- The distance equation of a pair `kl` of bodies in `{1, 2, 3}`. -/
def rowD (v : Fin 11 → R) (k l : Fin 3) : R :=
  gp v k.castSucc l.castSucc ^ 2 * (gX v k - gX v l) * (gY v k - gY v l) - 1

/-- The distance equation of the pair `k4`, multiplied by `μ₄²`:
`p_k4² (μ₄X_k − μ₄X₄)(μ₄Y_k − μ₄Y₄) − μ₄²`. -/
def rowD4 (μ : Fin 4 → R) (v : Fin 11 → R) (k : Fin 3) : R :=
  gp v k.castSucc 3 ^ 2 * (μ 3 * gX v k - gmX μ v 3) * (μ 3 * gY v k - gmY μ v 3) - μ 3 ^ 2

/-- **The twelve equations of `S12`** with the denominators cleared, in the order of `S12`. -/
def rows12 (μ : Fin 4 → R) (v : Fin 11 → R) : Fin 12 → R :=
  ![rowX μ v 0, rowX μ v 1, rowX μ v 2, rowY μ v 0, rowY μ v 1, rowY μ v 2, rowD v 0 1, rowD v 0 2, rowD4 μ v 0,
    rowD v 1 2, rowD4 μ v 1, rowD4 μ v 2]

/-- The positions multiplied by `μ₄`: `μ₄X₁, μ₄X₂, μ₄X₃` and `μ₄X₄ = −(μ₁X₁ + μ₂X₂ + μ₃X₃)`. -/
def Xh (μ : Fin 4 → R) (v : Fin 11 → R) : Fin 4 → R :=
  ![μ 3 * (v 0 + 1), μ 3 * v 0, μ 3 * v 1, -(μ 0 * (v 0 + 1) + μ 1 * v 0 + μ 2 * v 1)]

variable {F : Type*} [FunLike F R S] [RingHomClass F R S]

theorem map_rows12 (f : F) (μ : Fin 4 → R) (v : Fin 11 → R) (i : Fin 12) :
    f (rows12 μ v i) = rows12 (fun k => f (μ k)) (fun j => f (v j)) i := by
  fin_cases i <;> simp [rows12, rowX, rowY, rowD, rowD4, gX, gY, gmX, gmY, gp, Fin.sum_univ_four]

theorem map_Xh (f : F) (μ : Fin 4 → R) (v : Fin 11 → R) (l : Fin 4) :
    f (Xh μ v l) = Xh (fun k => f (μ k)) (fun j => f (v j)) l := by
  fin_cases l <;> simp [Xh]

/-- `Xh μ v` takes values in a subring containing the values of `μ` and `v`. -/
theorem Xh_mem (T : Subring R) {μ : Fin 4 → R} {v : Fin 11 → R} (hμ : ∀ k, μ k ∈ T) (hv : ∀ j, v j ∈ T)
    (l : Fin 4) : Xh μ v l ∈ T := by
  have h := map_Xh T.subtype (fun k => (⟨μ k, hμ k⟩ : T)) (fun j => ⟨v j, hv j⟩) l
  simp only [Subring.coe_subtype] at h
  rw [← h]
  exact (Xh (fun k => (⟨μ k, hμ k⟩ : T)) (fun j => (⟨v j, hv j⟩ : T)) l).2

/-- **The torque identity** of §6.7 for the polynomial equations: `Σ_k μ_k (Y_k Xeq_k − X_k Yeq_k) = 0`
identically, and with `μ₄Xeq₄ = −Σ_{k≤3} μ_k Xeq_k`, `μ₄Yeq₄ = −Σ_{k≤3} μ_k Yeq_k` (the centre of mass) it reads
`μ₃ (μ₄X₃ − μ₄X₄) Yeq₃ = Σ_{k≤3} μ_k (μ₄Y_k − μ₄Y₄) Xeq_k − Σ_{k≤2} μ_k (μ₄X_k − μ₄X₄) Yeq_k`. -/
theorem torque_rows (μ : Fin 4 → R) (v : Fin 11 → R) :
    μ 2 * (μ 3 * gX v 2 - gmX μ v 3) * rowY μ v 2 =
      μ 0 * (μ 3 * gY v 0 - gmY μ v 3) * rowX μ v 0 + μ 1 * (μ 3 * gY v 1 - gmY μ v 3) * rowX μ v 1 +
        μ 2 * (μ 3 * gY v 2 - gmY μ v 3) * rowX μ v 2 - μ 0 * (μ 3 * gX v 0 - gmX μ v 3) * rowY μ v 0 -
        μ 1 * (μ 3 * gX v 1 - gmX μ v 3) * rowY μ v 1 := by
  simp only [rowX, rowY, gX, gY, gmX, gmY, gp, Fin.sum_univ_four]
  simp
  ring

end Rows

/-! ## The evaluation lemmas -/

section Eval

variable {μ : Fin 4 → ℂ} (hμ : μ 3 ≠ 0) (v : Fin 11 → ℂ)
include hμ

theorem rowX_eq (k : Fin 3) : rowX μ v k = Xeq μ v k.castSucc := by
  fin_cases k <;> simp [rowX, Xeq, X, p, gX, gmX, gp, Fin.sum_univ_four] <;> field_simp <;> ring

theorem rowY_eq (k : Fin 3) : rowY μ v k = Yeq μ v k.castSucc := by
  fin_cases k <;> simp [rowY, Yeq, Y, p, gY, gmY, gp, Fin.sum_univ_four] <;> field_simp

theorem rowD4_eq (k : Fin 3) : rowD4 μ v k = μ 3 ^ 2 * dist μ v k.castSucc 3 := by
  fin_cases k <;> simp [rowD4, dist, X, Y, p, gX, gY, gmX, gmY, gp] <;> field_simp

omit hμ in
theorem rowD_eq (k l : Fin 3) : rowD v k l = dist μ v k.castSucc l.castSucc := by
  fin_cases k <;> fin_cases l <;> simp [rowD, dist, X, Y, p, gX, gY, gp]

/-- `Xh μ v = μ₄ X` when `μ₄ ≠ 0`. -/
theorem Xh_eq (l : Fin 4) : Xh μ v l = μ 3 * X μ v l := by
  fin_cases l <;> simp [Xh, X]
  field_simp

/-- The row factors: `μ₄²` for the distance equations of the pairs `14, 24, 34`, `1` otherwise. -/
def sc12 (μ : Fin 4 → ℂ) : Fin 12 → ℂ := ![1, 1, 1, 1, 1, 1, 1, 1, μ 3 ^ 2, 1, μ 3 ^ 2, μ 3 ^ 2]

/-- **The evaluation lemma**: the polynomial equations are the equations of `S12` times the row factors. -/
theorem rows12_eq (i : Fin 12) : rows12 μ v i = sc12 μ i * S12 μ v i := by
  fin_cases i <;> simp [rows12, sc12, S12, rowX_eq hμ, rowY_eq hμ, rowD_eq (μ := μ) v, rowD4_eq hμ]

/-- The zeros of `rows12 μ` are the zeros of `S12 μ` when `μ₄ ≠ 0`. -/
theorem rows12_eq_zero_iff : rows12 μ v = 0 ↔ S12 μ v = 0 := by
  have hsc : ∀ i, sc12 μ i ≠ 0 := fun i => by fin_cases i <;> simp [sc12, hμ]
  constructor
  · intro h
    funext i
    have h1 := congrFun h i
    rw [rows12_eq hμ, Pi.zero_apply] at h1
    exact (mul_eq_zero.mp h1).resolve_left (hsc i)
  · intro h
    funext i
    rw [rows12_eq hμ, h]
    simp

end Eval

/-! ## The polynomials over `ℤ[μ]` -/

/-- **`S12` as polynomials** in `v` over `ℤ[μ]` (`μ = (μ₁, …, μ₄)`), the denominators `μ₄` cleared. -/
def S12P : Fin 12 → MvPolynomial (Fin 11) (MvPolynomial (Fin 4) ℤ) :=
  rows12 (fun k => MvPolynomial.C (MvPolynomial.X k)) MvPolynomial.X

/-- Evaluation of `S12P`: the coefficients through `f : ℤ[μ] → R`, the unknowns at `v`. -/
theorem eval_S12P {R : Type*} [CommRing R] (f : MvPolynomial (Fin 4) ℤ →+* R) (v : Fin 11 → R) (i : Fin 12) :
    MvPolynomial.eval v (MvPolynomial.map f (S12P i)) = rows12 (fun k => f (MvPolynomial.X k)) v i := by
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, S12P, map_rows12]
  simp

/-- **Evaluation of `S12P` at complex masses** `μ` with `μ₄ ≠ 0`: the equations of `S12` times the row factors. -/
theorem eval_S12P_eq {μ : Fin 4 → ℂ} (hμ : μ 3 ≠ 0) (v : Fin 11 → ℂ) (i : Fin 12) :
    MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) μ) (S12P i)) =
      sc12 μ i * S12 μ v i := by
  rw [eval_S12P]
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
  exact rows12_eq hμ v i

/-! ## The masses `μ₀` -/

/-- The masses `μ₀ = (1, 2, 3, 30)` of Lemma 6.19 as reals, for the `T`-test. -/
def μ0R : Fin 4 → ℝ := ![1, 2, 3, 30]

theorem μ0_two_ne : μ0 2 ≠ 0 := by norm_num [μ0]

theorem μ0_three_ne : μ0 3 ≠ 0 := by norm_num [μ0]

/-- `S12P` with the coefficients evaluated at `μ₀` (`μ0Z`): the equations `rows12 μ₀`. -/
theorem eval_S12P_μ0 (v : Fin 11 → ℂ) (i : Fin 12) :
    MvPolynomial.eval v (MvPolynomial.map ((Int.castRingHom ℂ).comp (MvPolynomial.eval μ0Z)) (S12P i)) =
      rows12 μ0 v i := by
  have hμ : (fun k => ((Int.castRingHom ℂ).comp (MvPolynomial.eval μ0Z)) (MvPolynomial.X k)) = μ0 := by
    funext k
    fin_cases k <;> norm_num [μ0Z, μ0]
  rw [eval_S12P, hμ]

/-! ## From `S11` to `S12` -/

/-- **`S11` and `S12` have the same zeros where `X₃ ≠ X₄`** (§6.7): by the torque identity (`torque_rows`),
`μ₃ (X₄ − X₃) Yeq₃` lies in the ideal of `S11`. -/
theorem S12_of_S11 {μ : Fin 4 → ℂ} (h2 : μ 2 ≠ 0) (h3 : μ 3 ≠ 0) {v : Fin 11 → ℂ} (h : S11 μ v = 0)
    (hX : X μ v 2 - X μ v 3 ≠ 0) : S12 μ v = 0 := by
  have hS : ∀ i : Fin 11, S11 μ v i = 0 := fun i => congrFun h i
  have hx0 : rowX μ v 0 = 0 := (rowX_eq h3 v 0).trans (hS 0)
  have hx1 : rowX μ v 1 = 0 := (rowX_eq h3 v 1).trans (hS 1)
  have hx2 : rowX μ v 2 = 0 := (rowX_eq h3 v 2).trans (hS 2)
  have hy0 : rowY μ v 0 = 0 := (rowY_eq h3 v 0).trans (hS 3)
  have hy1 : rowY μ v 1 = 0 := (rowY_eq h3 v 1).trans (hS 4)
  have key := torque_rows μ v
  rw [hx0, hx1, hx2, hy0, hy1] at key
  have hfac : μ 3 * gX v 2 - gmX μ v 3 = μ 3 * (X μ v 2 - X μ v 3) := by
    simp only [gX, gmX, X_two, X_three]
    simp
    field_simp
  rw [hfac] at key
  have hy2 : rowY μ v 2 = 0 := by
    have h0 : μ 2 * (μ 3 * (X μ v 2 - X μ v 3)) * rowY μ v 2 = 0 := by
      rw [key]
      ring
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero h2 (mul_ne_zero h3 hX))
  have hY2 : Yeq μ v 2 = 0 := (rowY_eq h3 v 2).symm.trans hy2
  funext i
  fin_cases i
  exacts [hS 0, hS 1, hS 2, hS 3, hS 4, hY2, hS 5, hS 6, hS 7, hS 8, hS 9, hS 10]

/-! ## Moving a solution of `N₄(μ)` to the slice -/

/-- The point of the slice given by a solution `(X, Y, P)` of `N₄(μ)`, after `X ↦ X/(X₁ − X₂)`, `Y ↦ (X₁ − X₂) Y`:
`v = (X₂, X₃, Y₁, Y₂, Y₃, P₁₂, P₁₃, P₁₄, P₂₃, P₂₄, P₃₄)` of the moved solution. -/
def slice (Xo Yo : Fin 4 → ℂ) (P : Fin 4 → Fin 4 → ℂ) : Fin 11 → ℂ :=
  ![(Xo 0 - Xo 1)⁻¹ * Xo 1, (Xo 0 - Xo 1)⁻¹ * Xo 2, (Xo 0 - Xo 1) * Yo 0, (Xo 0 - Xo 1) * Yo 1,
    (Xo 0 - Xo 1) * Yo 2, P 0 1, P 0 2, P 0 3, P 1 2, P 1 3, P 2 3]

section Slice

variable {μ : Fin 4 → ℂ} {Xo Yo : Fin 4 → ℂ} {P : Fin 4 → Fin 4 → ℂ}

theorem X_slice (hμ : μ 3 ≠ 0) (h01 : Xo 0 - Xo 1 ≠ 0) (hcom : ∑ k, μ k * Xo k = 0) (l : Fin 4) :
    X μ (slice Xo Yo P) l = (Xo 0 - Xo 1)⁻¹ * Xo l := by
  have ha : (Xo 0 - Xo 1)⁻¹ * (Xo 0 - Xo 1) = 1 := inv_mul_cancel₀ h01
  rw [Fin.sum_univ_four] at hcom
  have h0 : X μ (slice Xo Yo P) 0 = (Xo 0 - Xo 1)⁻¹ * Xo 0 := by
    show (Xo 0 - Xo 1)⁻¹ * Xo 1 + 1 = (Xo 0 - Xo 1)⁻¹ * Xo 0
    linear_combination -ha
  fin_cases l
  · exact h0
  · rfl
  · rfl
  · show -(μ 0 * ((Xo 0 - Xo 1)⁻¹ * Xo 1 + 1) + μ 1 * ((Xo 0 - Xo 1)⁻¹ * Xo 1) +
        μ 2 * ((Xo 0 - Xo 1)⁻¹ * Xo 2)) / μ 3 = (Xo 0 - Xo 1)⁻¹ * Xo 3
    rw [div_eq_iff hμ]
    linear_combination (-(Xo 0 - Xo 1)⁻¹) * hcom + μ 0 * ha

theorem Y_slice (hμ : μ 3 ≠ 0) (hcom : ∑ k, μ k * Yo k = 0) (l : Fin 4) :
    Y μ (slice Xo Yo P) l = (Xo 0 - Xo 1) * Yo l := by
  rw [Fin.sum_univ_four] at hcom
  fin_cases l
  · rfl
  · rfl
  · rfl
  · show -(μ 0 * ((Xo 0 - Xo 1) * Yo 0) + μ 1 * ((Xo 0 - Xo 1) * Yo 1) + μ 2 * ((Xo 0 - Xo 1) * Yo 2)) / μ 3 =
        (Xo 0 - Xo 1) * Yo 3
    rw [div_eq_iff hμ]
    linear_combination (-(Xo 0 - Xo 1)) * hcom

theorem p_slice (hP : IsSymm P) {k l : Fin 4} (hkl : k ≠ l) : p (slice Xo Yo P) k l = P k l := by
  fin_cases k <;> fin_cases l <;> first | exact absurd rfl hkl | rfl | exact hP _ _

/-- **A solution of `N₄(μ)` on the slice**: if `(X, Y, P)` solves `N₄(μ)` and `μ₄ ≠ 0`, then
`slice X Y P` is a zero of `S12 μ`, with `X(slice) = X/(X₁ − X₂)`. -/
theorem S12_slice (hμ : μ 3 ≠ 0) (h : IsNSys μ Xo Yo P) : S12 μ (slice Xo Yo P) = 0 := by
  obtain ⟨hcX, hcY⟩ := isNSys_com h
  obtain ⟨hP, hXf, hYf, hd⟩ := h
  have h01 : Xo 0 - Xo 1 ≠ 0 := (distEqs_ne hd (by decide : (0 : Fin 4) ≠ 1)).2.1
  have hX := X_slice (Yo := Yo) (P := P) hμ h01 hcX
  have hY := Y_slice (Xo := Xo) (P := P) hμ hcY
  have hp : ∀ k l, k ≠ l → p (slice Xo Yo P) k l = P k l := fun k l hkl => p_slice (Yo := Yo) hP hkl
  have hXeq : ∀ k, Xeq μ (slice Xo Yo P) k = 0 := fun k => by
    have hF : force μ (p (slice Xo Yo P)) (X μ (slice Xo Yo P)) k = (Xo 0 - Xo 1)⁻¹ * force μ P Xo k := by
      rw [← force_smul]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [hp k l (Finset.ne_of_mem_erase hl).symm, hX k, hX l]
    rw [Xeq_eq_force, hF, hX k, ← hXf k, sub_self]
  have hYeq : ∀ k, Yeq μ (slice Xo Yo P) k = 0 := fun k => by
    have hF : force μ (p (slice Xo Yo P)) (Y μ (slice Xo Yo P)) k = (Xo 0 - Xo 1) * force μ P Yo k := by
      rw [← force_smul]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [hp k l (Finset.ne_of_mem_erase hl).symm, hY k, hY l]
    rw [Yeq_eq_force, hF, hY k, ← hYf k, sub_self]
  have hdist : ∀ k l, k ≠ l → dist μ (slice Xo Yo P) k l = 0 := fun k l hkl => by
    have ha : (Xo 0 - Xo 1)⁻¹ * (Xo 0 - Xo 1) = 1 := inv_mul_cancel₀ h01
    rw [dist, hp k l hkl, hX k, hX l, hY k, hY l]
    linear_combination ((Xo 0 - Xo 1)⁻¹ * (Xo 0 - Xo 1)) * hd k l hkl + ha
  funext i
  fin_cases i
  exacts [hXeq 0, hXeq 1, hXeq 2, hYeq 0, hYeq 1, hYeq 2, hdist 0 1 (by decide), hdist 0 2 (by decide),
    hdist 0 3 (by decide), hdist 1 2 (by decide), hdist 1 3 (by decide), hdist 2 3 (by decide)]

end Slice

end

end CC6Full.Six.D88
