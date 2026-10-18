import Lean6.Special.D98.UPolySem

/-!
# The three-body shapes of Sec. 6.4 (Lemma 6.9, `lem:three`)

Definitions in any commutative ring `R`, following Sec. 6.4: the positions `ℓ₁ = μ₂ + μ₃t`, `ℓ₂ = ℓ₁ − M`,
`ℓ₃ = ℓ₁ − Mt` (`M = μ₁ + μ₂ + μ₃`), `Λ_k = ∏_{k' ≠ k} ℓ_{k'}`, the Lagrange factors `t² − t + 1`, `N₀₁`, `N₁₀`, `N₁₁`,
the collinear quintics `Q_σ` and `S_μ(t) = (t² − t + 1) N₀₁ N₁₀ N₁₁ ∏_σ Q_σ(t − 1)` (masses indexed by `Fin 3`, so
`μ 0 = μ₁`).

* `lq_*`, `lagrange_shape`: the computation in the Lagrange case of the proof of Lemma 6.9. With `ω² + ω + 1 = 0`, the
  quadratic `t² − (1 + ω^b − ω^c) t + ω^b` of the class `(b, c)` is `t² − t + 1` for `(0,0)`, `(t − (1 + ω))²` for
  `(1,2)` and `(t + ω)²` for `(2,1)`, whose roots are roots of `t² − t + 1`; the products over the conjugate pairs
  `{(0,1),(0,2)}`, `{(1,0),(2,0)}`, `{(1,1),(2,2)}` are `N₀₁`, `N₁₀`, `N₁₁`.
* `Q_eq_F`: `Q_σ(x) = x²(1+x)²(x(F₁ − F₂) − (F₂ − F₃))` with `F_k = Σ_{l≠k} μ_l σ_{kl} z_{kl}^{-2}`, `z₁₂ = 1`,
  `z₂₃ = x`, `z₁₃ = 1 + x`, `σ_{lk} = −σ_{kl}`.
* `Spol_natDegree`, `Spol_leadingCoeff`: `S_μ ∈ ℤ[μ₁, μ₂, μ₃][t]` has degree `34` and leading coefficient `(μ₁ + μ₂)⁴`.
* `toPoly_SUP`: the computable `SUP` of the checkers is `S_μ` at integer masses.
-/

namespace Lean6.Special.D98

open Polynomial Lean6.Special.Comp.D98

variable {R : Type*} [CommRing R]

/-- `M = μ₁ + μ₂ + μ₃`. -/
def Mtot (μ : Fin 3 → R) : R := μ 0 + μ 1 + μ 2

/-- `ℓ₁ = μ₂ + μ₃ t`. -/
def ell1 (μ : Fin 3 → R) (t : R) : R := μ 1 + μ 2 * t

/-- `ℓ₂ = ℓ₁ − M`. -/
def ell2 (μ : Fin 3 → R) (t : R) : R := ell1 μ t - Mtot μ

/-- `ℓ₃ = ℓ₁ − M t`. -/
def ell3 (μ : Fin 3 → R) (t : R) : R := ell1 μ t - Mtot μ * t

/-- `Λ_k = ∏_{k' ≠ k} ℓ_{k'}`. -/
def Lam (μ : Fin 3 → R) (t : R) : Fin 3 → R := ![ell2 μ t * ell3 μ t, ell1 μ t * ell3 μ t, ell1 μ t * ell2 μ t]

/-- `t² − t + 1`. -/
def lag (t : R) : R := t ^ 2 - t + 1

/-- `N₀₁ = t⁴ − 5t³ + 9t² − 5t + 1`. -/
def N01 (t : R) : R := t ^ 4 - 5 * t ^ 3 + 9 * t ^ 2 - 5 * t + 1

/-- `N₁₀ = t⁴ + t³ − 2t + 1`. -/
def N10 (t : R) : R := t ^ 4 + t ^ 3 - 2 * t + 1

/-- `N₁₁ = t⁴ − 2t³ + t + 1`. -/
def N11 (t : R) : R := t ^ 4 - 2 * t ^ 3 + t + 1

/-! ## The Lagrange case -/

/-- The quadratic of the class `(b, c)`: `t² − (1 + ω^b − ω^c) t + ω^b`. -/
def lq (ω : R) (b c : ℕ) (t : R) : R := t ^ 2 - (1 + ω ^ b - ω ^ c) * t + ω ^ b

theorem lq_00 (ω t : R) : lq ω 0 0 t = lag t := by simp only [lq, lag, pow_zero]; ring

section Lagrange

variable {ω : R} (hω : ω ^ 2 + ω + 1 = 0) (t : R)
include hω

theorem lq_12 : lq ω 1 2 t = (t - (1 + ω)) ^ 2 ∧ lag (1 + ω) = 0 := by
  constructor
  · simp only [lq]; linear_combination (t - 1) * hω
  · simp only [lag]; linear_combination hω

theorem lq_21 : lq ω 2 1 t = (t + ω) ^ 2 ∧ lag (-ω) = 0 := by
  constructor
  · simp only [lq]; linear_combination (-t) * hω
  · simp only [lag]; linear_combination hω

theorem lq_01_02 : lq ω 0 1 t * lq ω 0 2 t = N01 t := by
  simp only [lq, N01]; linear_combination (t * (t ^ 2 + t * ω - 3 * t + 1)) * hω

theorem lq_10_20 : lq ω 1 0 t * lq ω 2 0 t = N10 t := by
  simp only [lq, N10]; linear_combination (-(t - 1) * (t ^ 2 - t * ω + t + ω - 1)) * hω

theorem lq_11_22 : lq ω 1 1 t * lq ω 2 2 t = N11 t := by
  simp only [lq, N11]; linear_combination (t ^ 2 - t + ω - 1) * hω

theorem pow_mod_three (n : ℕ) : ω ^ n = ω ^ (n % 3) := by
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, h3, one_pow, one_mul]

/-- **The Lagrange shapes** (Lemma 6.9): in a domain, a root of the quadratic of any class `(b, c)` is a root of
`(t² − t + 1) N₀₁ N₁₀ N₁₁`. -/
theorem lagrange_shape [IsDomain R] (b c : ℕ) (h : lq ω b c t = 0) : lag t * N01 t * N10 t * N11 t = 0 := by
  have hb : lq ω b c t = lq ω (b % 3) (c % 3) t := by
    simp only [lq]; rw [pow_mod_three hω b, pow_mod_three hω c]
  rw [hb] at h
  have hb3 : b % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hc3 : c % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize b % 3 = b' at h hb3
  generalize c % 3 = c' at h hc3
  interval_cases b' <;> interval_cases c'
  · rw [lq_00] at h; simp [h]
  · have := lq_01_02 hω t; rw [h, zero_mul] at this; simp [← this]
  · have := lq_01_02 hω t; rw [h, mul_zero] at this; simp [← this]
  · have := lq_10_20 hω t; rw [h, zero_mul] at this; simp [← this]
  · have := lq_11_22 hω t; rw [h, zero_mul] at this; simp [← this]
  · obtain ⟨e, he⟩ := lq_12 hω t
    rw [e] at h
    have : t = 1 + ω := by simpa [sub_eq_zero] using h
    simp [this, he]
  · have := lq_10_20 hω t; rw [h, mul_zero] at this; simp [← this]
  · obtain ⟨e, he⟩ := lq_21 hω t
    rw [e] at h
    have : t = -ω := by simpa [add_eq_zero_iff_eq_neg] using h
    simp [this, he]
  · have := lq_11_22 hω t; rw [h, mul_zero] at this; simp [← this]

end Lagrange

/-! ## The collinear quintics -/

/-- The four classes of signs `σ = (σ₁₂, σ₁₃, σ₂₃)` modulo `±1`. -/
def sig : Fin 4 → ℤ × ℤ × ℤ := ![(1, 1, 1), (1, 1, -1), (1, -1, -1), (1, -1, 1)]

/-- `Q_σ(x)`, expanded: `(μ₁+μ₂)σ₁₂ x³(1+x)² + μ₁σ₁₂ x²(1+x)² + μ₃σ₁₃ x³ − μ₁σ₁₃ x² − μ₃σ₂₃ x(1+x)²
− (μ₂+μ₃)σ₂₃ (1+x)²`. -/
def Q (μ : Fin 3 → R) (s : ℤ × ℤ × ℤ) (x : R) : R :=
  (μ 0 + μ 1) * s.1 * x ^ 3 * (1 + x) ^ 2 + μ 0 * s.1 * x ^ 2 * (1 + x) ^ 2 + μ 2 * s.2.1 * x ^ 3 -
    μ 0 * s.2.1 * x ^ 2 - μ 2 * s.2.2 * x * (1 + x) ^ 2 - (μ 1 + μ 2) * s.2.2 * (1 + x) ^ 2

/-- The antisymmetric sign matrix of `σ = (σ₁₂, σ₁₃, σ₂₃)`. -/
def sigM (s : ℤ × ℤ × ℤ) : Fin 3 → Fin 3 → ℤ := ![![0, s.1, s.2.1], ![-s.1, 0, s.2.2], ![-s.2.1, -s.2.2, 0]]

/-- The differences `z_{kl}` with `z₁₂ = 1`, `z₂₃ = x`, `z₁₃ = 1 + x`. -/
def zM {K : Type*} [Field K] (x : K) : Fin 3 → Fin 3 → K := ![![0, 1, 1 + x], ![-1, 0, x], ![-(1 + x), -x, 0]]

/-- `F_k = Σ_{l ≠ k} μ_l σ_{kl} z_{kl}^{-2}`. -/
def Fk {K : Type*} [Field K] (μ : Fin 3 → K) (s : ℤ × ℤ × ℤ) (x : K) (k : Fin 3) : K :=
  ∑ l : Fin 3, if l = k then 0 else μ l * (sigM s k l : K) * (zM x k l)⁻¹ ^ 2

/-- **`Q_σ` is the quintic of Sec. 6.4.** -/
theorem Q_eq_F {K : Type*} [Field K] (μ : Fin 3 → K) (s : ℤ × ℤ × ℤ) (x : K) (hx : x ≠ 0) (hx1 : 1 + x ≠ 0) :
    Q μ s x = x ^ 2 * (1 + x) ^ 2 * (x * (Fk μ s x 0 - Fk μ s x 1) - (Fk μ s x 1 - Fk μ s x 2)) := by
  have h0 : Fk μ s x 0 = μ 1 * s.1 + μ 2 * s.2.1 / (1 + x) ^ 2 := by
    simp [Fk, sigM, zM, Fin.sum_univ_three, div_eq_mul_inv]
  have h1 : Fk μ s x 1 = -(μ 0 * s.1) + μ 2 * s.2.2 / x ^ 2 := by
    simp [Fk, sigM, zM, Fin.sum_univ_three, div_eq_mul_inv]
  have h2 : Fk μ s x 2 = -(μ 0 * s.2.1 / (1 + x) ^ 2) - μ 1 * s.2.2 / x ^ 2 := by
    simp [Fk, sigM, zM, Fin.sum_univ_three, div_eq_mul_inv, neg_sq]
    ring
  rw [h0, h1, h2, Q]
  field_simp
  ring

/-- `S_μ(t) = (t² − t + 1) N₀₁ N₁₀ N₁₁ ∏_σ Q_σ(t − 1)`. -/
def S (μ : Fin 3 → R) (t : R) : R := lag t * N01 t * N10 t * N11 t * ∏ i : Fin 4, Q μ (sig i) (t - 1)

theorem map_S {R' : Type*} [CommRing R'] (f : R →+* R') (μ : Fin 3 → R) (t : R) :
    f (S μ t) = S (fun i => f (μ i)) (f t) := by
  simp [S, Q, lag, N01, N10, N11, map_prod, map_ofNat]

/-- `S_μ` as a polynomial over `R`. -/
noncomputable def Spol (μ : Fin 3 → R) : R[X] := S (fun i => C (μ i)) X

theorem eval_Spol (μ : Fin 3 → R) (t : R) : (Spol μ).eval t = S μ t := by
  have := map_S (evalRingHom t) (fun i => C (μ i)) X
  simpa [Spol] using this

theorem map_Spol {R' : Type*} [CommRing R'] (f : R →+* R') (μ : Fin 3 → R) :
    (Spol μ).map f = Spol (fun i => f (μ i)) := by
  have := map_S (mapRingHom f) (fun i => C (μ i)) X
  simpa [Spol] using this

end Lean6.Special.D98
