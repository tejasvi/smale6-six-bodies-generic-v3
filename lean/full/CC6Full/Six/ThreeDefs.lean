import CC6Full.Six.Systems
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Complex central configurations of three bodies: the polynomials of Lemma 6.9 (`lem:three`)

§6.4 (`ss:three`). For masses `μ = (μ₁, μ₂, μ₃)` with total mass `M_μ = μ₁ + μ₂ + μ₃` (`Mμ`):

* `ellP μ k` is `ℓ_k(t)`: `ℓ₁ = μ₂ + μ₃ t`, `ℓ₂ = ℓ₁ − M_μ`, `ℓ₃ = ℓ₁ − M_μ t`; `LamP μ k` is
  `Λ_k = ∏_{k' ≠ k} ℓ_{k'}`;
* `N01`, `N10`, `N11` are the quartics `N₀₁ = t⁴ − 5t³ + 9t² − 5t + 1`, `N₁₀ = t⁴ + t³ − 2t + 1`,
  `N₁₁ = t⁴ − 2t³ + t + 1`;
* `Qσ μ a b c` is the quintic `Q_σ(x)` for the sign pattern `σ = (σ₁₂, σ₁₃, σ₂₃) = (a, b, c)`, written out as an
  explicit polynomial; `Qσ_eval_eq` checks it against the paper's definition `x²(1+x)²(x(F₁ − F₂) − (F₂ − F₃))`,
  `F_k = Σ_{l≠k} μ_l σ_kl z_kl⁻²` with `z₁₂ = 1`, `z₂₃ = x`, `z₁₃ = 1 + x` and `σ_lk = −σ_kl` (`Fσ`);
* `Sμ μ` is `S_μ(t) = (t² − t + 1) N₀₁(t) N₁₀(t) N₁₁(t) ∏_σ Q_σ(t − 1)`, the product over the four classes
  `σ ∈ {(1,1,1), (1,1,−1), (1,−1,−1), (1,−1,1)}` of signs modulo `±1`;
* `SZ` is the integer-coefficient version, in `ℤ[μ₁, μ₂, μ₃][t]`: its specialization at `μ` is `S_μ` (`SZ_map`),
  its coefficient of `t³⁴` is `(μ₁ + μ₂)⁴` (`SZ_coeff_34`) and its higher coefficients vanish (`SZ_coeff_of_lt`).

The polynomials are defined over any commutative ring `R`; for `μ : Fin 3 → ℂ` they are the polynomials of §6.4
in `ℂ[t]`. Bodies are numbered `0, 1, 2` (body `k` of the paper is `k − 1`), so `μ 0, μ 1, μ 2` are `μ₁, μ₂, μ₃`.

The file also contains the two finite computations of the proof of Lemma 6.9: the Lagrange quadratics
`t² − (1 + j^b − j^c) t + j^b` with `j = e^{2πi/3}` (`lagQuad`, `lagQuad_root`), and the reduction of a sign
pattern `σ ∈ {±1}³` to one of the four classes (`Qσ_classes`). The lemma itself is in `CC6Full.Six.Three`.
-/

namespace CC6Full.Six

open Polynomial Finset

noncomputable section

/-- The three cases of `Fin 3`. -/
theorem fin3_cases (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  revert k
  decide

/-! ## The polynomials of §6.4 -/

section Defs

variable {R : Type*} [CommRing R]

/-- The total mass `M_μ = μ₁ + μ₂ + μ₃` of §6.4 (Lemma 6.9). -/
def Mμ (μ : Fin 3 → R) : R := μ 0 + μ 1 + μ 2

/-- `ℓ_k(t)` of §6.4 (Lemma 6.9): `ℓ₁ = μ₂ + μ₃ t`, `ℓ₂ = ℓ₁ − M_μ` and `ℓ₃ = ℓ₁ − M_μ t` are `ellP μ 0, 1, 2`. -/
def ellP (μ : Fin 3 → R) : Fin 3 → R[X] :=
  ![C (μ 1) + C (μ 2) * X, C (μ 1) + C (μ 2) * X - C (Mμ μ), C (μ 1) + C (μ 2) * X - C (Mμ μ) * X]

/-- `Λ_k = ∏_{k' ≠ k} ℓ_{k'}` of §6.4 (Lemma 6.9). -/
def LamP (μ : Fin 3 → R) (k : Fin 3) : R[X] := ∏ k' ∈ univ.erase k, ellP μ k'

/-- The quartic `N₀₁ = t⁴ − 5t³ + 9t² − 5t + 1` of §6.4 (Lemma 6.9). -/
def N01 : R[X] := X ^ 4 - 5 * X ^ 3 + 9 * X ^ 2 - 5 * X + 1

/-- The quartic `N₁₀ = t⁴ + t³ − 2t + 1` of §6.4 (Lemma 6.9). -/
def N10 : R[X] := X ^ 4 + X ^ 3 - 2 * X + 1

/-- The quartic `N₁₁ = t⁴ − 2t³ + t + 1` of §6.4 (Lemma 6.9). -/
def N11 : R[X] := X ^ 4 - 2 * X ^ 3 + X + 1

/-- The quintic `Q_σ(x)` of §6.4 (Lemma 6.9) for the sign pattern `σ = (σ₁₂, σ₁₃, σ₂₃) = (a, b, c)`, written out:
`(μ₁ + μ₂)σ₁₂ x³(1+x)² + μ₁σ₁₂ x²(1+x)² + μ₃σ₁₃ x³ − μ₁σ₁₃ x² − μ₃σ₂₃ x(1+x)² − (μ₂ + μ₃)σ₂₃ (1+x)²`.
This is the paper's `x²(1+x)²(x(F₁ − F₂) − (F₂ − F₃))` (`Qσ_eval_eq`). -/
def Qσ (μ : Fin 3 → R) (a b c : R) : R[X] :=
  C ((μ 0 + μ 1) * a) * X ^ 3 * (1 + X) ^ 2 + C (μ 0 * a) * X ^ 2 * (1 + X) ^ 2 + C (μ 2 * b) * X ^ 3
    - C (μ 0 * b) * X ^ 2 - C (μ 2 * c) * X * (1 + X) ^ 2 - C ((μ 1 + μ 2) * c) * (1 + X) ^ 2

/-- `S_μ(t) = (t² − t + 1) N₀₁(t) N₁₀(t) N₁₁(t) ∏_σ Q_σ(t − 1)` of §6.4 (Lemma 6.9), the product over the four
classes `σ = (1,1,1), (1,1,−1), (1,−1,−1), (1,−1,1)` of signs modulo `±1`. -/
def Sμ (μ : Fin 3 → R) : R[X] :=
  (X ^ 2 - X + 1) * N01 * N10 * N11 *
    ((Qσ μ 1 1 1).comp (X - 1) * (Qσ μ 1 1 (-1)).comp (X - 1) * (Qσ μ 1 (-1) (-1)).comp (X - 1) *
      (Qσ μ 1 (-1) 1).comp (X - 1))

end Defs

/-- The integer-coefficient version of `S_μ` (§6.4, Lemma 6.9): the masses are the variables of `ℤ[μ₁, μ₂, μ₃]`. -/
def SZ : (MvPolynomial (Fin 3) ℤ)[X] := Sμ MvPolynomial.X

/-! ## Evaluations -/

section Eval

variable {R : Type*} [CommRing R]

@[simp] theorem eval_ellP_zero (μ : Fin 3 → R) (t : R) : (ellP μ 0).eval t = μ 1 + μ 2 * t := by
  simp [ellP]

@[simp] theorem eval_ellP_one (μ : Fin 3 → R) (t : R) :
    (ellP μ 1).eval t = μ 1 + μ 2 * t - Mμ μ := by
  simp [ellP]

@[simp] theorem eval_ellP_two (μ : Fin 3 → R) (t : R) :
    (ellP μ 2).eval t = μ 1 + μ 2 * t - Mμ μ * t := by
  simp [ellP]

theorem LamP_zero (μ : Fin 3 → R) : LamP μ 0 = ellP μ 1 * ellP μ 2 := by
  rw [LamP, show univ.erase (0 : Fin 3) = {1, 2} by decide, prod_pair (by decide)]

theorem LamP_one (μ : Fin 3 → R) : LamP μ 1 = ellP μ 0 * ellP μ 2 := by
  rw [LamP, show univ.erase (1 : Fin 3) = {0, 2} by decide, prod_pair (by decide)]

theorem LamP_two (μ : Fin 3 → R) : LamP μ 2 = ellP μ 0 * ellP μ 1 := by
  rw [LamP, show univ.erase (2 : Fin 3) = {0, 1} by decide, prod_pair (by decide)]

theorem eval_Qσ (μ : Fin 3 → R) (a b c x : R) : (Qσ μ a b c).eval x =
    (μ 0 + μ 1) * a * x ^ 3 * (1 + x) ^ 2 + μ 0 * a * x ^ 2 * (1 + x) ^ 2 + μ 2 * b * x ^ 3
      - μ 0 * b * x ^ 2 - μ 2 * c * x * (1 + x) ^ 2 - (μ 1 + μ 2) * c * (1 + x) ^ 2 := by
  simp only [Qσ, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow, eval_one]

theorem eval_lagProd (t : R) : ((X ^ 2 - X + 1) * N01 * N10 * N11 : R[X]).eval t =
    (t ^ 2 - t + 1) * (t ^ 4 - 5 * t ^ 3 + 9 * t ^ 2 - 5 * t + 1) * (t ^ 4 + t ^ 3 - 2 * t + 1) *
      (t ^ 4 - 2 * t ^ 3 + t + 1) := by
  simp only [N01, N10, N11, eval_mul, eval_add, eval_sub, eval_pow, eval_X, eval_one, eval_ofNat]

/-- `S_μ(t) = [(t² − t + 1) N₀₁ N₁₀ N₁₁](t) · ∏_σ Q_σ(t − 1)`. -/
theorem eval_Sμ (μ : Fin 3 → R) (t : R) : (Sμ μ).eval t =
    ((X ^ 2 - X + 1) * N01 * N10 * N11 : R[X]).eval t *
      ((Qσ μ 1 1 1).eval (t - 1) * (Qσ μ 1 1 (-1)).eval (t - 1) * (Qσ μ 1 (-1) (-1)).eval (t - 1) *
        (Qσ μ 1 (-1) 1).eval (t - 1)) := by
  simp only [Sμ, eval_mul, eval_comp, eval_sub, eval_X, eval_one]

end Eval

/-! ## Degree and leading coefficient -/

section Top

variable {R : Type*} [CommRing R]

/-- `f` has degree at most `d`, with coefficient `a` in degree `d`. -/
def TopCoeff (f : R[X]) (d : ℕ) (a : R) : Prop := f.natDegree ≤ d ∧ f.coeff d = a

namespace TopCoeff

variable {f g : R[X]} {m n d : ℕ} {a b : R}

theorem mul (hf : TopCoeff f m a) (hg : TopCoeff g n b) : TopCoeff (f * g) (m + n) (a * b) :=
  ⟨natDegree_mul_le_of_le hf.1 hg.1, by rw [coeff_mul_add_eq_of_natDegree_le hf.1 hg.1, hf.2, hg.2]⟩

theorem add (hf : TopCoeff f d a) (hg : TopCoeff g d b) : TopCoeff (f + g) d (a + b) :=
  ⟨natDegree_add_le_of_degree_le hf.1 hg.1, by rw [coeff_add, hf.2, hg.2]⟩

theorem sub (hf : TopCoeff f d a) (hg : TopCoeff g d b) : TopCoeff (f - g) d (a - b) :=
  ⟨(natDegree_sub_le f g).trans (max_le hf.1 hg.1), by rw [coeff_sub, hf.2, hg.2]⟩

theorem of_lt {e : ℕ} (h : f.natDegree ≤ d) (hde : d < e) : TopCoeff f e 0 :=
  ⟨h.trans hde.le, coeff_eq_zero_of_natDegree_lt (h.trans_lt hde)⟩

theorem congr (h : TopCoeff f d a) {d' : ℕ} {a' : R} (hd : d = d') (ha : a = a') : TopCoeff f d' a' := by
  subst hd ha
  exact h

/-- The substitution `t ↦ t − 1` keeps the degree bound and the coefficient in that degree. -/
theorem comp_X_sub_one (h : TopCoeff f d a) : TopCoeff (f.comp (X - 1)) d a := by
  have e : f.comp (X - 1) = taylor (-1) f := by
    rw [taylor_apply, C_neg, C_1, ← sub_eq_add_neg]
  rw [e]
  refine ⟨(natDegree_taylor f (-1)).le.trans h.1, ?_⟩
  rcases h.1.lt_or_eq with hlt | heq
  · have h1 : (taylor (-1) f).natDegree < d := by rwa [natDegree_taylor]
    rw [coeff_eq_zero_of_natDegree_lt h1, ← h.2, coeff_eq_zero_of_natDegree_lt hlt]
  · subst heq
    rw [coeff_taylor_natDegree]
    exact h.2

end TopCoeff

theorem topCoeff_C (k : R) : TopCoeff (C k) 0 k := ⟨(natDegree_C k).le, coeff_C_zero⟩

theorem topCoeff_X_pow (n : ℕ) : TopCoeff (X ^ n : R[X]) n 1 := ⟨natDegree_X_pow_le n, coeff_X_pow_self n⟩

theorem topCoeff_one_add_X_sq : TopCoeff ((1 + X) ^ 2 : R[X]) 2 1 :=
  ⟨by compute_degree, by rw [coeff_one_add_X_pow]; simp⟩

theorem topCoeff_quad : TopCoeff (X ^ 2 - X + 1 : R[X]) 2 1 :=
  ⟨by compute_degree, by simp [coeff_X, coeff_one]⟩

theorem topCoeff_N01 : TopCoeff (N01 : R[X]) 4 1 :=
  ⟨by unfold N01; compute_degree, by simp [N01, coeff_X, coeff_one]⟩

theorem topCoeff_N10 : TopCoeff (N10 : R[X]) 4 1 :=
  ⟨by unfold N10; compute_degree, by simp [N10, coeff_X, coeff_one]⟩

theorem topCoeff_N11 : TopCoeff (N11 : R[X]) 4 1 :=
  ⟨by unfold N11; compute_degree, by simp [N11, coeff_X, coeff_one]⟩

theorem topCoeff_Qσ (μ : Fin 3 → R) (a b c : R) : TopCoeff (Qσ μ a b c) 5 ((μ 0 + μ 1) * a) := by
  have h1 : TopCoeff (C ((μ 0 + μ 1) * a) * X ^ 3 * (1 + X) ^ 2) 5 ((μ 0 + μ 1) * a) :=
    (((topCoeff_C _).mul (topCoeff_X_pow 3)).mul topCoeff_one_add_X_sq).congr rfl (by ring)
  have h2 : TopCoeff (C (μ 0 * a) * X ^ 2 * (1 + X) ^ 2) 5 0 :=
    TopCoeff.of_lt (d := 4) (by compute_degree) (by norm_num)
  have h3 : TopCoeff (C (μ 2 * b) * X ^ 3) 5 0 := TopCoeff.of_lt (d := 3) (by compute_degree) (by norm_num)
  have h4 : TopCoeff (C (μ 0 * b) * X ^ 2) 5 0 := TopCoeff.of_lt (d := 2) (by compute_degree) (by norm_num)
  have h5 : TopCoeff (C (μ 2 * c) * X * (1 + X) ^ 2) 5 0 :=
    TopCoeff.of_lt (d := 3) (by compute_degree) (by norm_num)
  have h6 : TopCoeff (C ((μ 1 + μ 2) * c) * (1 + X) ^ 2) 5 0 :=
    TopCoeff.of_lt (d := 2) (by compute_degree) (by norm_num)
  exact (((((h1.add h2).add h3).sub h4).sub h5).sub h6).congr rfl (by ring)

/-- `S_μ` has degree at most `34`, with coefficient `(μ₁ + μ₂)⁴` in degree `34`. -/
theorem topCoeff_Sμ (μ : Fin 3 → R) : TopCoeff (Sμ μ) 34 ((μ 0 + μ 1) ^ 4) := by
  have hQ : ∀ a b c : R, TopCoeff ((Qσ μ a b c).comp (X - 1)) 5 ((μ 0 + μ 1) * a) :=
    fun a b c => (topCoeff_Qσ μ a b c).comp_X_sub_one
  have h := (((topCoeff_quad.mul topCoeff_N01).mul topCoeff_N10).mul topCoeff_N11).mul
    ((((hQ 1 1 1).mul (hQ 1 1 (-1))).mul (hQ 1 (-1) (-1))).mul (hQ 1 (-1) 1))
  exact h.congr rfl (by ring)

theorem natDegree_Sμ_le (μ : Fin 3 → R) : (Sμ μ).natDegree ≤ 34 := (topCoeff_Sμ μ).1

/-- The coefficient of `t³⁴` in `S_μ` is `(μ₁ + μ₂)⁴` (§6.4). -/
theorem coeff_Sμ_34 (μ : Fin 3 → R) : (Sμ μ).coeff 34 = (μ 0 + μ 1) ^ 4 := (topCoeff_Sμ μ).2

theorem coeff_Sμ_of_lt (μ : Fin 3 → R) {n : ℕ} (hn : 34 < n) : (Sμ μ).coeff n = 0 :=
  coeff_eq_zero_of_natDegree_lt ((natDegree_Sμ_le μ).trans_lt hn)

end Top

/-! ## The integer-coefficient version -/

section Map

variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_Qσ (f : R →+* S) (μ : Fin 3 → R) (a b c : R) :
    (Qσ μ a b c).map f = Qσ (f ∘ μ) (f a) (f b) (f c) := by
  simp only [Qσ, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_C,
    Polynomial.map_X, Polynomial.map_one, map_add, map_mul, Function.comp_apply]

theorem map_N01 (f : R →+* S) : (N01 : R[X]).map f = N01 := by
  simp only [N01, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat]

theorem map_N10 (f : R →+* S) : (N10 : R[X]).map f = N10 := by
  simp only [N10, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat]

theorem map_N11 (f : R →+* S) : (N11 : R[X]).map f = N11 := by
  simp only [N11, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat]

theorem map_Sμ (f : R →+* S) (μ : Fin 3 → R) : (Sμ μ).map f = Sμ (f ∘ μ) := by
  simp only [Sμ, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_one, Polynomial.map_comp, map_Qσ, map_N01, map_N10, map_N11, map_one,
    map_neg]

end Map

/-- The specialization of `SZ` at `μ` is `S_μ`. -/
theorem SZ_map (μ : Fin 3 → ℂ) : SZ.map (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) μ) = Sμ μ := by
  rw [SZ, map_Sμ]
  congr 1
  funext k
  simp

theorem natDegree_SZ_le : SZ.natDegree ≤ 34 := natDegree_Sμ_le _

/-- The coefficient of `t³⁴` in `SZ` is `(μ₁ + μ₂)⁴`. -/
theorem SZ_coeff_34 : SZ.coeff 34 = (MvPolynomial.X 0 + MvPolynomial.X 1) ^ 4 := coeff_Sμ_34 _

/-- The coefficients of `SZ` above `t³⁴` vanish. -/
theorem SZ_coeff_of_lt {n : ℕ} (hn : 34 < n) : SZ.coeff n = 0 := coeff_Sμ_of_lt _ hn

/-! ## The paper's definition of `Q_σ` -/

section Check

/-- The slice of §6.4: the positions `(1 + x, x, 0)`, so that `z₁₂ = 1`, `z₂₃ = x` and `z₁₃ = 1 + x`. -/
def zsl (x : ℂ) : Fin 3 → ℂ := ![1 + x, x, 0]

/-- The antisymmetric sign pattern with `σ₁₂ = a`, `σ₁₃ = b`, `σ₂₃ = c` and `σ_lk = −σ_kl`. -/
def sgnPat (a b c : ℂ) : Fin 3 → Fin 3 → ℂ := ![![0, a, b], ![-a, 0, c], ![-b, -c, 0]]

/-- `F_k = Σ_{l≠k} μ_l σ_kl z_kl⁻²` on the slice (§6.4, Lemma 6.9). -/
def Fσ (μ : Fin 3 → ℂ) (a b c x : ℂ) (k : Fin 3) : ℂ :=
  ∑ l ∈ univ.erase k, μ l * sgnPat a b c k l / (zsl x k - zsl x l) ^ 2

theorem Fσ_zero (μ : Fin 3 → ℂ) (a b c x : ℂ) : Fσ μ a b c x 0 = μ 1 * a + μ 2 * b / (1 + x) ^ 2 := by
  rw [Fσ, sum_erase_eq_sub (mem_univ _), Fin.sum_univ_three]
  simp [zsl, sgnPat]

theorem Fσ_one (μ : Fin 3 → ℂ) (a b c x : ℂ) : Fσ μ a b c x 1 = -(μ 0 * a) + μ 2 * c / x ^ 2 := by
  rw [Fσ, sum_erase_eq_sub (mem_univ _), Fin.sum_univ_three]
  simp [zsl, sgnPat]

theorem Fσ_two (μ : Fin 3 → ℂ) (a b c x : ℂ) :
    Fσ μ a b c x 2 = -(μ 0 * b) / (1 + x) ^ 2 - μ 1 * c / x ^ 2 := by
  rw [Fσ, sum_erase_eq_sub (mem_univ _), Fin.sum_univ_three]
  simp [zsl, sgnPat]
  ring

/-- The explicit `Q_σ` is the paper's `x²(1+x)²(x(F₁ − F₂) − (F₂ − F₃))` (§6.4, Lemma 6.9). -/
theorem Qσ_eval_eq (μ : Fin 3 → ℂ) (a b c : ℂ) {x : ℂ} (hx : x ≠ 0) (hx1 : 1 + x ≠ 0) :
    (Qσ μ a b c).eval x =
      x ^ 2 * (1 + x) ^ 2 * (x * (Fσ μ a b c x 0 - Fσ μ a b c x 1) - (Fσ μ a b c x 1 - Fσ μ a b c x 2)) := by
  rw [eval_Qσ, Fσ_zero, Fσ_one, Fσ_two]
  field_simp
  ring

end Check

/-! ## The Lagrange quadratics -/

section Lagrange

/-- `j = e^{2πi/3}`, a primitive cube root of unity (proof of Lemma 6.9). -/
def jj : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

theorem jj_prim : IsPrimitiveRoot jj 3 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  norm_num at h
  exact h

theorem jj_sq_add_jj_add_one : jj ^ 2 + jj + 1 = 0 := by
  have h := jj_prim.geom_sum_eq_zero (by norm_num)
  simp only [sum_range_succ, sum_range_zero, pow_zero, pow_one, zero_add] at h
  linear_combination h

theorem jj_pow_three : jj ^ 3 = 1 := jj_prim.pow_eq_one

/-- The cube roots of unity are `1, j, j²`. -/
theorem eq_jj_pow_of_pow_three {β : ℂ} (h : β ^ 3 = 1) : ∃ b : Fin 3, β = jj ^ (b : ℕ) := by
  have h3 : (β - 1) * (β - jj) * (β - jj ^ 2) = 0 := by
    linear_combination h - (β - 1) * β * jj_sq_add_jj_add_one + (β - 1) * jj_pow_three
  rcases mul_eq_zero.1 h3 with h3 | h3
  · rcases mul_eq_zero.1 h3 with h3 | h3
    · refine ⟨0, ?_⟩
      show β = jj ^ 0
      linear_combination h3
    · refine ⟨1, ?_⟩
      show β = jj ^ 1
      linear_combination h3
  · refine ⟨2, ?_⟩
    show β = jj ^ 2
    linear_combination h3

theorem jj_pow_fin3 (b : Fin 3) : jj ^ (b : ℕ) = 1 ∨ jj ^ (b : ℕ) = jj ∨ jj ^ (b : ℕ) = jj ^ 2 := by
  rcases fin3_cases b with rfl | rfl | rfl
  · left
    show jj ^ 0 = 1
    exact pow_zero _
  · right; left
    show jj ^ 1 = jj
    exact pow_one _
  · right; right
    rfl

/-- The quadratic `t² − (1 + j^b − j^c) t + j^b` of the Lagrange case of Lemma 6.9. -/
def lagQuad (b c : Fin 3) : ℂ[X] := X ^ 2 - C (1 + jj ^ (b : ℕ) - jj ^ (c : ℕ)) * X + C (jj ^ (b : ℕ))

theorem eval_lagQuad (b c : Fin 3) (t : ℂ) :
    (lagQuad b c).eval t = t ^ 2 - (1 + jj ^ (b : ℕ) - jj ^ (c : ℕ)) * t + jj ^ (b : ℕ) := by
  simp only [lagQuad, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]

/-- Lemma 6.9, the Lagrange case: a root of `t² − (1 + j^b − j^c) t + j^b` is a root of
`(t² − t + 1) N₀₁ N₁₀ N₁₁`. The classes `(0,0)`, `(1,2)`, `(2,1)` give `t² − t + 1` (the last two have the double
roots `−j²` and `−j`), and the three pairs of conjugate classes `{(0,1), (0,2)}`, `{(1,0), (2,0)}`,
`{(1,1), (2,2)}` give the products `N₀₁`, `N₁₀`, `N₁₁` of conjugate quadratics. -/
theorem lagQuad_root (b c : Fin 3) {t : ℂ} (h : (lagQuad b c).IsRoot t) :
    ((X ^ 2 - X + 1) * N01 * N10 * N11 : ℂ[X]).IsRoot t := by
  have hj := jj_sq_add_jj_add_one
  rw [IsRoot.def, eval_lagQuad] at h
  rw [IsRoot.def, eval_lagProd]
  rcases jj_pow_fin3 b with hb | hb | hb <;> rcases jj_pow_fin3 c with hc | hc | hc <;>
    rw [hb, hc] at h
  · -- `(b, c) = (0, 0)`: `t² − t + 1`
    rw [show t ^ 2 - t + 1 = 0 by linear_combination h]
    ring
  · -- `(0, 1)`: a factor of `N₀₁`
    rw [show t ^ 4 - 5 * t ^ 3 + 9 * t ^ 2 - 5 * t + 1 = 0 by
      linear_combination (t ^ 2 - (2 - jj ^ 2) * t + 1) * h + (-t ^ 3 + (3 - jj) * t ^ 2 - t) * hj]
    ring
  · -- `(0, 2)`: a factor of `N₀₁`
    rw [show t ^ 4 - 5 * t ^ 3 + 9 * t ^ 2 - 5 * t + 1 = 0 by
      linear_combination (t ^ 2 - (2 - jj) * t + 1) * h + (-t ^ 3 + (3 - jj) * t ^ 2 - t) * hj]
    ring
  · -- `(1, 0)`: a factor of `N₁₀`
    rw [show t ^ 4 + t ^ 3 - 2 * t + 1 = 0 by
      linear_combination (t ^ 2 - jj ^ 2 * t + jj ^ 2) * h +
        (t ^ 3 - jj * t ^ 2 + 2 * (jj - 1) * t - (jj - 1)) * hj]
    ring
  · -- `(1, 1)`: a factor of `N₁₁`
    rw [show t ^ 4 - 2 * t ^ 3 + t + 1 = 0 by
      linear_combination (t ^ 2 - t + jj ^ 2) * h + (-t ^ 2 + t + 1 - jj) * hj]
    ring
  · -- `(1, 2)`: `(t + j²)² = 0`
    have h2 : (t + jj ^ 2) ^ 2 = 0 := by linear_combination h + (t + jj ^ 2 - jj) * hj
    have h1 := (pow_eq_zero_iff two_ne_zero).1 h2
    rw [show t ^ 2 - t + 1 = 0 by linear_combination (t - jj ^ 2 - 1) * h1 + (jj ^ 2 - jj + 1) * hj]
    ring
  · -- `(2, 0)`: a factor of `N₁₀`
    rw [show t ^ 4 + t ^ 3 - 2 * t + 1 = 0 by
      linear_combination (t ^ 2 - jj * t + jj) * h +
        (t ^ 3 - jj * t ^ 2 + 2 * (jj - 1) * t - (jj - 1)) * hj]
    ring
  · -- `(2, 1)`: `(t + j)² = 0`
    have h2 : (t + jj) ^ 2 = 0 := by linear_combination h + t * hj
    have h1 := (pow_eq_zero_iff two_ne_zero).1 h2
    rw [show t ^ 2 - t + 1 = 0 by linear_combination (t - jj - 1) * h1 + hj]
    ring
  · -- `(2, 2)`: a factor of `N₁₁`
    rw [show t ^ 4 - 2 * t ^ 3 + t + 1 = 0 by
      linear_combination (t ^ 2 - t + jj) * h + (-t ^ 2 + t + 1 - jj) * hj]
    ring

end Lagrange

/-! ## The four classes of sign patterns -/

/-- Lemma 6.9, the collinear case: `Q_{−σ} = −Q_σ`, so the patterns `σ` and `−σ` give the same solutions, and a zero
of `Q_σ` for a sign pattern `σ ∈ {±1}³` is a zero of the product over the four classes. -/
theorem Qσ_classes (μ : Fin 3 → ℂ) {a b c x : ℂ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (h : (Qσ μ a b c).eval x = 0) :
    (Qσ μ 1 1 1).eval x * (Qσ μ 1 1 (-1)).eval x * (Qσ μ 1 (-1) (-1)).eval x * (Qσ μ 1 (-1) 1).eval x = 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl
  · rw [h]; ring
  · rw [h]; ring
  · rw [h]; ring
  · rw [h]; ring
  · rw [show (Qσ μ 1 (-1) (-1)).eval x = 0 by rw [eval_Qσ] at h ⊢; linear_combination -h]
    ring
  · rw [show (Qσ μ 1 (-1) 1).eval x = 0 by rw [eval_Qσ] at h ⊢; linear_combination -h]
    ring
  · rw [show (Qσ μ 1 1 (-1)).eval x = 0 by rw [eval_Qσ] at h ⊢; linear_combination -h]
    ring
  · rw [show (Qσ μ 1 1 1).eval x = 0 by rw [eval_Qσ] at h ⊢; linear_combination -h]
    ring

end

end CC6Full.Six
