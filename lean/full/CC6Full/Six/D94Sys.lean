import CC6Full.Six.D88Gen

/-!
# Diagram 94: the systems `KC₁₂` and `KC` of §6.7 with symbolic masses

For the computations of Lemma 6.19 (`lem:d88comp`) §6.7 of the paper (`ss:d88`) uses the slice `X₁ = 1` of the
centred system `KC(μ)` and the twelve unknowns `v = (X₂, X₃, Y₁, Y₂, Y₃, Y₄, p₁₂, p₁₃, p₁₄, p₂₃, p₂₄, p₃₄)`
(`v₀, …, v₁₁` in Lean), with `X₄ = 0`. The system `KC₁₂` consists of the four `X`-equations (those of the bodies
`1, 2, 3` and the equation of the centre `0 = Σ_{l≤3} μ_l p_4l³ (X₄ − X_l)`), the `Y`-equations of the bodies `1, 2`
and the six distance equations. `KC` (on the slice) adds the `Y`-equation of body `3`. In Lean the bodies `1, …, 4`
are `0, …, 3`.

On this slice there are no denominators: the equations are polynomial in `v` and in the masses as they stand, so each
system is defined once, over any commutative ring.

* `D94.X`, `D94.Y`, `D94.p`, `D94.Xeq`, `D94.Xc`, `D94.Yeq`, `D94.dist`, `D94.KC12`, `D94.KC`: the systems for masses
  `μ : Fin 4 → R`. Over `ℂ`, at `μ = D94.μ0 = (1, 2, 3, 30)`, they are written as the system of the checks of
  Lemma 6.19 (d) (unknowns, order of the equations and the sums `Σ_l if l = k then 0 else …`), so that
  `D94.KC12 D94.μ0` and `D94.X` are definitionally equal to the system and the positions of those checks.
* `D94.map_KC12`, `D94.map_KC`, `D94.map_X3`: ring homomorphisms commute with the systems. `D94.KC12P`, `D94.KCP`:
  the systems as polynomials in `v` over `ℤ[μ]`, with the evaluation lemmas `D94.eval_KC12P`, `D94.eval_KCP` and
  `D94.eval_KCP_μ0`.
* `D94.torque_KC`: the identity `Σ_k μ_k (Y_k Xeq_k − X_k Yeq_k) = 0` of §6.7 on the slice, where `X₄ = 0` and the
  `X`-equation of body `4` is `−Xc`: `μ₃ X₃ Yeq₃ = Σ_{k≤3} μ_k Y_k Xeq_k − μ₄ Y₄ Xc − Σ_{k≤2} μ_k X_k Yeq_k`.
  `D94.KC_of_KC12`: a zero of `KC₁₂` is a zero of `KC` when `μ₃ ≠ 0`, since `X₃ ≠ 0` by the distance equation of
  `34` (§6.7: `KC₁₂` "generates the same ideal as `KC` when `μ₃` is a unit, by the same torque identity").
* `D94.slice`: a solution `(X, Y, P)` of `KC(μ)` (`IsKC`) with `X₁ ≠ 0`, moved to the slice by `X ↦ X/X₁`,
  `Y ↦ X₁ Y`, under which `KC(μ)` is invariant; `D94.KC_slice`: it is a zero of `KC`.
-/

namespace CC6Full.Six.D94

open Finset

noncomputable section

/-! ## The systems over a commutative ring -/

section Defs

variable {R : Type*} [CommRing R]

/-- The positions `X` on the slice: `X₁ = 1`, `X₂ = v₀`, `X₃ = v₁` and `X₄ = 0`. -/
def X (v : Fin 12 → R) : Fin 4 → R := ![1, v 0, v 1, 0]

/-- The positions `Y`: `Y₁ = v₂`, `Y₂ = v₃`, `Y₃ = v₄`, `Y₄ = v₅`. -/
def Y (v : Fin 12 → R) : Fin 4 → R := ![v 2, v 3, v 4, v 5]

/-- The unknowns `p_kl`: `p₁₂, p₁₃, p₁₄, p₂₃, p₂₄, p₃₄ = v₆, …, v₁₁` (symmetric, `0` on the diagonal). -/
def p (v : Fin 12 → R) : Fin 4 → Fin 4 → R :=
  ![![0, v 6, v 7, v 8], ![v 6, 0, v 9, v 10], ![v 7, v 9, 0, v 11], ![v 8, v 10, v 11, 0]]

/-- The `X`-equation of body `k`: `X_k − Σ_{l≠k} μ_l p_kl³ (X_k − X_l)`. -/
def Xeq (μ : Fin 4 → R) (v : Fin 12 → R) (k : Fin 4) : R :=
  X v k - ∑ l, if l = k then 0 else μ l * p v k l ^ 3 * (X v k - X v l)

/-- The equation of the centre: `Σ_{l≤3} μ_l p_4l³ (X₄ − X_l)`. -/
def Xc (μ : Fin 4 → R) (v : Fin 12 → R) : R :=
  ∑ l, if l = 3 then 0 else μ l * p v 3 l ^ 3 * (X v 3 - X v l)

/-- The `Y`-equation of body `k`: `Y_k − Σ_{l≠k} μ_l p_kl³ (Y_k − Y_l)`. -/
def Yeq (μ : Fin 4 → R) (v : Fin 12 → R) (k : Fin 4) : R :=
  Y v k - ∑ l, if l = k then 0 else μ l * p v k l ^ 3 * (Y v k - Y v l)

/-- The distance equation of the pair `ab`: `p_ab² (X_a − X_b)(Y_a − Y_b) − 1`. -/
def dist (v : Fin 12 → R) (a b : Fin 4) : R := p v a b ^ 2 * (X v a - X v b) * (Y v a - Y v b) - 1

/-- **The system `KC₁₂`** of §6.7: the `X`-equations of the bodies `1, 2, 3`, the equation of the centre, the
`Y`-equations of the bodies `1, 2` and the distance equations of `12, 13, 14, 23, 24, 34`. -/
def KC12 (μ : Fin 4 → R) (v : Fin 12 → R) : Fin 12 → R :=
  ![Xeq μ v 0, Xeq μ v 1, Xeq μ v 2, Xc μ v, Yeq μ v 0, Yeq μ v 1, dist v 0 1, dist v 0 2, dist v 0 3,
    dist v 1 2, dist v 1 3, dist v 2 3]

/-- **The system `KC`** of §6.7 on the slice `X₁ = 1`: the equations of `KC₁₂` (in the same order) and the
`Y`-equation of body `3` (last). -/
def KC (μ : Fin 4 → R) (v : Fin 12 → R) : Fin 13 → R :=
  ![Xeq μ v 0, Xeq μ v 1, Xeq μ v 2, Xc μ v, Yeq μ v 0, Yeq μ v 1, dist v 0 1, dist v 0 2, dist v 0 3,
    dist v 1 2, dist v 1 3, dist v 2 3, Yeq μ v 2]

/-- The positions `X₁, X₂, X₃` of the bodies `1, 2, 3` (for the binary relations of diagram `94`). -/
def X3 (v : Fin 12 → R) (l : Fin 3) : R := X v l.castSucc

/-- The first twelve equations of `KC` are those of `KC₁₂`. -/
theorem KC_castSucc (μ : Fin 4 → R) (v : Fin 12 → R) (i : Fin 12) : KC μ v i.castSucc = KC12 μ v i := by
  fin_cases i <;> rfl

/-- The last equation of `KC` is the `Y`-equation of body `3`. -/
theorem KC_last (μ : Fin 4 → R) (v : Fin 12 → R) : KC μ v (Fin.last 12) = Yeq μ v 2 := rfl

/-- The zeros of `KC` are zeros of `KC₁₂`. -/
theorem KC12_of_KC {μ : Fin 4 → R} {v : Fin 12 → R} (h : KC μ v = 0) : KC12 μ v = 0 := by
  funext i
  rw [← KC_castSucc]
  exact congrFun h _

/-- **The torque identity** of §6.7 on the slice: `Σ_k μ_k (Y_k Xeq_k − X_k Yeq_k) = 0` identically, and with
`X₄ = 0` and `Xeq₄ = −Xc` it reads `μ₃ X₃ Yeq₃ = Σ_{k≤3} μ_k Y_k Xeq_k − μ₄ Y₄ Xc − Σ_{k≤2} μ_k X_k Yeq_k`. -/
theorem torque_KC (μ : Fin 4 → R) (v : Fin 12 → R) :
    μ 2 * X v 2 * Yeq μ v 2 =
      μ 0 * Y v 0 * Xeq μ v 0 + μ 1 * Y v 1 * Xeq μ v 1 + μ 2 * Y v 2 * Xeq μ v 2 - μ 3 * Y v 3 * Xc μ v -
        μ 0 * X v 0 * Yeq μ v 0 - μ 1 * X v 1 * Yeq μ v 1 := by
  simp only [Xeq, Yeq, Xc, X, Y, p, Fin.sum_univ_four]
  simp
  ring

variable {S : Type*} [CommRing S] {F : Type*} [FunLike F R S] [RingHomClass F R S]

theorem map_X (f : F) (v : Fin 12 → R) (k : Fin 4) : f (X v k) = X (fun j => f (v j)) k := by
  fin_cases k <;> simp [X]

omit [CommRing R] [CommRing S] [RingHomClass F R S] in
theorem map_Y (f : F) (v : Fin 12 → R) (k : Fin 4) : f (Y v k) = Y (fun j => f (v j)) k := by
  fin_cases k <;> simp [Y]

theorem map_p (f : F) (v : Fin 12 → R) (k l : Fin 4) : f (p v k l) = p (fun j => f (v j)) k l := by
  fin_cases k <;> fin_cases l <;> simp [p]

theorem map_Xeq (f : F) (μ : Fin 4 → R) (v : Fin 12 → R) (k : Fin 4) :
    f (Xeq μ v k) = Xeq (fun k => f (μ k)) (fun j => f (v j)) k := by
  rw [Xeq, Xeq, map_sub, map_sum, map_X]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · exact map_zero f
  · simp only [map_mul, map_pow, map_sub, map_p, map_X]

theorem map_Xc (f : F) (μ : Fin 4 → R) (v : Fin 12 → R) :
    f (Xc μ v) = Xc (fun k => f (μ k)) (fun j => f (v j)) := by
  rw [Xc, Xc, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · exact map_zero f
  · simp only [map_mul, map_pow, map_sub, map_p, map_X]

theorem map_Yeq (f : F) (μ : Fin 4 → R) (v : Fin 12 → R) (k : Fin 4) :
    f (Yeq μ v k) = Yeq (fun k => f (μ k)) (fun j => f (v j)) k := by
  rw [Yeq, Yeq, map_sub, map_sum, map_Y]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · exact map_zero f
  · simp only [map_mul, map_pow, map_sub, map_p, map_Y]

theorem map_dist (f : F) (v : Fin 12 → R) (a b : Fin 4) :
    f (dist v a b) = dist (fun j => f (v j)) a b := by
  simp only [dist, map_sub, map_mul, map_pow, map_one, map_p, map_X, map_Y]

theorem map_KC12 (f : F) (μ : Fin 4 → R) (v : Fin 12 → R) (i : Fin 12) :
    f (KC12 μ v i) = KC12 (fun k => f (μ k)) (fun j => f (v j)) i := by
  fin_cases i <;> simp [KC12, map_Xeq, map_Xc, map_Yeq, map_dist]

theorem map_KC (f : F) (μ : Fin 4 → R) (v : Fin 12 → R) (i : Fin 13) :
    f (KC μ v i) = KC (fun k => f (μ k)) (fun j => f (v j)) i := by
  fin_cases i <;> simp [KC, map_Xeq, map_Xc, map_Yeq, map_dist]

theorem map_X3 (f : F) (v : Fin 12 → R) (l : Fin 3) : f (X3 v l) = X3 (fun j => f (v j)) l :=
  map_X f v l.castSucc

end Defs

/-! ## The polynomials over `ℤ[μ]` -/

/-- **`KC₁₂` as polynomials** in `v` over `ℤ[μ]`, `μ = (μ₁, …, μ₄)`. -/
def KC12P : Fin 12 → MvPolynomial (Fin 12) (MvPolynomial (Fin 4) ℤ) :=
  KC12 (fun k => MvPolynomial.C (MvPolynomial.X k)) MvPolynomial.X

/-- **`KC` as polynomials** in `v` over `ℤ[μ]`. -/
def KCP : Fin 13 → MvPolynomial (Fin 12) (MvPolynomial (Fin 4) ℤ) :=
  KC (fun k => MvPolynomial.C (MvPolynomial.X k)) MvPolynomial.X

theorem KCP_castSucc (i : Fin 12) : KCP i.castSucc = KC12P i := KC_castSucc _ _ i

/-- Evaluation of `KC12P`: the coefficients through `f : ℤ[μ] → R`, the unknowns at `v`. -/
theorem eval_KC12P {R : Type*} [CommRing R] (f : MvPolynomial (Fin 4) ℤ →+* R) (v : Fin 12 → R) (i : Fin 12) :
    MvPolynomial.eval v (MvPolynomial.map f (KC12P i)) = KC12 (fun k => f (MvPolynomial.X k)) v i := by
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, KC12P, map_KC12]
  simp

/-- Evaluation of `KCP`. -/
theorem eval_KCP {R : Type*} [CommRing R] (f : MvPolynomial (Fin 4) ℤ →+* R) (v : Fin 12 → R) (i : Fin 13) :
    MvPolynomial.eval v (MvPolynomial.map f (KCP i)) = KC (fun k => f (MvPolynomial.X k)) v i := by
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, KCP, map_KC]
  simp

/-! ## The masses `μ₀` -/

/-- The masses `μ₀ = (1, 2, 3, 30)` of Lemma 6.19 (`lem:d88comp`). -/
def μ0 : Fin 4 → ℂ := ![1, 2, 3, 30]

/-- The masses `(m₁, m₂, m₃) = (1, 2, 3)` of the bodies `1, 2, 3` at `μ₀`, as reals (for the sums of Lemma 6.17 (b)). -/
def μ3R : Fin 3 → ℝ := ![1, 2, 3]

theorem μ0_two_ne : μ0 2 ≠ 0 := by norm_num [μ0]

/-- `KCP` with the coefficients evaluated at `μ₀` (`μ0Z`): the equations `KC μ₀`. -/
theorem eval_KCP_μ0 (v : Fin 12 → ℂ) (i : Fin 13) :
    MvPolynomial.eval v (MvPolynomial.map ((Int.castRingHom ℂ).comp (MvPolynomial.eval μ0Z)) (KCP i)) =
      KC μ0 v i := by
  have hμ : (fun k => ((Int.castRingHom ℂ).comp (MvPolynomial.eval μ0Z)) (MvPolynomial.X k)) = μ0 := by
    funext k
    fin_cases k <;> norm_num [μ0Z, μ0]
  rw [eval_KCP, hμ]

/-! ## From `KC₁₂` to `KC` -/

/-- The distance equation of the pair `l4`, `l ≤ 3`, forces `X_l ≠ 0` (since `X₄ = 0`). -/
theorem X_ne_of_dist {v : Fin 12 → ℂ} (l : Fin 3) (h : dist v l.castSucc 3 = 0) : X v l.castSucc ≠ 0 := by
  intro h0
  rw [dist, h0, show X v 3 = 0 from rfl] at h
  simp at h

/-- **A zero of `KC₁₂` is a zero of `KC`** when `μ₃ ≠ 0` (§6.7): by the torque identity (`torque_KC`), `μ₃ X₃ Yeq₃`
lies in the ideal of `KC₁₂`, and `X₃ ≠ 0` by the distance equation of `34`. -/
theorem KC_of_KC12 {μ : Fin 4 → ℂ} (hμ : μ 2 ≠ 0) {v : Fin 12 → ℂ} (h : KC12 μ v = 0) : KC μ v = 0 := by
  have hS : ∀ i : Fin 12, KC12 μ v i = 0 := fun i => congrFun h i
  have hX : X v 2 ≠ 0 := X_ne_of_dist (v := v) 2 (hS 11)
  have e0 : Xeq μ v 0 = 0 := hS 0
  have e1 : Xeq μ v 1 = 0 := hS 1
  have e2 : Xeq μ v 2 = 0 := hS 2
  have e3 : Xc μ v = 0 := hS 3
  have e4 : Yeq μ v 0 = 0 := hS 4
  have e5 : Yeq μ v 1 = 0 := hS 5
  have key := torque_KC μ v
  rw [e0, e1, e2, e3, e4, e5] at key
  have hY : Yeq μ v 2 = 0 := by
    have h0 : μ 2 * X v 2 * Yeq μ v 2 = 0 := by
      rw [key]
      ring
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hμ hX)
  funext i
  fin_cases i
  exacts [hS 0, hS 1, hS 2, hS 3, hS 4, hS 5, hS 6, hS 7, hS 8, hS 9, hS 10, hS 11, hY]

/-! ## The equations through the force -/

theorem Xeq_eq_force (μ : Fin 4 → ℂ) (v : Fin 12 → ℂ) (k : Fin 4) :
    Xeq μ v k = X v k - force μ (p v) (X v) k := by
  rw [Xeq, force, sum_ite_eq_sum_erase]

theorem Xc_eq_force (μ : Fin 4 → ℂ) (v : Fin 12 → ℂ) : Xc μ v = force μ (p v) (X v) 3 := by
  rw [Xc, force, sum_ite_eq_sum_erase]

theorem Yeq_eq_force (μ : Fin 4 → ℂ) (v : Fin 12 → ℂ) (k : Fin 4) :
    Yeq μ v k = Y v k - force μ (p v) (Y v) k := by
  rw [Yeq, force, sum_ite_eq_sum_erase]

/-! ## Moving a solution of `KC(μ)` to the slice -/

/-- The point of the slice given by a solution `(X, Y, P)` of `KC(μ)`, after `X ↦ X/X₁`, `Y ↦ X₁ Y`:
`v = (X₂, X₃, Y₁, Y₂, Y₃, Y₄, P₁₂, P₁₃, P₁₄, P₂₃, P₂₄, P₃₄)` of the moved solution. -/
def slice (Xo Yo : Fin 4 → ℂ) (P : Fin 4 → Fin 4 → ℂ) : Fin 12 → ℂ :=
  ![(Xo 0)⁻¹ * Xo 1, (Xo 0)⁻¹ * Xo 2, Xo 0 * Yo 0, Xo 0 * Yo 1, Xo 0 * Yo 2, Xo 0 * Yo 3, P 0 1, P 0 2, P 0 3,
    P 1 2, P 1 3, P 2 3]

section Slice

variable {Xo Yo : Fin 4 → ℂ} {P : Fin 4 → Fin 4 → ℂ}

theorem X_slice (h0 : Xo 0 ≠ 0) (h3 : Xo 3 = 0) (l : Fin 4) : X (slice Xo Yo P) l = (Xo 0)⁻¹ * Xo l := by
  fin_cases l
  · exact (inv_mul_cancel₀ h0).symm
  · rfl
  · rfl
  · show (0 : ℂ) = (Xo 0)⁻¹ * Xo 3
    rw [h3, mul_zero]

theorem Y_slice (l : Fin 4) : Y (slice Xo Yo P) l = Xo 0 * Yo l := by
  fin_cases l <;> rfl

theorem p_slice (hP : IsSymm P) {k l : Fin 4} (hkl : k ≠ l) : p (slice Xo Yo P) k l = P k l := by
  fin_cases k <;> fin_cases l <;> first | exact absurd rfl hkl | rfl | exact hP _ _

/-- **A solution of `KC(μ)` on the slice**: if `(X, Y, P)` solves `KC(μ)` (`IsKC`) and `X₁ ≠ 0`, then
`slice X Y P` is a zero of `KC μ`, with `X(slice) = X/X₁` and `Y(slice) = X₁ Y`. -/
theorem KC_slice {μ : Fin 4 → ℂ} (h : IsKC μ Xo Yo P) (h0 : Xo 0 ≠ 0) : KC μ (slice Xo Yo P) = 0 := by
  obtain ⟨hP, h3, hXf, hc, hYf, hd⟩ := h
  have hX := X_slice (Yo := Yo) (P := P) h0 h3
  have hY : ∀ l, Y (slice Xo Yo P) l = Xo 0 * Yo l := Y_slice
  have hp : ∀ k l, k ≠ l → p (slice Xo Yo P) k l = P k l := fun k l hkl => p_slice (Yo := Yo) hP hkl
  have hFX : ∀ k, force μ (p (slice Xo Yo P)) (X (slice Xo Yo P)) k = (Xo 0)⁻¹ * force μ P Xo k := fun k => by
    rw [← force_smul]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [hp k l (Finset.ne_of_mem_erase hl).symm, hX k, hX l]
  have hFY : ∀ k, force μ (p (slice Xo Yo P)) (Y (slice Xo Yo P)) k = Xo 0 * force μ P Yo k := fun k => by
    rw [← force_smul]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [hp k l (Finset.ne_of_mem_erase hl).symm, hY k, hY l]
  have hXeq : ∀ k, k ≠ 3 → Xeq μ (slice Xo Yo P) k = 0 := fun k hk => by
    rw [Xeq_eq_force, hFX, hX k, ← hXf k hk, sub_self]
  have hXc : Xc μ (slice Xo Yo P) = 0 := by
    rw [Xc_eq_force, hFX, hc, mul_zero]
  have hYeq : ∀ k, k ≠ 3 → Yeq μ (slice Xo Yo P) k = 0 := fun k hk => by
    rw [Yeq_eq_force, hFY, hY k, ← hYf k hk, sub_self]
  have hdist : ∀ k l, k ≠ l → dist (slice Xo Yo P) k l = 0 := fun k l hkl => by
    have ha : (Xo 0)⁻¹ * Xo 0 = 1 := inv_mul_cancel₀ h0
    rw [dist, hp k l hkl, hX k, hX l, hY k, hY l]
    linear_combination ((Xo 0)⁻¹ * Xo 0) * hd k l hkl + ha
  funext i
  fin_cases i
  exacts [hXeq 0 (by decide), hXeq 1 (by decide), hXeq 2 (by decide), hXc, hYeq 0 (by decide),
    hYeq 1 (by decide), hdist 0 1 (by decide), hdist 0 2 (by decide), hdist 0 3 (by decide),
    hdist 1 2 (by decide), hdist 1 3 (by decide), hdist 2 3 (by decide), hYeq 2 (by decide)]

end Slice

end

end CC6Full.Six.D94
