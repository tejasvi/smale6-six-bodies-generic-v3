import CC6Full.Germ.Cell
import CC6Full.Algebra.Elim

/-!
# Lemma 5.2 (b): a nonzero integer polynomial in the masses

Paper §5.1, the last step of the proof of Lemma 5.2 (b) (`lem:core`): part (a), applied after the substitution
`m_j = 1`, gives a nonzero polynomial `h₁` in the other masses with `h₁(m / m_j) = 0`, and
`m_j^{deg h₁} h₁(m / m_j)` is a nonzero polynomial in the masses that vanishes at `m`; clearing denominators gives one
with integer coefficients.

* `homogenizeAt j h`: for `h = Σ_s c_s m^s` (over any commutative semiring of coefficients) the polynomial
  `Σ_s c_s m^s m_j^{deg h − |s|}`, where `deg h` is the total degree and `|s| = Σ_i s_i`.
  `aeval_homogenizeAt`: at a point `x` with `x_j ≠ 0` it is `x_j^{deg h} h(x / x_j)`.
  `coeff_homogenizeAt`, `homogenizeAt_ne_zero`: if `h` does not involve `m_j` (`j ∉ h.vars`), the monomial `m^s` of
  `h` becomes `m^s m_j^{deg h − |s|}`, injectively in `s`, so the homogenization of a nonzero `h` is nonzero.
* The last step of Lemma 5.2 (b): `homogenizeAt_int` (`h` with integer coefficients: its homogenization) and
  `exists_int_of_aeval_div_eq_zero` (`h` with rational coefficients: a positive integer multiple of its
  homogenization, by `exists_map_int_eq_natCast_mul`).
* With `core_b`: `Germ.LiesIn.core_b` (`core_b` for a germ that lies in a cell) and `Cell.core_b_int`: if
  `Σ_i g_i f_i|_{m_j = 1} = h` for members `f_i` of an initial system written through the trees of the cell and a
  nonzero `h ∈ ℚ[m]` that does not involve `m_j`, there is a nonzero `F ∈ ℤ[m]` that vanishes at the masses of every
  germ that lies in the cell (with `m_j > 0` and the `f_i` members of its initial system). `Germ.LiesIn.core_b_theta`
  and `Cell.core_b_theta_int`: the same with the saturation by `Θ` (`core_b_theta`).
-/

namespace CC6Full

open MvPolynomial

noncomputable section

/-! ## Homogenization with respect to one variable -/

section homogenize

variable {σ R : Type*} [CommSemiring R]

/-- The homogenization of `h = Σ_s c_s m^s` with respect to the variable `m_j`: `Σ_s c_s m^s m_j^{deg h − |s|}`, where
`deg h` is the total degree of `h` and `|s| = Σ_i s_i`. At a point with `m_j ≠ 0` it is `m_j^{deg h} h(m / m_j)`
(`aeval_homogenizeAt`). -/
def homogenizeAt (j : σ) (h : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ s ∈ h.support, monomial (s + Finsupp.single j (h.totalDegree - s.sum fun _ e => e)) (h.coeff s)

/-- `homogenizeAt j h` evaluates to `x_j^{deg h} h(x / x_j)` at a point `x` with `x_j ≠ 0`. -/
theorem aeval_homogenizeAt {K : Type*} [Field K] [Algebra R K] (j : σ) (h : MvPolynomial σ R) (x : σ → K)
    (hx : x j ≠ 0) : aeval x (homogenizeAt j h) = x j ^ h.totalDegree * aeval (fun k => x k / x j) h := by
  have hh : aeval (fun k => x k / x j) h =
      ∑ s ∈ h.support, aeval (fun k => x k / x j) (monomial s (h.coeff s)) := by
    conv_lhs => rw [h.as_sum]
    rw [map_sum]
  rw [hh, homogenizeAt, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd : (s.sum fun _ e => e) ≤ h.totalDegree := le_totalDegree hs
  have hsingle : ∀ e : ℕ, ((Finsupp.single j e).prod fun i k => x i ^ k) = x j ^ e := fun e =>
    Finsupp.prod_single_index (h := fun i k => x i ^ k) (pow_zero (x j))
  have hadd : ((s + Finsupp.single j (h.totalDegree - s.sum fun _ e => e)).prod fun i k => x i ^ k) =
      (s.prod fun i k => x i ^ k) * x j ^ (h.totalDegree - s.sum fun _ e => e) := by
    rw [Finsupp.prod_add_index' (h := fun i k => x i ^ k) (fun i => pow_zero (x i))
      (fun i a b => pow_add (x i) a b), hsingle]
  have hprod : (s.prod fun i k => (x i / x j) ^ k) * x j ^ (s.sum fun _ e => e) = s.prod fun i k => x i ^ k := by
    simp only [Finsupp.prod, Finsupp.sum, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
    exact div_mul_cancel₀ _ (pow_ne_zero _ hx)
  have hxd : x j ^ h.totalDegree =
      x j ^ (h.totalDegree - s.sum fun _ e => e) * x j ^ (s.sum fun _ e => e) := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  rw [aeval_monomial, aeval_monomial, hadd, ← hprod, hxd]
  ring

/-- If `h` does not involve `m_j`, the coefficient of `m^s m_j^{deg h − |s|}` in the homogenization is the
coefficient of `m^s` in `h`. -/
theorem coeff_homogenizeAt (j : σ) {h : MvPolynomial σ R} (hj : j ∉ h.vars) {s : σ →₀ ℕ}
    (hs : s ∈ h.support) :
    (homogenizeAt j h).coeff (s + Finsupp.single j (h.totalDegree - s.sum fun _ e => e)) = h.coeff s := by
  classical
  have h0 : ∀ t ∈ h.support, t j = 0 := fun t ht => by
    by_contra hne
    exact hj ((mem_vars_iff_mem_support j).mpr ⟨t, ht, Finsupp.mem_support_iff.mpr hne⟩)
  rw [homogenizeAt, coeff_sum, Finset.sum_eq_single s]
  · rw [coeff_monomial, ite_eq_left rfl]
  · intro t ht hts
    rw [coeff_monomial, ite_eq_right]
    intro heq
    apply hts
    ext i
    by_cases hi : i = j
    · rw [hi, h0 t ht, h0 s hs]
    · have hi' := DFunLike.congr_fun heq i
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne hi, add_zero] at hi'
      exact hi'
  · intro hs'
    exact absurd hs hs'

/-- The homogenization of a nonzero polynomial that does not involve `m_j` is nonzero. -/
theorem homogenizeAt_ne_zero (j : σ) {h : MvPolynomial σ R} (hj : j ∉ h.vars) (h0 : h ≠ 0) :
    homogenizeAt j h ≠ 0 := by
  obtain ⟨s, hs⟩ := ne_zero_iff.mp h0
  intro hz
  have hc := coeff_homogenizeAt j hj (mem_support_iff.mpr hs)
  rw [hz] at hc
  exact hs (by simpa using hc.symm)

end homogenize

/-! ## The last step of Lemma 5.2 (b) -/

section laststep

variable {n : ℕ}

/-- **Lemma 5.2 (b)**, last step, for `h₁ ∈ ℤ[m]`: if `h₁` is nonzero and does not involve `m_j`, its
homogenization `m_j^{deg h₁} h₁(m / m_j)` is a nonzero polynomial with integer coefficients, and it vanishes at every
`m` with `m_j ≠ 0` and `h₁(m / m_j) = 0`. -/
theorem homogenizeAt_int (j : Fin n) {h₁ : MvPolynomial (Fin n) ℤ} (hj : j ∉ h₁.vars) (h0 : h₁ ≠ 0) :
    homogenizeAt j h₁ ≠ 0 ∧ ∀ m : Fin n → ℝ, m j ≠ 0 → aeval (fun k => m k / m j) h₁ = 0 →
      aeval m (homogenizeAt j h₁) = 0 :=
  ⟨homogenizeAt_ne_zero j hj h0, fun m hmj hm => by rw [aeval_homogenizeAt j h₁ m hmj, hm, mul_zero]⟩

/-- **Lemma 5.2 (b)**, last step, for `h₁ ∈ ℚ[m]`: if `h₁` is nonzero and does not involve `m_j`, there is a
nonzero `F ∈ ℤ[m]`, a positive integer multiple of the homogenization `m_j^{deg h₁} h₁(m / m_j)`, that vanishes at
every `m` with `m_j ≠ 0` and `h₁(m / m_j) = 0`. -/
theorem exists_int_of_aeval_div_eq_zero (j : Fin n) {h₁ : MvPolynomial (Fin n) ℚ} (hj : j ∉ h₁.vars)
    (h0 : h₁ ≠ 0) :
    ∃ F : MvPolynomial (Fin n) ℤ, F ≠ 0 ∧ (∃ D : ℕ, 0 < D ∧ map (algebraMap ℤ ℚ) F = C (D : ℚ) * homogenizeAt j h₁) ∧
      ∀ m : Fin n → ℝ, m j ≠ 0 → aeval (fun k => m k / m j) h₁ = 0 → aeval m F = 0 := by
  obtain ⟨D, F, hD, hF⟩ := exists_map_int_eq_natCast_mul (homogenizeAt j h₁)
  refine ⟨F, ?_, ⟨D, hD, hF⟩, fun m hmj hm => ?_⟩
  · rintro rfl
    rw [map_zero, eq_comm, mul_eq_zero, C_eq_zero, Nat.cast_eq_zero] at hF
    rcases hF with hc | hc
    · exact hD.ne' hc
    · exact homogenizeAt_ne_zero j hj h0 hc
  · rw [← aeval_map_algebraMap ℚ, hF, map_mul, aeval_homogenizeAt j h₁ m hmj, hm, mul_zero, mul_zero]

end laststep

/-! ## Lemma 5.2 (b) for a cell -/

section cell

variable {n : ℕ}

/-- Lemma 5.2 (b) (`core_b`) for a germ that lies in the cell `c`: the members of the initial system are written
through the trees of the cell. -/
theorem Germ.LiesIn.core_b {m : Fin n → ℝ} {G : Germ n m} {c : Cell n} (hG : G.LiesIn c) (j : Fin n)
    (hj : 0 < m j) (items : List (CoreItem n)) (gs : List (CPoly n)) (h : MvPolynomial (Fin n) ℚ)
    (hvalid : ∀ it ∈ items, it.Valid G)
    (hsum : (List.zipWith (· * ·) gs (items.map fun it => CPoly.setMassOne j (it.poly c.tz c.tw))).sum =
      MvPolynomial.rename CVar.mass h) :
    aeval (fun k => m k / m j) h = 0 := by
  obtain ⟨htz, htw, hRz, hRw, -⟩ := hG
  exact CC6Full.core_b j hj items gs h hvalid hRz hRw hsum

/-- Lemma 5.2 (b) with saturation by `Θ` (`core_b_theta`) for a germ that lies in the cell `c`. -/
theorem Germ.LiesIn.core_b_theta {m : Fin n → ℝ} {G : Germ n m} {c : Cell n} (hG : G.LiesIn c) (j : Fin n)
    (hj : 0 < m j) (items : List (CoreItem n)) (gs : List (CPoly n)) (h : MvPolynomial (Fin n) ℚ) (N : ℕ)
    (hvalid : ∀ it ∈ items, it.Valid G)
    (hsum : (List.zipWith (· * ·) gs (items.map fun it => CPoly.setMassOne j (it.poly c.tz c.tw))).sum =
      MvPolynomial.rename CVar.mass h * theta c.tz c.tw ^ N) :
    aeval (fun k => m k / m j) h = 0 := by
  obtain ⟨htz, htw, hRz, hRw, -⟩ := hG
  exact CC6Full.core_b_theta j hj items gs h N hvalid hRz hRw hsum

/-- **Lemma 5.2 (b)** (`lem:core`) for the cell `c`, with its conclusion: let `items` be members of an initial system
(initial forms of identities with argmin sets, and distance polynomials), written through the trees of `c`, and
suppose that `Σ_i g_i f_i|_{m_j = 1} = h` for polynomials `g_i` and a nonzero `h ∈ ℚ[m]` that does not involve `m_j`.
Then there is a nonzero `F ∈ ℤ[m]` (a positive integer multiple of `m_j^{deg h} h(m / m_j)`) that vanishes at the
masses `m` of every germ `G` that lies in `c`, has `m_j > 0`, and at which the items are members of the initial
system (`CoreItem.Valid`: the identities hold and the argmin sets at `G` are the given ones). -/
theorem Cell.core_b_int (c : Cell n) (j : Fin n) (items : List (CoreItem n)) (gs : List (CPoly n))
    (h : MvPolynomial (Fin n) ℚ) (hjh : j ∉ h.vars) (h0 : h ≠ 0)
    (hsum : (List.zipWith (· * ·) gs (items.map fun it => CPoly.setMassOne j (it.poly c.tz c.tw))).sum =
      MvPolynomial.rename CVar.mass h) :
    ∃ F : MvPolynomial (Fin n) ℤ, F ≠ 0 ∧ ∀ (m : Fin n → ℝ) (G : Germ n m), 0 < m j → G.LiesIn c →
      (∀ it ∈ items, it.Valid G) → aeval m F = 0 := by
  obtain ⟨F, hF0, -, hF⟩ := exists_int_of_aeval_div_eq_zero j hjh h0
  exact ⟨F, hF0, fun m G hj hG hvalid => hF m hj.ne' (hG.core_b j hj items gs h hvalid hsum)⟩

/-- **Lemma 5.2 (b)** (`lem:core`) for the cell `c` with saturation by `Θ`: the same as `Cell.core_b_int` when
`Σ_i g_i f_i|_{m_j = 1} = h Θ^N`. -/
theorem Cell.core_b_theta_int (c : Cell n) (j : Fin n) (items : List (CoreItem n)) (gs : List (CPoly n))
    (h : MvPolynomial (Fin n) ℚ) (N : ℕ) (hjh : j ∉ h.vars) (h0 : h ≠ 0)
    (hsum : (List.zipWith (· * ·) gs (items.map fun it => CPoly.setMassOne j (it.poly c.tz c.tw))).sum =
      MvPolynomial.rename CVar.mass h * theta c.tz c.tw ^ N) :
    ∃ F : MvPolynomial (Fin n) ℤ, F ≠ 0 ∧ ∀ (m : Fin n → ℝ) (G : Germ n m), 0 < m j → G.LiesIn c →
      (∀ it ∈ items, it.Valid G) → aeval m F = 0 := by
  obtain ⟨F, hF0, -, hF⟩ := exists_int_of_aeval_div_eq_zero j hjh h0
  exact ⟨F, hF0, fun m G hj hG hvalid => hF m hj.ne' (hG.core_b_theta j hj items gs h N hvalid hsum)⟩

end cell

end

end CC6Full
