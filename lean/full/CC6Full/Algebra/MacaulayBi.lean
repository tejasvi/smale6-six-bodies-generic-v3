import CC6Full.Algebra.Macaulay
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Macaulay matrices in bidegree `(N, N)`: the bihomogeneous case of Proposition 7.11

§7.3 of the paper (`prop:C4`, `lem:transfer`, `lem:C4cert`) works on the variety `X`, the quotient of
`(ℂ² ∖ 0) × (ℂ⁷ ∖ 0)` with coordinates `(s, t)` and `(P_12, …, P_34, c)` by the action
`(λ₁, λ₂) · (s, t, P, c) = (λ₁ s, λ₁ t, λ₂ P, λ₁⁻¹ λ₂ c)` of `(ℂ*)²`, with the grading `deg s = deg t = (1, 0)`,
`deg P_kl = (0, 1)`, `deg c = (-1, 1)`. We treat the slightly more general grading on variables `x_i` (`i : α`,
degree `(1, 0)`) and `y_j` (`j : β`, degree `(-e_j, 1)` with `e_j ∈ ℕ`): `biWeight e`. For §7.3, `α = {s, t}`,
`β = {P_12, …, P_34, c}`, `e = 0` on the `P_kl` and `e c = 1`. A point of `X` is a pair `(x, y)` with `x ≠ 0` and
`y ≠ 0`, evaluated as `Sum.elim x y`.

* Item (a), `eq_zero_or_eq_zero_of_monomials_mem_ideal` (the last step of the proof of Lemma 7.10): if every
  monomial of bidegree `(N, N)` lies in the ideal of the equations, the equations have no common zero on `X`; if
  `x_i ≠ 0` and `y_j ≠ 0` then `x_i^{N + e_j N} y_j^N` (that is `s^N P_kl^N`, or `s^{2N} c^N`) has bidegree
  `(N, N)` and does not vanish. `eq_zero_or_eq_zero_of_monomials_mem_span` assumes instead that the monomials
  lie in the span of the rows `X^u f_k` of the Macaulay matrix in bidegree `(N, N)`.
* Item (b), `monomials_mem_ideal_of_charts`: from cofactor identities `1 = Σ g_k f_k` on the charts
  `x_i = y_j = 1` (`chart i j`; the 14 charts of `lem:C4cert`), over a field, every monomial of bidegree `(N, N)`
  lies in the ideal for `N` large. Each identity is homogenized to `x_i^a y_j^b ∈ I`
  (`exists_pow_mul_pow_mem_of_chart`: apply the substitution `x ↦ x/x_i`, `y_l ↦ y_l x_i^{e_l - e_j}/y_j` into the
  fraction field, which inverts the dehomogenization on bihomogeneous elements; the negative first degree of `c`
  is handled by integer powers of `x_i`), and every monomial of bidegree `(N, N)` with `N ≥ 1`,
  `N ≥ |α| a` and `N ≥ |β| b` is divisible by some `x_i^a y_j^b` (`exists_le_of_biWeight_eq`, pigeonhole: its
  `y`-degree is `N` and its `x`-degree is `N + Σ e_j b_j ≥ N`). This replaces the Nullstellensatz in the proof of
  Lemma 7.10.
* Item (c), `exists_biMacaulayMinor_ne_zero_of_charts`, `eq_zero_or_eq_zero_of_map_biMacaulayMinor_ne_zero`,
  `biMacaulay_transfer_of_charts`: the Macaulay matrix in bidegree `(N, N)` (`biMacaulay`). If all monomials of
  bidegree `(N, N)` lie in the ideal at the specialization `φ₀` into a field (for example at `μ₀`, modulo `p`),
  then they lie in the span of the rows at `φ₀` (`mem_span_rowPolys_of_mem_ideal`, taking bihomogeneous
  components), the specialized matrix has full column rank, and some maximal minor `h` has `φ₀ h ≠ 0`
  (`exists_submatrix_det_ne_zero`; `exists_biMacaulayMinor_ne_zero_of_rank` starts from a rank certificate). For
  every specialization `φ` with `φ h ≠ 0` the equations have no common zero on `X`. With coefficients in `R[μ]`
  this gives the nonzero polynomial `h(μ)` of Proposition 7.11 (`biMacaulay_transfer_poly`).
* `c4Shift`: the shifts of §7.3 on `Fin 2 ⊕ Fin 7`, with `deg s = deg t = (1, 0)`, `deg P_kl = (0, 1)` and
  `deg c = (-1, 1)` (`biWeight_c4Shift_inl`, `biWeight_c4Shift_P`, `biWeight_c4Shift_c`).
-/

namespace CC6Full

open MvPolynomial Finset

noncomputable section

variable {α β ι : Type*}

/-- The bigrading of §7.3 on the variables `x_i` (`i : α`) and `y_j` (`j : β`): `deg x_i = (1, 0)` and
`deg y_j = (-e_j, 1)`. -/
def biWeight (e : β → ℕ) : α ⊕ β → ℤ × ℤ :=
  Sum.elim (fun _ => ((1 : ℤ), (0 : ℤ))) fun j => (-(e j : ℤ), (1 : ℤ))

/-- Weighted homogeneity is preserved by specializing the coefficients. -/
theorem isWeightedHomogeneous_map {σ M A B : Type*} [CommRing A] [CommRing B]
    [AddCommMonoid M] {w : σ → M} {p : MvPolynomial σ A} {m : M} (hp : p.IsWeightedHomogeneous w m)
    (φ : A →+* B) : (map φ p).IsWeightedHomogeneous w m := by
  intro d hd
  rw [coeff_map] at hd
  exact hp fun h => hd (by rw [h, map_zero])

/-! ### Item (a): no zero on `X` -/

/-- Item (a), as in the proof of Lemma 7.10: if every monomial of bidegree `(N, N)` lies in the ideal generated
by the `f k`, then the `f k` have no common zero `(x, y)` with `x ≠ 0` and `y ≠ 0`, that is, no zero on `X`. If
`x_i ≠ 0` and `y_j ≠ 0`, the monomial `x_i^{N + e_j N} y_j^N` has bidegree `(N, N)` and does not vanish. -/
theorem eq_zero_or_eq_zero_of_monomials_mem_ideal {K : Type*} [Field K] (e : β → ℕ)
    (f : ι → MvPolynomial (α ⊕ β) K) (N : ℕ)
    (hN : ∀ v : α ⊕ β →₀ ℕ, Finsupp.weight (biWeight e) v = ((N : ℤ), (N : ℤ)) →
      monomial v (1 : K) ∈ Ideal.span (Set.range f))
    (x : α → K) (y : β → K) (hxy : ∀ k, eval (Sum.elim x y) (f k) = 0) : x = 0 ∨ y = 0 := by
  by_contra h
  rw [not_or] at h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h.1
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h.2
  have hw : Finsupp.weight (biWeight e)
      (Finsupp.single (Sum.inl i) (N + e j * N) + Finsupp.single (Sum.inr j) N) =
        ((N : ℤ), (N : ℤ)) := by
    rw [map_add, Finsupp.weight_single, Finsupp.weight_single]
    simp only [biWeight, Sum.elim_inl, Sum.elim_inr]
    ext
    · simp only [Prod.fst_add, Prod.smul_fst]
      simp only [nsmul_eq_mul, mul_one, mul_neg]
      push_cast
      ring
    · simp only [Prod.snd_add, Prod.smul_snd]
      simp only [nsmul_eq_mul, mul_one, mul_zero, zero_add]
  have h0 := eval_eq_zero_of_mem_ideal hxy (hN _ hw)
  rw [← one_mul (1 : K), ← monomial_mul_monomial, ← X_pow_eq_monomial, ← X_pow_eq_monomial, eval_mul,
    eval_pow, eval_pow, eval_X, eval_X, Sum.elim_inl, Sum.elim_inr] at h0
  exact mul_ne_zero (pow_ne_zero _ hi) (pow_ne_zero _ hj) h0

section Fintype

variable [Fintype α] [Fintype β]

/-- The bidegree of a monomial `x^a y^b` is `(|a| - Σ e_j b_j, |b|)`. -/
theorem weight_biWeight (e : β → ℕ) (v : α ⊕ β →₀ ℕ) :
    Finsupp.weight (biWeight e) v =
      (((∑ i, v (Sum.inl i) : ℕ) : ℤ) - ((∑ j, e j * v (Sum.inr j) : ℕ) : ℤ),
        ((∑ j, v (Sum.inr j) : ℕ) : ℤ)) := by
  rw [Finsupp.weight_eq_sum, Fintype.sum_sum_type]
  simp only [biWeight, Sum.elim_inl, Sum.elim_inr]
  ext
  · rw [Prod.fst_add, Prod.fst_sum, Prod.fst_sum]
    simp only [Prod.smul_fst]
    simp only [nsmul_eq_mul, mul_one]
    push_cast
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  · rw [Prod.snd_add, Prod.snd_sum, Prod.snd_sum]
    simp only [Prod.smul_snd]
    simp only [nsmul_eq_mul, mul_one, mul_zero, Finset.sum_const_zero, zero_add]
    push_cast
    rfl

/-- Pigeonhole: a monomial of bidegree `(N, N)` with `N ≥ 1`, `N ≥ |α| a` and `N ≥ |β| b` has some exponent of
an `x_i` at least `a` and some exponent of a `y_j` at least `b` (its `y`-degree is `N` and its `x`-degree is
`N + Σ e_j b_j ≥ N`). For §7.3 (`|α| = 2`, `|β| = 7`): every such monomial is divisible by one of the chart
monomials `x_i^a y_j^b`. -/
theorem exists_le_of_biWeight_eq (e : β → ℕ) {a b N : ℕ} (hN : 1 ≤ N) (ha : Fintype.card α * a ≤ N)
    (hb : Fintype.card β * b ≤ N) {v : α ⊕ β →₀ ℕ}
    (hv : Finsupp.weight (biWeight e) v = ((N : ℤ), (N : ℤ))) :
    ∃ i j, a ≤ v (Sum.inl i) ∧ b ≤ v (Sum.inr j) := by
  rw [weight_biWeight, Prod.mk.injEq] at hv
  obtain ⟨h1, h2⟩ := hv
  have h1' : ∑ i, v (Sum.inl i) = N + ∑ j, e j * v (Sum.inr j) := by omega
  have h2' : ∑ j, v (Sum.inr j) = N := by omega
  obtain ⟨j, -, hj⟩ : ∃ j ∈ (Finset.univ : Finset β), b ≤ v (Sum.inr j) := by
    apply Finset.exists_le_of_sum_le
    · rcases isEmpty_or_nonempty β with hβ | hβ
      · exfalso
        simp only [Finset.univ_eq_empty, Finset.sum_empty] at h2'
        omega
      · exact Finset.univ_nonempty
    · simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      omega
  obtain ⟨i, -, hi⟩ : ∃ i ∈ (Finset.univ : Finset α), a ≤ v (Sum.inl i) := by
    apply Finset.exists_le_of_sum_le
    · rcases isEmpty_or_nonempty α with hα | hα
      · exfalso
        simp only [Finset.univ_eq_empty, Finset.sum_empty] at h1'
        omega
      · exact Finset.univ_nonempty
    · simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      omega
  exact ⟨i, j, hi, hj⟩

variable [DecidableEq α] [DecidableEq β]

/-- If the ideal `I` contains the chart monomials `x_i^a y_j^b` for all `i, j`, it contains every monomial of
bidegree `(N, N)` for `N ≥ 1`, `N ≥ |α| a`, `N ≥ |β| b`. -/
theorem monomial_mem_of_chart_monomials_mem {K : Type*} [Field K] (e : β → ℕ)
    {I : Ideal (MvPolynomial (α ⊕ β) K)} {a b : ℕ}
    (hI : ∀ i j, X (Sum.inl i) ^ a * X (Sum.inr j) ^ b ∈ I) {N : ℕ} (hN : 1 ≤ N)
    (ha : Fintype.card α * a ≤ N) (hb : Fintype.card β * b ≤ N) {v : α ⊕ β →₀ ℕ}
    (hv : Finsupp.weight (biWeight e) v = ((N : ℤ), (N : ℤ))) : monomial v (1 : K) ∈ I := by
  obtain ⟨i, j, hi, hj⟩ := exists_le_of_biWeight_eq e hN ha hb hv
  have hle : Finsupp.single (Sum.inl i) a + Finsupp.single (Sum.inr j) b ≤ v := by
    rw [Finsupp.le_def]
    intro x
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    rcases x with x | x
    · by_cases hx : i = x
      · subst hx
        simp [hi]
      · simp [hx]
    · by_cases hx : j = x
      · subst hx
        simp [hj]
      · simp [hx]
  have hmon : monomial v (1 : K) = X (Sum.inl i) ^ a * X (Sum.inr j) ^ b *
      monomial (v - (Finsupp.single (Sum.inl i) a + Finsupp.single (Sum.inr j) b)) 1 := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, monomial_mul_monomial, one_mul, one_mul,
      add_tsub_cancel_of_le hle]
  rw [hmon]
  exact Ideal.mul_mem_right _ _ (hI i j)

end Fintype

/-! ### Item (b): from chart identities to monomials in the ideal -/

section Charts

variable [DecidableEq α] [DecidableEq β]

/-- The affine chart `x_i = 1`, `y_j = 1` of `X`: substitute `1` for the variables `x_i` and `y_j`. Its image
is the polynomial ring in the other variables (the dehomogenized ring of the chart, `F[t, P_13, …, P_34, c]` for
the chart `s = P_12 = 1` of §7.3), seen inside `F[x, y]`; a cofactor identity in that ring gives the hypothesis
`1 ∈ Ideal.span (Set.range fun k => chart i j (f k))` of `exists_pow_mul_pow_mem_of_chart` (by
`one_mem_span_of_cofactors`). -/
def chart {F : Type*} [CommRing F] (i : α) (j : β) :
    MvPolynomial (α ⊕ β) F →ₐ[F] MvPolynomial (α ⊕ β) F :=
  aeval (Sum.elim (fun i' => if i' = i then 1 else X (Sum.inl i'))
    fun j' => if j' = j then 1 else X (Sum.inr j'))

omit [DecidableEq α] [DecidableEq β] in
/-- A cofactor identity `Σ g_k p_k = 1` puts `1` into the ideal generated by the `p_k`. -/
theorem one_mem_span_of_cofactors {R : Type*} [CommRing R] [Fintype ι] {p g : ι → R}
    (h : ∑ k, g k * p k = 1) : (1 : R) ∈ Ideal.span (Set.range p) :=
  (Submodule.mem_span_range_iff_exists_fun _).mpr ⟨g, by simpa only [smul_eq_mul] using h⟩

variable {F : Type*} [Field F] (e : β → ℕ) (i : α) (j : β)

local notation "ιL" => algebraMap (MvPolynomial (α ⊕ β) F) (FractionRing (MvPolynomial (α ⊕ β) F))

omit [DecidableEq α] [DecidableEq β] in
theorem algebraMap_X_ne_zero (v : α ⊕ β) : ιL (X v) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (X_ne_zero v)

/-- The twist `x_i^{-(a + e_j b)} y_j^{-b}` of the bidegree `(a, b)`, in the fraction field. -/
def chartTwist (W : ℤ × ℤ) : FractionRing (MvPolynomial (α ⊕ β) F) :=
  ιL (X (Sum.inl i)) ^ (-(W.1 + (e j : ℤ) * W.2)) * ιL (X (Sum.inr j)) ^ (-W.2)

/-- The substitution `x_{i'} ↦ x_{i'}/x_i`, `y_{j'} ↦ y_{j'} x_i^{e_{j'} - e_j}/y_j` into the fraction field. It
sends `x_i` and `y_j` to `1`, and a polynomial of bidegree `W` to itself times `chartTwist W`. -/
def chartSubst : MvPolynomial (α ⊕ β) F →+* FractionRing (MvPolynomial (α ⊕ β) F) :=
  eval₂Hom (RingHom.comp ιL C) fun v => ιL (X v) * chartTwist (F := F) e i j (biWeight e v)

omit [DecidableEq α] [DecidableEq β] in
theorem chartTwist_zero : chartTwist (F := F) e i j 0 = 1 := by
  simp [chartTwist]

omit [DecidableEq α] [DecidableEq β] in
theorem chartTwist_add (W W' : ℤ × ℤ) :
    chartTwist (F := F) e i j (W + W') = chartTwist e i j W * chartTwist e i j W' := by
  simp only [chartTwist, Prod.fst_add, Prod.snd_add]
  rw [show -((W.1 + W'.1) + (e j : ℤ) * (W.2 + W'.2)) =
      -(W.1 + (e j : ℤ) * W.2) + -(W'.1 + (e j : ℤ) * W'.2) by ring,
    show -(W.2 + W'.2) = -W.2 + -W'.2 by ring,
    zpow_add₀ (algebraMap_X_ne_zero _), zpow_add₀ (algebraMap_X_ne_zero _)]
  ring

omit [DecidableEq α] [DecidableEq β] in
theorem chartTwist_nsmul (n : ℕ) (W : ℤ × ℤ) :
    chartTwist (F := F) e i j (n • W) = chartTwist e i j W ^ n := by
  induction n with
  | zero => simp [chartTwist_zero]
  | succ n ih => rw [succ_nsmul, chartTwist_add, ih, pow_succ]

omit [DecidableEq α] [DecidableEq β] in
theorem chartSubst_C (c : F) : chartSubst e i j (C c) = ιL (C c) := by
  simp [chartSubst]

omit [DecidableEq α] [DecidableEq β] in
theorem chartSubst_X (v : α ⊕ β) :
    chartSubst e i j (X v) = ιL (X v) * chartTwist (F := F) e i j (biWeight e v) := by
  simp [chartSubst]

omit [DecidableEq α] [DecidableEq β] in
theorem chartSubst_monomial_one (d : α ⊕ β →₀ ℕ) :
    chartSubst e i j (monomial d (1 : F)) =
      ιL (monomial d 1) * chartTwist e i j (Finsupp.weight (biWeight e) d) := by
  induction d using Finsupp.induction_linear with
  | zero => simp [chartTwist_zero]
  | add d d' hd hd' =>
    rw [show (monomial (d + d') (1 : F) : MvPolynomial (α ⊕ β) F) = monomial d 1 * monomial d' 1 by
      rw [monomial_mul_monomial, one_mul], map_mul, map_mul, hd, hd', (Finsupp.weight (biWeight e)).map_add,
      chartTwist_add]
    ring
  | single v n =>
    rw [← X_pow_eq_monomial, map_pow, map_pow, Finsupp.weight_single, chartTwist_nsmul, chartSubst_X]
    ring

omit [DecidableEq α] [DecidableEq β] in
theorem chartSubst_monomial (d : α ⊕ β →₀ ℕ) (c : F) :
    chartSubst e i j (monomial d c) =
      ιL (monomial d c) * chartTwist e i j (Finsupp.weight (biWeight e) d) := by
  rw [show (monomial d c : MvPolynomial (α ⊕ β) F) = C c * monomial d 1 by
    rw [C_mul_monomial, mul_one], map_mul, map_mul, chartSubst_monomial_one, chartSubst_C]
  ring

omit [DecidableEq α] [DecidableEq β] in
/-- On a polynomial of bidegree `W`, the substitution is multiplication by `chartTwist W`. -/
theorem chartSubst_of_isWeightedHomogeneous {p : MvPolynomial (α ⊕ β) F} {W : ℤ × ℤ}
    (hp : p.IsWeightedHomogeneous (biWeight e) W) :
    chartSubst e i j p = ιL p * chartTwist e i j W := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [chartSubst_monomial, hp (mem_support_iff.mp hd)]

/-- The substitution factors through the chart: it already sends `x_i` and `y_j` to `1`. -/
theorem chartSubst_chart (p : MvPolynomial (α ⊕ β) F) :
    chartSubst e i j (chart i j p) = chartSubst e i j p := by
  have hxi := algebraMap_X_ne_zero (F := F) (Sum.inl i : α ⊕ β)
  have hyj := algebraMap_X_ne_zero (F := F) (Sum.inr j : α ⊕ β)
  have h : (chartSubst e i j).comp (chart (F := F) i j).toRingHom = chartSubst e i j := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [chart]
    · intro v
      rcases v with i' | j'
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, chart, aeval_X,
          Sum.elim_inl]
        split_ifs with hi'
        · subst hi'
          rw [map_one, chartSubst_X]
          simp only [chartTwist, biWeight, Sum.elim_inl, mul_zero, add_zero, neg_zero, zpow_zero,
            mul_one, zpow_neg_one]
          exact (mul_inv_cancel₀ hxi).symm
        · rfl
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, chart, aeval_X,
          Sum.elim_inr]
        split_ifs with hj'
        · subst hj'
          rw [map_one, chartSubst_X]
          simp only [chartTwist, biWeight, Sum.elim_inr, mul_one, neg_add_cancel, neg_zero,
            zpow_zero, one_mul, zpow_neg_one]
          exact (mul_inv_cancel₀ hyj).symm
        · rfl
  exact RingHom.congr_fun h p

omit [DecidableEq α] [DecidableEq β] in
/-- An element of the fraction field is *clearable* if a monomial in `x_i` and `y_j` multiplies it into the
image of the polynomial ring. -/
def ChartClear (z : FractionRing (MvPolynomial (α ⊕ β) F)) : Prop :=
  ∃ (a b : ℕ) (G : MvPolynomial (α ⊕ β) F),
    ιL G = z * ιL (X (Sum.inl i)) ^ a * ιL (X (Sum.inr j)) ^ b

omit [DecidableEq α] [DecidableEq β] in
theorem chartClear_algebraMap (G : MvPolynomial (α ⊕ β) F) : ChartClear i j (ιL G) :=
  ⟨0, 0, G, by simp⟩

omit [DecidableEq α] [DecidableEq β] in
theorem ChartClear.mul {z z' : FractionRing (MvPolynomial (α ⊕ β) F)} (hz : ChartClear i j z)
    (hz' : ChartClear i j z') : ChartClear i j (z * z') := by
  obtain ⟨a, b, G, hG⟩ := hz
  obtain ⟨a', b', G', hG'⟩ := hz'
  exact ⟨a + a', b + b', G * G', by rw [map_mul, hG, hG']; ring⟩

omit [DecidableEq α] [DecidableEq β] in
theorem ChartClear.add {z z' : FractionRing (MvPolynomial (α ⊕ β) F)} (hz : ChartClear i j z)
    (hz' : ChartClear i j z') : ChartClear i j (z + z') := by
  obtain ⟨a, b, G, hG⟩ := hz
  obtain ⟨a', b', G', hG'⟩ := hz'
  refine ⟨a + a', b + b', G * X (Sum.inl i) ^ a' * X (Sum.inr j) ^ b' +
    G' * X (Sum.inl i) ^ a * X (Sum.inr j) ^ b, ?_⟩
  simp only [map_add, map_mul, map_pow, hG, hG']
  ring

omit [DecidableEq α] [DecidableEq β] in
theorem ChartClear.le {z : FractionRing (MvPolynomial (α ⊕ β) F)} {a b a' b' : ℕ}
    {G : MvPolynomial (α ⊕ β) F} (hG : ιL G = z * ιL (X (Sum.inl i)) ^ a * ιL (X (Sum.inr j)) ^ b)
    (ha : a ≤ a') (hb : b ≤ b') : ∃ G' : MvPolynomial (α ⊕ β) F,
      ιL G' = z * ιL (X (Sum.inl i)) ^ a' * ιL (X (Sum.inr j)) ^ b' := by
  refine ⟨G * X (Sum.inl i) ^ (a' - a) * X (Sum.inr j) ^ (b' - b), ?_⟩
  rw [map_mul, map_mul, hG, map_pow, map_pow, ← Nat.sub_add_cancel ha, ← Nat.sub_add_cancel hb]
  simp only [Nat.add_sub_cancel]
  ring

/-- `u^n u^{(-n)₊} = u^{n₊}` for `u ≠ 0` and `n ∈ ℤ`. -/
theorem zpow_mul_pow_toNat_neg {L : Type*} [Field L] {u : L} (hu : u ≠ 0) (n : ℤ) :
    u ^ n * u ^ (-n).toNat = u ^ n.toNat := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hu]
  congr 1
  have := Int.toNat_sub_toNat_neg n
  omega

omit [DecidableEq α] [DecidableEq β] in
theorem chartClear_zpow_x (n : ℤ) :
    ChartClear i j (ιL (X (Sum.inl i : α ⊕ β)) ^ n : FractionRing (MvPolynomial (α ⊕ β) F)) :=
  ⟨(-n).toNat, 0, X (Sum.inl i) ^ n.toNat, by
    rw [map_pow, pow_zero, mul_one, zpow_mul_pow_toNat_neg (algebraMap_X_ne_zero _)]⟩

omit [DecidableEq α] [DecidableEq β] in
theorem chartClear_zpow_y (n : ℤ) :
    ChartClear i j (ιL (X (Sum.inr j : α ⊕ β)) ^ n : FractionRing (MvPolynomial (α ⊕ β) F)) :=
  ⟨0, (-n).toNat, X (Sum.inr j) ^ n.toNat, by
    rw [map_pow, pow_zero, mul_one, zpow_mul_pow_toNat_neg (algebraMap_X_ne_zero _)]⟩

omit [DecidableEq α] [DecidableEq β] in
theorem chartClear_twist (W : ℤ × ℤ) : ChartClear i j (chartTwist (F := F) e i j W) :=
  (chartClear_zpow_x i j _).mul i j (chartClear_zpow_y i j _)

omit [DecidableEq α] [DecidableEq β] in
theorem chartClear_subst (p : MvPolynomial (α ⊕ β) F) : ChartClear i j (chartSubst e i j p) := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [chartSubst_C]; exact chartClear_algebraMap i j _
  | add p q hp hq => rw [map_add]; exact hp.add i j hq
  | mul_X p v hp =>
    rw [map_mul, chartSubst_X]
    exact hp.mul i j ((chartClear_algebraMap i j _).mul i j (chartClear_twist e i j _))

/-- Item (b), homogenization of a chart identity: if the bihomogeneous `f k` generate the unit ideal on the chart
`x_i = y_j = 1` (`1 = Σ g_k · chart i j (f k)`), then some monomial `x_i^a y_j^b` lies in the ideal of the `f k`.
-/
theorem exists_pow_mul_pow_mem_of_chart [Fintype ι] (f : ι → MvPolynomial (α ⊕ β) F)
    (wf : ι → ℤ × ℤ) (hf : ∀ k, (f k).IsWeightedHomogeneous (biWeight e) (wf k))
    (h1 : (1 : MvPolynomial (α ⊕ β) F) ∈ Ideal.span (Set.range fun k => chart i j (f k))) :
    ∃ a b : ℕ, X (Sum.inl i) ^ a * X (Sum.inr j) ^ b ∈ Ideal.span (Set.range f) := by
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h1
  have hsum : ∑ k, chartSubst e i j (g k) * chartTwist e i j (wf k) * ιL (f k) = 1 := by
    have := congrArg (chartSubst e i j) hg
    rw [map_sum, map_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_eq_mul, map_mul, chartSubst_chart, chartSubst_of_isWeightedHomogeneous e i j (hf k)]
    ring
  have hclear : ∀ k, ChartClear i j (chartSubst e i j (g k) * chartTwist e i j (wf k)) := fun k =>
    (chartClear_subst e i j (g k)).mul i j (chartClear_twist e i j (wf k))
  choose a b G hG using hclear
  have hG' : ∀ k, ∃ G' : MvPolynomial (α ⊕ β) F,
      ιL G' = chartSubst e i j (g k) * chartTwist e i j (wf k) *
        ιL (X (Sum.inl i)) ^ (∑ k, a k) * ιL (X (Sum.inr j)) ^ (∑ k, b k) := fun k =>
    ChartClear.le i j (hG k) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
  choose G' hG'' using hG'
  refine ⟨∑ k, a k, ∑ k, b k, ?_⟩
  have key : X (Sum.inl i) ^ (∑ k, a k) * X (Sum.inr j) ^ (∑ k, b k) = ∑ k, G' k * f k := by
    apply IsFractionRing.injective (MvPolynomial (α ⊕ β) F) (FractionRing (MvPolynomial (α ⊕ β) F))
    rw [map_sum, map_mul, map_pow, map_pow]
    simp only [map_mul, hG'']
    conv_lhs => rw [← one_mul (ιL (X (Sum.inl i)) ^ (∑ k, a k) * ιL (X (Sum.inr j)) ^ (∑ k, b k)),
      ← hsum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [key]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)

/-- Item (b): if the bihomogeneous `f k` generate the unit ideal on each chart `x_i = y_j = 1` (cofactor
identities over the field `F`), then every monomial of bidegree `(N, N)` lies in the ideal of the `f k`, for all
large `N`. -/
theorem monomials_mem_ideal_of_charts [Fintype α] [Fintype β] [Fintype ι]
    (f : ι → MvPolynomial (α ⊕ β) F) (wf : ι → ℤ × ℤ)
    (hf : ∀ k, (f k).IsWeightedHomogeneous (biWeight e) (wf k))
    (hcharts : ∀ i j, (1 : MvPolynomial (α ⊕ β) F) ∈ Ideal.span (Set.range fun k => chart i j (f k))) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ v : α ⊕ β →₀ ℕ,
      Finsupp.weight (biWeight e) v = ((N : ℤ), (N : ℤ)) →
        monomial v (1 : F) ∈ Ideal.span (Set.range f) := by
  have hc : ∀ ij : α × β, ∃ ab : ℕ × ℕ,
      X (Sum.inl ij.1) ^ ab.1 * X (Sum.inr ij.2) ^ ab.2 ∈ Ideal.span (Set.range f) := by
    intro ij
    obtain ⟨a, b, h⟩ := exists_pow_mul_pow_mem_of_chart e ij.1 ij.2 f wf hf (hcharts ij.1 ij.2)
    exact ⟨(a, b), h⟩
  choose ab hab using hc
  set a := Finset.univ.sup fun ij => (ab ij).1 with ha_def
  set b := Finset.univ.sup fun ij => (ab ij).2 with hb_def
  have hI : ∀ i j, X (Sum.inl i) ^ a * X (Sum.inr j) ^ b ∈ Ideal.span (Set.range f) := by
    intro i j
    have ha : (ab (i, j)).1 ≤ a := Finset.le_sup (f := fun ij => (ab ij).1) (Finset.mem_univ (i, j))
    have hb : (ab (i, j)).2 ≤ b := Finset.le_sup (f := fun ij => (ab ij).2) (Finset.mem_univ (i, j))
    rw [← pow_mul_pow_sub (X (Sum.inl i)) ha, ← pow_mul_pow_sub (X (Sum.inr j)) hb, mul_mul_mul_comm]
    exact Ideal.mul_mem_right _ _ (hab (i, j))
  refine ⟨1 + Fintype.card α * a + Fintype.card β * b, fun N hN v hv => ?_⟩
  exact monomial_mem_of_chart_monomials_mem e hI (by omega) (by omega) (by omega) hv

end Charts

/-! ### Bihomogeneous components and the span of the rows -/

section Components

/-- The component of weight `W` of `c * g`, for `g` weighted homogeneous of weight `m`, is the component of weight
`W - m` of `c`, times `g`. -/
theorem weightedHomogeneousComponent_mul_of_isWeightedHomogeneous {σ R M : Type*} [CommRing R]
    [AddCommGroup M] {w : σ → M} {g : MvPolynomial σ R} {m : M} (hg : g.IsWeightedHomogeneous w m)
    (c : MvPolynomial σ R) (W : M) :
    weightedHomogeneousComponent w W (c * g) = weightedHomogeneousComponent w (W - m) c * g := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hd
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hx1
    · rfl
    · by_cases hg2 : g.coeff x.2 = 0
      · rw [hg2, mul_zero, mul_zero]
      · exfalso
        apply hx1
        have h3 : Finsupp.weight w x.1 + Finsupp.weight w x.2 = W := by
          rw [← map_add, Finset.mem_antidiagonal.mp hx, hd]
        rw [hg hg2] at h3
        exact eq_sub_of_add_eq h3
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hx1
    · by_cases hg2 : g.coeff x.2 = 0
      · rw [hg2, mul_zero]
      · exfalso
        apply hd
        rw [← Finset.mem_antidiagonal.mp hx, map_add, hx1, hg hg2, sub_add_cancel]
    · rw [zero_mul]

/-- A weighted homogeneous element of weight `W` of the ideal of weighted homogeneous `f k` is a linear
combination of the `X^u f k` with `weight u + weight (f k) = W` (the rows of the Macaulay matrix in weight `W`). -/
theorem mem_span_rowPolys_of_mem_ideal {σ F M : Type*} [Field F] [AddCommGroup M] [DecidableEq M]
    [Fintype ι] {w : σ → M} {f : ι → MvPolynomial σ F} {wf : ι → M}
    (hf : ∀ k, (f k).IsWeightedHomogeneous w (wf k)) {W : M} {R : Finset (ι × (σ →₀ ℕ))}
    (hR : ∀ k u, Finsupp.weight w u + wf k = W → (k, u) ∈ R) {p : MvPolynomial σ F}
    (hp : p ∈ Ideal.span (Set.range f)) (hpW : p.IsWeightedHomogeneous w W) :
    p ∈ Submodule.span F (Set.range fun r : R => macaulayRowPoly f (r : ι × (σ →₀ ℕ))) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hp
  have hp' : p = ∑ k, weightedHomogeneousComponent w (W - wf k) (c k) * f k := by
    calc p = weightedHomogeneousComponent w W p := hpW.weightedHomogeneousComponent_same.symm
      _ = weightedHomogeneousComponent w W (∑ k, c k • f k) := by rw [hc]
      _ = ∑ k, weightedHomogeneousComponent w (W - wf k) (c k) * f k := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_eq_mul, weightedHomogeneousComponent_mul_of_isWeightedHomogeneous (hf k)]
  rw [hp']
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [weightedHomogeneousComponent_apply, Finset.sum_mul]
  refine Submodule.sum_mem _ fun u hu => ?_
  have hu' := (Finset.mem_filter.mp hu).2
  have hr : (k, u) ∈ R := hR k u (by rw [hu', sub_add_cancel])
  have : monomial u ((c k).coeff u) * f k = (c k).coeff u • macaulayRowPoly f (k, u) := by
    rw [macaulayRowPoly, smul_eq_C_mul, ← mul_assoc, C_mul_monomial, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨(k, u), hr⟩, rfl⟩)

/-- If every monomial of `C` is a linear combination of the polynomials of the rows, the rows of the Macaulay
matrix span `F^C` (full column rank). -/
theorem span_macaulay_rows_eq_top {σ F : Type*} [Field F] [DecidableEq σ] (f : ι → MvPolynomial σ F)
    (R : Finset (ι × (σ →₀ ℕ))) (C : Finset (σ →₀ ℕ))
    (h : ∀ c ∈ C, monomial c (1 : F) ∈
      Submodule.span F (Set.range fun r : R => macaulayRowPoly f (r : ι × (σ →₀ ℕ)))) :
    Submodule.span F (Set.range (macaulay f R C).row) = ⊤ := by
  let L : MvPolynomial σ F →ₗ[F] (C → F) := LinearMap.pi fun c => lcoeff F (c : σ →₀ ℕ)
  have hmap : Submodule.map L
      (Submodule.span F (Set.range fun r : R => macaulayRowPoly f (r : ι × (σ →₀ ℕ)))) =
        Submodule.span F (Set.range (macaulay f R C).row) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [eq_top_iff, ← hmap]
  rintro x -
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_
  refine ⟨monomial (c : σ →₀ ℕ) 1, h c c.2, ?_⟩
  funext c'
  show (monomial (c : σ →₀ ℕ) (1 : F)).coeff (c' : σ →₀ ℕ) = if c = c' then 1 else 0
  rw [coeff_monomial]
  by_cases hcc : c = c'
  · simp [hcc]
  · have hne : (c : σ →₀ ℕ) ≠ c' := fun h => hcc (Subtype.ext h)
    simp [hcc, hne]

end Components

/-! ### Item (c): the Macaulay matrix in bidegree `(N, N)` and the transfer -/

section BiMacaulay

variable [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Fintype ι]

variable (α) in
/-- The monomials of bidegree `W` (the columns of the Macaulay matrix in bidegree `W`). Their total degree is at
most `W₁ + (max e + 1) W₂`. -/
def biMonomials (e : β → ℕ) (W : ℤ × ℤ) : Finset (α ⊕ β →₀ ℕ) :=
  (monomialsUpTo (α ⊕ β) (W.1.toNat + (Finset.univ.sup e + 1) * W.2.toNat)).filter
    fun v => Finsupp.weight (biWeight e) v = W

theorem mem_biMonomials {e : β → ℕ} {W : ℤ × ℤ} {v : α ⊕ β →₀ ℕ} :
    v ∈ biMonomials α e W ↔ Finsupp.weight (biWeight e) v = W := by
  simp only [biMonomials, Finset.mem_filter, mem_monomialsUpTo, and_iff_right_iff_imp]
  intro hv
  rw [weight_biWeight] at hv
  rw [Finsupp.degree_eq_sum, Fintype.sum_sum_type]
  have hE : ∑ j, e j * v (Sum.inr j) ≤ (Finset.univ.sup e) * ∑ j, v (Sum.inr j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (Finset.le_sup (Finset.mem_univ j))
  obtain ⟨h1, h2⟩ := Prod.mk.inj hv
  have h1' := Int.self_le_toNat W.1
  have h2' : ((W.2.toNat : ℕ) : ℤ) = W.2 := Int.toNat_of_nonneg (by rw [← h2]; positivity)
  have hS : W.2.toNat = ∑ j, v (Sum.inr j) := by omega
  rw [hS, add_one_mul]
  have : (∑ i, v (Sum.inl i) : ℕ) ≤ W.1.toNat + ∑ j, e j * v (Sum.inr j) := by omega
  omega

variable (α) in
/-- The rows of the Macaulay matrix in bidegree `W` of equations of bidegrees `wf k`: the pairs `(k, u)` with `u`
a monomial of bidegree `W - wf k`. -/
def biRows (e : β → ℕ) (wf : ι → ℤ × ℤ) (W : ℤ × ℤ) : Finset (ι × (α ⊕ β →₀ ℕ)) :=
  (Finset.univ ×ˢ Finset.univ.biUnion fun k => biMonomials α e (W - wf k)).filter
    fun r => Finsupp.weight (biWeight e) r.2 + wf r.1 = W

theorem mem_biRows {e : β → ℕ} {wf : ι → ℤ × ℤ} {W : ℤ × ℤ} {r : ι × (α ⊕ β →₀ ℕ)} :
    r ∈ biRows α e wf W ↔ Finsupp.weight (biWeight e) r.2 + wf r.1 = W := by
  simp only [biRows, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_biUnion, mem_biMonomials, and_iff_right_iff_imp]
  intro h
  exact ⟨r.1, eq_sub_of_add_eq h⟩

/-- The Macaulay matrix in bidegree `(N, N)` of the equations `f k` of bidegrees `wf k`. -/
def biMacaulay {A : Type*} [CommRing A] (f : ι → MvPolynomial (α ⊕ β) A) (e : β → ℕ) (wf : ι → ℤ × ℤ)
    (N : ℕ) :
    Matrix (biRows α e wf ((N : ℤ), (N : ℤ))) (biMonomials α e ((N : ℤ), (N : ℤ))) A :=
  macaulay f (biRows α e wf ((N : ℤ), (N : ℤ))) (biMonomials α e ((N : ℤ), (N : ℤ)))

/-- The maximal minor of the Macaulay matrix in bidegree `(N, N)` with rows chosen by `S`. -/
def biMacaulayMinor {A : Type*} [CommRing A] (f : ι → MvPolynomial (α ⊕ β) A) (e : β → ℕ)
    (wf : ι → ℤ × ℤ) (N : ℕ)
    (S : biMonomials α e ((N : ℤ), (N : ℤ)) → biRows α e wf ((N : ℤ), (N : ℤ))) : A :=
  ((biMacaulay f e wf N).submatrix S id).det

theorem map_biMacaulayMinor {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (f : ι → MvPolynomial (α ⊕ β) A) (e : β → ℕ) (wf : ι → ℤ × ℤ) (N : ℕ)
    (S : biMonomials α e ((N : ℤ), (N : ℤ)) → biRows α e wf ((N : ℤ), (N : ℤ))) :
    φ (biMacaulayMinor f e wf N S) = biMacaulayMinor (fun k => map φ (f k)) e wf N S :=
  map_det_macaulay_submatrix φ f _ _ S

/-- The polynomial `X^u f k` of a row in bidegree `W` only involves monomials of bidegree `W`. -/
theorem macaulayRowPoly_mem_biMonomials {A : Type*} [CommRing A] {f : ι → MvPolynomial (α ⊕ β) A}
    {e : β → ℕ} {wf : ι → ℤ × ℤ} (hf : ∀ k, (f k).IsWeightedHomogeneous (biWeight e) (wf k))
    {W : ℤ × ℤ} (r : biRows α e wf W) :
    ∀ v ∈ (macaulayRowPoly f (r : ι × (α ⊕ β →₀ ℕ))).support, v ∈ biMonomials α e W := by
  intro v hv
  have hr := mem_biRows.mp r.2
  have hhom : (macaulayRowPoly f (r : ι × (α ⊕ β →₀ ℕ))).IsWeightedHomogeneous (biWeight e) W := by
    have := (isWeightedHomogeneous_monomial (biWeight e) (r : ι × (α ⊕ β →₀ ℕ)).2 (1 : A) rfl).mul
      (hf (r : ι × (α ⊕ β →₀ ℕ)).1)
    rwa [hr] at this
  exact mem_biMonomials.mpr (hhom (mem_support_iff.mp hv))

/-- Item (a) with the hypothesis as stated in the paper: if every monomial of bidegree `(N, N)` is a linear
combination of the polynomials `X^u f_k` of the rows of the Macaulay matrix in bidegree `(N, N)`, the `f k` have
no common zero on `X`. -/
theorem eq_zero_or_eq_zero_of_monomials_mem_span {K : Type*} [Field K] (e : β → ℕ)
    (f : ι → MvPolynomial (α ⊕ β) K) (wf : ι → ℤ × ℤ) (N : ℕ)
    (hN : ∀ v : α ⊕ β →₀ ℕ, Finsupp.weight (biWeight e) v = ((N : ℤ), (N : ℤ)) →
      monomial v (1 : K) ∈ Submodule.span K
        (Set.range fun r : biRows α e wf ((N : ℤ), (N : ℤ)) =>
          macaulayRowPoly f (r : ι × (α ⊕ β →₀ ℕ))))
    (x : α → K) (y : β → K) (hxy : ∀ k, eval (Sum.elim x y) (f k) = 0) : x = 0 ∨ y = 0 := by
  refine eq_zero_or_eq_zero_of_monomials_mem_ideal e f N (fun v hv => ?_) x y hxy
  have hle : Submodule.span K (Set.range fun r : biRows α e wf ((N : ℤ), (N : ℤ)) =>
      macaulayRowPoly f (r : ι × (α ⊕ β →₀ ℕ))) ≤ (Ideal.span (Set.range f)).restrictScalars K := by
    rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    exact macaulayRowPoly_mem_ideal f _
  exact hle (hN v hv)

/-- Item (c), the transfer: if the specialization `φ h` of a maximal minor `h` of the Macaulay matrix in bidegree
`(N, N)` is nonzero, every monomial of bidegree `(N, N)` lies in the ideal of the specialized equations, so they
have no common zero `(x, y)` with `x ≠ 0` and `y ≠ 0` (no zero on `X`). -/
theorem eq_zero_or_eq_zero_of_map_biMacaulayMinor_ne_zero {A K : Type*} [CommRing A] [Field K]
    (φ : A →+* K) (f : ι → MvPolynomial (α ⊕ β) A) (e : β → ℕ) (wf : ι → ℤ × ℤ)
    (hf : ∀ k, (f k).IsWeightedHomogeneous (biWeight e) (wf k)) (N : ℕ)
    (S : biMonomials α e ((N : ℤ), (N : ℤ)) → biRows α e wf ((N : ℤ), (N : ℤ)))
    (hS : φ (biMacaulayMinor f e wf N S) ≠ 0) (x : α → K) (y : β → K)
    (hxy : ∀ k, eval (Sum.elim x y) (map φ (f k)) = 0) : x = 0 ∨ y = 0 := by
  rw [map_biMacaulayMinor] at hS
  refine eq_zero_or_eq_zero_of_monomials_mem_ideal e (fun k => map φ (f k)) N (fun v hv => ?_) x y hxy
  exact monomial_mem_ideal_of_isUnit_det (fun k => map φ (f k)) S
    (fun c => macaulayRowPoly_mem_biMonomials (fun k => isWeightedHomogeneous_map (hf k) φ) (S c))
    (isUnit_iff_ne_zero.mpr hS) ⟨v, mem_biMonomials.mpr hv⟩

/-- Item (c), full column rank at one specialization: if at the specialization `φ₀` into a field every monomial
of bidegree `(N, N)` lies in the ideal of the specialized equations, then some maximal minor `h` of the Macaulay
matrix in bidegree `(N, N)` has `φ₀ h ≠ 0`. -/
theorem exists_biMacaulayMinor_ne_zero {A F : Type*} [CommRing A] [Field F] (φ₀ : A →+* F)
    (f : ι → MvPolynomial (α ⊕ β) A) (e : β → ℕ) (wf : ι → ℤ × ℤ)
    (hf : ∀ k, (f k).IsWeightedHomogeneous (biWeight e) (wf k)) (N : ℕ)
    (hN : ∀ v : α ⊕ β →₀ ℕ, Finsupp.weight (biWeight e) v = ((N : ℤ), (N : ℤ)) →
      monomial v (1 : F) ∈ Ideal.span (Set.range fun k => map φ₀ (f k))) :
    ∃ S : biMonomials α e ((N : ℤ), (N : ℤ)) → biRows α e wf ((N : ℤ), (N : ℤ)),
      φ₀ (biMacaulayMinor f e wf N S) ≠ 0 := by
  have hspan := span_macaulay_rows_eq_top (fun k => map φ₀ (f k)) (biRows α e wf ((N : ℤ), (N : ℤ)))
    (biMonomials α e ((N : ℤ), (N : ℤ))) fun c hc =>
      mem_span_rowPolys_of_mem_ideal (fun k => isWeightedHomogeneous_map (hf k) φ₀)
        (fun k u h => mem_biRows.mpr h) (hN c (mem_biMonomials.mp hc))
        (isWeightedHomogeneous_monomial _ _ _ (mem_biMonomials.mp hc))
  obtain ⟨S, hS⟩ := exists_submatrix_det_ne_zero _ hspan
  refine ⟨S, ?_⟩
  rw [map_biMacaulayMinor]
  exact hS

/-- Item (c) with a rank certificate: if the Macaulay matrix in bidegree `(N, N)`, specialized by `φ₀` into a
field, has rank equal to the number of monomials of bidegree `(N, N)`, some maximal minor `h` has `φ₀ h ≠ 0`. -/
theorem exists_biMacaulayMinor_ne_zero_of_rank {A F : Type*} [CommRing A] [Field F] (φ₀ : A →+* F)
    (f : ι → MvPolynomial (α ⊕ β) A) (e : β → ℕ) (wf : ι → ℤ × ℤ) (N : ℕ)
    (h : ((biMacaulay f e wf N).map φ₀).rank =
      Fintype.card (biMonomials α e ((N : ℤ), (N : ℤ)))) :
    ∃ S : biMonomials α e ((N : ℤ), (N : ℤ)) → biRows α e wf ((N : ℤ), (N : ℤ)),
      φ₀ (biMacaulayMinor f e wf N S) ≠ 0 := by
  obtain ⟨S, hS⟩ := exists_submatrix_det_ne_zero _ (span_row_eq_top_of_rank_eq _ h)
  refine ⟨S, ?_⟩
  rw [biMacaulayMinor, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map]
  exact hS

/-- Items (b) and (c) together: cofactor identities on the charts at one specialization `φ₀` into a field give a
bidegree `(N, N)` and a maximal minor `h` with `φ₀ h ≠ 0`, such that for every specialization `φ` into a field
with `φ h ≠ 0` the equations have no common zero on `X`. -/
theorem biMacaulay_transfer_of_charts {A F : Type*} [CommRing A] [Field F] (φ₀ : A →+* F)
    (f : ι → MvPolynomial (α ⊕ β) A) (e : β → ℕ) (wf : ι → ℤ × ℤ)
    (hf : ∀ k, (f k).IsWeightedHomogeneous (biWeight e) (wf k))
    (hcharts : ∀ i j, (1 : MvPolynomial (α ⊕ β) F) ∈
      Ideal.span (Set.range fun k => chart i j (map φ₀ (f k)))) :
    ∃ (N : ℕ) (S : biMonomials α e ((N : ℤ), (N : ℤ)) → biRows α e wf ((N : ℤ), (N : ℤ))),
      φ₀ (biMacaulayMinor f e wf N S) ≠ 0 ∧
        ∀ {K : Type*} [Field K] (φ : A →+* K), φ (biMacaulayMinor f e wf N S) ≠ 0 →
          ∀ (x : α → K) (y : β → K), (∀ k, eval (Sum.elim x y) (map φ (f k)) = 0) → x = 0 ∨ y = 0 := by
  obtain ⟨N₀, hN₀⟩ := monomials_mem_ideal_of_charts e (fun k => map φ₀ (f k)) wf
    (fun k => isWeightedHomogeneous_map (hf k) φ₀) hcharts
  obtain ⟨S, hS⟩ := exists_biMacaulayMinor_ne_zero φ₀ f e wf hf N₀ (hN₀ N₀ le_rfl)
  exact ⟨N₀, S, hS, fun φ hφ x y hxy =>
    eq_zero_or_eq_zero_of_map_biMacaulayMinor_ne_zero φ f e wf hf N₀ S hφ x y hxy⟩

/-- Proposition 7.11 in the form used by the formalization: equations with coefficients in `R[μ]`, bihomogeneous,
with cofactor identities on all charts at one parameter point `μ₀` over a field `F` (for example `R = ℤ`,
`F = ZMod p`, `ψ₀` the reduction). Then there is a polynomial `h ∈ R[μ]`, `h ≠ 0` and `h(μ₀) ≠ 0`, such that for
every ring map `ψ : R →+* K` into a field and every `μ ∈ K^τ` with `h(μ) ≠ 0` the equations at `μ` have no common
zero on `X`. -/
theorem biMacaulay_transfer_poly {τ R F : Type*} [CommRing R] [Field F] (ψ₀ : R →+* F) (μ₀ : τ → F)
    (f : ι → MvPolynomial (α ⊕ β) (MvPolynomial τ R)) (e : β → ℕ) (wf : ι → ℤ × ℤ)
    (hf : ∀ k, (f k).IsWeightedHomogeneous (biWeight e) (wf k))
    (hcharts : ∀ i j, (1 : MvPolynomial (α ⊕ β) F) ∈
      Ideal.span (Set.range fun k => chart i j (map (eval₂Hom ψ₀ μ₀) (f k)))) :
    ∃ h : MvPolynomial τ R, h ≠ 0 ∧ eval₂ ψ₀ μ₀ h ≠ 0 ∧
      ∀ {K : Type*} [Field K] (ψ : R →+* K) (μ : τ → K), eval₂ ψ μ h ≠ 0 →
        ∀ (x : α → K) (y : β → K), (∀ k, eval (Sum.elim x y) (map (eval₂Hom ψ μ) (f k)) = 0) →
          x = 0 ∨ y = 0 := by
  obtain ⟨N, S, hS, hT⟩ := biMacaulay_transfer_of_charts (eval₂Hom ψ₀ μ₀) f e wf hf hcharts
  refine ⟨biMacaulayMinor f e wf N S, fun h => hS (by rw [h, map_zero]), ?_, fun ψ μ hμ x y hxy => ?_⟩
  · rwa [coe_eval₂Hom] at hS
  · rw [← coe_eval₂Hom] at hμ
    exact hT (eval₂Hom ψ μ) hμ x y hxy

end BiMacaulay

/-! ### The grading of §7.3 -/

/-- The shifts `e` of §7.3, with `α = Fin 2` for `(s, t)` and `β = Fin 7` for
`(P_12, P_13, P_14, P_23, P_24, P_34, c)`: `e = 0` on the `P_kl` and `e = 1` on `c`. -/
def c4Shift : Fin 7 → ℕ := ![0, 0, 0, 0, 0, 0, 1]

/-- `deg s = deg t = (1, 0)`. -/
theorem biWeight_c4Shift_inl (i : Fin 2) : biWeight c4Shift (Sum.inl i : Fin 2 ⊕ Fin 7) = (1, 0) :=
  rfl

/-- `deg P_kl = (0, 1)`. -/
theorem biWeight_c4Shift_P {j : Fin 7} (hj : j ≠ 6) :
    biWeight c4Shift (Sum.inr j : Fin 2 ⊕ Fin 7) = (0, 1) := by
  fin_cases j <;> simp_all [biWeight, c4Shift]

/-- `deg c = (-1, 1)`. -/
theorem biWeight_c4Shift_c : biWeight c4Shift (Sum.inr 6 : Fin 2 ⊕ Fin 7) = (-1, 1) := by
  simp [biWeight, c4Shift]

end

end CC6Full
