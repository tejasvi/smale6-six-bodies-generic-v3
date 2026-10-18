import Lean6.Special.Hand.Sec9.Basic

/-!
# Algebra inside the hand proofs of Section 9 (III): Lemmas 9.11, 9.12, 9.13

Triangles `T = {a, b, s}` at one node of a tree, with `G_kl = P_kl³ (η_k − η_l)` and the distance rows
`P_kl² (ξ_k − ξ_l)(η_k − η_l) = 1` (the case `c = w`; `c = z` exchanges the colours).

* H9.8, Lemma 9.11 (`lem:handR`): `handR_lambda` (balance of `a`, `b` gives `(G_ab, G_bs, G_sa) = λ(m_s, m_a, m_b)`),
  `handR_relations` (`κ = P_bs/P_sa` satisfies `M_A m_b κ³ = M_B m_a` and
  `m_s² (M_A + M_B)(m_a + m_b κ)³ = m_a³ m_b² M_B`), the resultant `N` (`NF`, `NG`, `N`) with `N_eval_zero` (a common
  root makes `N` vanish), `N_special` (with `M_A = m_a`, `M_B = m_b`, `m_s = 0` it is `−m_a^{12} m_b^{12}`), `N_ne_zero`,
  and `handR_kappa` (at positive masses, with `M_A = m_a`, `M_B = m_b`: `κ = 1` and `m_s² (m_a + m_b)⁴ = m_a³ m_b³`).
* H9.9, Lemma 9.12 (`lem:handR6`): `handR6_relation` (`ω = P_sb/P_sa`, `ω³ = 1`,
  `m_a m_b⁵ = m_s² (m_a + m_b)³ (m_a + ω m_b)`), `prod_cube_roots`, `handR6_product` (the product over `ω` is
  `(m_a m_b⁵ − m_s²(m_a+m_b)³m_a)³ − (m_s²(m_a+m_b)³m_b)³`, which is `(m_a m_b⁵)³` at `m_s = 0`), `H6poly_ne_zero`,
  `handR6_pos` (at positive masses `ω = 1`, so `m_s² (m_a + m_b)⁴ = m_a m_b⁵`).
* H9.10, Lemma 9.13 (`lem:handW3`): `handW3_core` (`α + β + γ = 0` with `α³ u₁ = β³ u₂ = γ³ u₃ = c ≠ 0` gives
  `H_W = (u₁u₂ + u₂u₃ + u₃u₁)³ − 27 (u₁u₂u₃)² = 0`), `handW3` (from the relations of the lemma).
-/

namespace Lean6.Special.Hand.Sec9

open Complex

/-! ## H9.8, Lemma 9.11 -/

/-- **Lemma 9.11**, balance: `Φ^w_a = m_b G_ab + m_s P_as³(η_a − η_s) = 0` and
`Φ^w_b = m_a P_ab³(η_b − η_a) + m_s G_bs = 0` give `(G_ab, G_bs, G_sa) = λ (m_s, m_a, m_b)` with
`λ = G_ab/m_s`. -/
theorem handR_lambda {K : Type*} [Field K] (ma mb ms ηa ηb ηs Pab Pbs Psa : K) (hms : ms ≠ 0)
    (hΦa : mb * (Pab ^ 3 * (ηa - ηb)) + ms * (Psa ^ 3 * (ηa - ηs)) = 0)
    (hΦb : ma * (Pab ^ 3 * (ηb - ηa)) + ms * (Pbs ^ 3 * (ηb - ηs)) = 0) :
    Pab ^ 3 * (ηa - ηb) = (Pab ^ 3 * (ηa - ηb) / ms) * ms ∧
      Pbs ^ 3 * (ηb - ηs) = (Pab ^ 3 * (ηa - ηb) / ms) * ma ∧
      Psa ^ 3 * (ηs - ηa) = (Pab ^ 3 * (ηa - ηb) / ms) * mb := by
  refine ⟨by field_simp, ?_, ?_⟩
  · field_simp; linear_combination hΦb
  · field_simp; linear_combination -hΦa

/-- **Lemma 9.11**, the relations (`η_s = 0`). With `(G_ab, G_bs, G_sa) = λ(m_s, m_a, m_b)`, `λ ≠ 0`, the relation
`M_A η_a + M_B η_b = 0` of (a), (b) or (c), and the three distance rows: `κ = P_bs/P_sa` satisfies
`M_A m_b κ³ = M_B m_a` and `m_s² (M_A + M_B)(m_a + m_b κ)³ = m_a³ m_b² M_B`. -/
theorem handR_relations {K : Type*} [Field K] (ma mb ms MA MB lam ηa ηb ξa ξb ξs Pab Pbs Psa : K)
    (hms : ms ≠ 0) (hlam : lam ≠ 0)
    (Gab : Pab ^ 3 * (ηa - ηb) = lam * ms) (Gbs : Pbs ^ 3 * ηb = lam * ma) (Gsa : Psa ^ 3 * (-ηa) = lam * mb)
    (hroot : MA * ηa + MB * ηb = 0)
    (dab : Pab ^ 2 * (ξa - ξb) * (ηa - ηb) = 1) (dbs : Pbs ^ 2 * (ξb - ξs) * ηb = 1)
    (dsa : Psa ^ 2 * (ξs - ξa) * (-ηa) = 1) :
    MA * mb * (Pbs / Psa) ^ 3 = MB * ma ∧ ms ^ 2 * (MA + MB) * (ma + mb * (Pbs / Psa)) ^ 3 = ma ^ 3 * mb ^ 2 * MB := by
  have hPsa : Psa ≠ 0 := by intro h0; rw [h0] at dsa; simp at dsa
  have hPbs : Pbs ≠ 0 := by intro h0; rw [h0] at dbs; simp at dbs
  have k1 : lam * (MA * mb * Pbs ^ 3 - MB * ma * Psa ^ 3) = 0 := by
    linear_combination (-(MA * Pbs ^ 3)) * Gsa + (MB * Psa ^ 3) * Gbs - Psa ^ 3 * Pbs ^ 3 * hroot
  have k1' : MA * mb * Pbs ^ 3 = MB * ma * Psa ^ 3 := by
    linear_combination (mul_eq_zero.mp k1).resolve_left hlam
  have er : lam * (ms * Pbs ^ 3 * Psa ^ 3 + ma * Pab ^ 3 * Psa ^ 3 + mb * Pab ^ 3 * Pbs ^ 3) = 0 := by
    linear_combination (-(Pbs ^ 3 * Psa ^ 3)) * Gab + (-(Pab ^ 3 * Psa ^ 3)) * Gbs + (-(Pab ^ 3 * Pbs ^ 3)) * Gsa
  have er' : ms * Pbs ^ 3 * Psa ^ 3 + ma * Pab ^ 3 * Psa ^ 3 + mb * Pab ^ 3 * Pbs ^ 3 = 0 :=
    (mul_eq_zero.mp er).resolve_left hlam
  have x1 : Pab * ma * mb + Pbs * ms * mb + Psa * ms * ma = 0 := by
    linear_combination ma * mb * (ξa - ξb) * Gab - ma * mb * Pab * dab + ms * mb * (ξb - ξs) * Gbs -
      ms * mb * Pbs * dbs + ms * ma * (ξs - ξa) * Gsa - ms * ma * Psa * dsa
  have E1 : Pbs ^ 3 * (ms * MB * Psa ^ 3 + mb * (MA + MB) * Pab ^ 3) = 0 := by
    linear_combination MB * er' + Pab ^ 3 * k1'
  have E1' : ms * MB * Psa ^ 3 + mb * (MA + MB) * Pab ^ 3 = 0 :=
    (mul_eq_zero.mp E1).resolve_left (pow_ne_zero 3 hPbs)
  have T : ms * (ms ^ 2 * (MA + MB) * (ma * Psa + mb * Pbs) ^ 3 - ma ^ 3 * mb ^ 2 * MB * Psa ^ 3) = 0 := by
    linear_combination (MA + MB) * ((Pab * ma * mb + Pbs * ms * mb + Psa * ms * ma) ^ 2 -
      3 * (Pab * ma * mb + Pbs * ms * mb + Psa * ms * ma) * (ma * mb * Pab) + 3 * (ma * mb * Pab) ^ 2) * x1 -
      ma ^ 3 * mb ^ 2 * E1'
  have T' : ms ^ 2 * (MA + MB) * (ma * Psa + mb * Pbs) ^ 3 = ma ^ 3 * mb ^ 2 * MB * Psa ^ 3 := by
    linear_combination (mul_eq_zero.mp T).resolve_left hms
  constructor
  · rw [div_pow]; field_simp; linear_combination k1'
  · have e : ma + mb * (Pbs / Psa) = (ma * Psa + mb * Pbs) / Psa := by field_simp
    rw [e, div_pow]; field_simp; linear_combination T'

open Polynomial in
/-- The first polynomial of `N`, in `κ` over `ℤ[m_a, m_b, m_s, M_A, M_B]` (variables `0, …, 4`):
`M_A m_b κ³ − M_B m_a`. -/
noncomputable def NF : (MvPolynomial (Fin 5) ℤ)[X] :=
  C (MvPolynomial.X 3 * MvPolynomial.X 1) * X ^ 3 - C (MvPolynomial.X 4 * MvPolynomial.X 0)

open Polynomial in
/-- The second polynomial of `N`: `m_s² (M_A + M_B)(m_a + m_b κ)³ − m_a³ m_b² M_B`. -/
noncomputable def NG : (MvPolynomial (Fin 5) ℤ)[X] :=
  C (MvPolynomial.X 2 ^ 2 * (MvPolynomial.X 3 + MvPolynomial.X 4)) *
      (C (MvPolynomial.X 0) + C (MvPolynomial.X 1) * X) ^ 3 -
    C (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 4)

/-- **The polynomial `N` of Lemma 9.11**: `Res_κ` of `NF` and `NG`, with the formal degrees `3, 3`. -/
noncomputable def N : MvPolynomial (Fin 5) ℤ := Polynomial.resultant NF NG 3 3

open Polynomial in
theorem natDegree_map_NF_le {S : Type*} [CommRing S] (φ : MvPolynomial (Fin 5) ℤ →+* S) :
    (NF.map φ).natDegree ≤ 3 := by
  unfold NF
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
  compute_degree

open Polynomial in
theorem natDegree_map_NG_le {S : Type*} [CommRing S] (φ : MvPolynomial (Fin 5) ℤ →+* S) :
    (NG.map φ).natDegree ≤ 3 := by
  unfold NG
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_add]
  compute_degree

/-- **Lemma 9.11**, `N = 0`: at a point `(m_a, m_b, m_s, M_A, M_B)` of a commutative ring where the two polynomials
have a common root `κ`, the value of `N` vanishes (a resultant lies in the ideal of its two arguments). -/
theorem N_eval_zero {S : Type*} [CommRing S] (x : Fin 5 → S) (κ : S)
    (hf : x 3 * x 1 * κ ^ 3 - x 4 * x 0 = 0)
    (hg : x 2 ^ 2 * (x 3 + x 4) * (x 0 + x 1 * κ) ^ 3 - x 0 ^ 3 * x 1 ^ 2 * x 4 = 0) :
    MvPolynomial.eval₂Hom (Int.castRingHom S) x N = 0 := by
  set φ := MvPolynomial.eval₂Hom (Int.castRingHom S) x
  unfold N
  rw [← Polynomial.resultant_map_map]
  obtain ⟨p, q, -, -, e⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant (NF.map φ) (NG.map φ)
    (natDegree_map_NF_le φ) (natDegree_map_NG_le φ) (Or.inl (by norm_num))
  have e' := congrArg (Polynomial.eval κ) e
  have hF : (NF.map φ).eval κ = 0 := by
    unfold NF; simp [φ, hf]
  have hG : (NG.map φ).eval κ = 0 := by
    unfold NG; simp [φ, hg]
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, hF, hG, Polynomial.eval_C] at e'
  rw [← e']; ring

/-- The substitution `M_A ↦ m_a`, `M_B ↦ m_b`, `m_s ↦ 0`. -/
noncomputable def ψN : MvPolynomial (Fin 5) ℤ →+* MvPolynomial (Fin 5) ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![MvPolynomial.X 0, MvPolynomial.X 1, 0, MvPolynomial.X 0, MvPolynomial.X 1]

/-- **Lemma 9.11**, the specialization: with `M_A = m_a`, `M_B = m_b` and `m_s = 0`, `N` becomes
`−m_a^{12} m_b^{12}`. -/
theorem N_special : ψN N = -(MvPolynomial.X 0 ^ 12 * MvPolynomial.X 1 ^ 12) := by
  unfold N
  rw [← Polynomial.resultant_map_map]
  have hG : NG.map ψN = Polynomial.C (-(MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 3)) := by
    unfold NG
    simp [ψN]
    ring
  have hF : (NF.map ψN).coeff 3 = MvPolynomial.X 0 * MvPolynomial.X 1 := by
    unfold NF
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_X, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
    simp [ψN]
  rw [hG, Polynomial.resultant_C_right, hF]
  ring

/-- **Lemma 9.11**: `N` is a nonzero polynomial. -/
theorem N_ne_zero : N ≠ 0 := by
  intro h
  have := N_special
  rw [h, map_zero] at this
  have h0 : (MvPolynomial.X 0 : MvPolynomial (Fin 5) ℤ) ^ 12 * MvPolynomial.X 1 ^ 12 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (MvPolynomial.X_ne_zero _)) (pow_ne_zero _ (MvPolynomial.X_ne_zero _))
  exact h0 (neg_eq_zero.mp this.symm)

/-- **Lemma 9.11**, the last statement: at positive masses with `M_A = m_a`, `M_B = m_b`, the relations give
`κ = 1` and `m_s² (m_a + m_b)⁴ = m_a³ m_b³`. -/
theorem handR_kappa (ma mb ms : ℝ) (hma : 0 < ma) (hmb : 0 < mb) (hms : 0 < ms) (κ : ℂ)
    (h1 : (ma : ℂ) * mb * κ ^ 3 = mb * ma)
    (h2 : (ms : ℂ) ^ 2 * (ma + mb) * (ma + mb * κ) ^ 3 = ma ^ 3 * mb ^ 2 * mb) :
    κ = 1 ∧ ms ^ 2 * (ma + mb) ^ 4 = ma ^ 3 * mb ^ 3 := by
  have hab : (ma : ℂ) * mb ≠ 0 := by
    have : (0 : ℝ) < ma * mb := mul_pos hma hmb
    exact_mod_cast this.ne'
  have hk3 : κ ^ 3 = 1 := by
    have : (ma : ℂ) * mb * (κ ^ 3 - 1) = 0 := by linear_combination h1
    linear_combination (mul_eq_zero.mp this).resolve_left hab
  set r : ℝ := ma ^ 3 * mb ^ 3 / (ms ^ 2 * (ma + mb)) with hr
  have hr0 : 0 < r := by positivity
  have hd : (ms : ℂ) ^ 2 * (ma + mb) ≠ 0 := by
    have : (0 : ℝ) < ms ^ 2 * (ma + mb) := by positivity
    exact_mod_cast this.ne'
  have hcube : ((ma : ℂ) + mb * κ) ^ 3 = r := by
    rw [hr]; push_cast
    rw [eq_div_iff hd]
    linear_combination h2
  have hk : κ = 1 := cube_pos_forces_one hma hmb hk3 hr0 hcube
  refine ⟨hk, ?_⟩
  rw [hk] at h2
  have h' : ((ms ^ 2 * (ma + mb) ^ 4 : ℝ) : ℂ) = ((ma ^ 3 * mb ^ 3 : ℝ) : ℂ) := by
    push_cast; linear_combination h2
  exact_mod_cast h'

/-! ## H9.9, Lemma 9.12 -/

/-- **Lemma 9.12**, the relation (`c = w`, `η_s = 0`). Hypotheses: the root relation `m_a η_a + m_b η_b = 0`, the
initial forms of the `w`-equation of `s` and of the `z`-equation of `a`, and the three distance rows. Then
`ω = P_sb/P_sa` satisfies `ω³ = 1` and `m_a m_b⁵ = m_s² (m_a + m_b)³ (m_a + ω m_b)`. -/
theorem handR6_relation {K : Type*} [Field K] (ma mb ms ηa ηb ξa ξb ξs Pab Psb Psa : K) (hma : ma ≠ 0)
    (hroot : ma * ηa + mb * ηb = 0) (hsw : ma * Psa ^ 3 * ηa + mb * Psb ^ 3 * ηb = 0)
    (hza : mb * Pab ^ 3 * (ξa - ξb) + ms * Psa ^ 3 * (ξa - ξs) = 0)
    (dab : Pab ^ 2 * (ξa - ξb) * (ηa - ηb) = 1) (dbs : Psb ^ 2 * (ξb - ξs) * ηb = 1)
    (dsa : Psa ^ 2 * (ξs - ξa) * (-ηa) = 1) :
    (Psb / Psa) ^ 3 = 1 ∧ ma * mb ^ 5 = ms ^ 2 * (ma + mb) ^ 3 * (ma + Psb / Psa * mb) := by
  have hηa : ηa ≠ 0 := by intro h0; rw [h0] at dsa; simp at dsa
  have hPsa : Psa ≠ 0 := by intro h0; rw [h0] at dsa; simp at dsa
  have F1 : ma * ηa * (Psa ^ 3 - Psb ^ 3) = 0 := by linear_combination hsw - Psb ^ 3 * hroot
  have F1' : Psa ^ 3 = Psb ^ 3 := by
    linear_combination (mul_eq_zero.mp F1).resolve_left (mul_ne_zero hma hηa)
  set ω := Psb / Psa with hω
  have hPsb : Psb = ω * Psa := by rw [hω]; field_simp
  have hω3 : ω ^ 3 = 1 := by
    rw [hω, div_pow, ← F1', div_self (pow_ne_zero 3 hPsa)]
  have F2 : ηa * (mb ^ 2 * Pab + ms * (ma + mb) * Psa) = 0 := by
    linear_combination mb * (ηa - ηb) * ηa * hza - mb * mb * Pab * ηa * dab -
      mb * ms * Psa * (ηa - ηb) * dsa + ms * Psa * hroot
  have F2' : mb ^ 2 * Pab + ms * (ma + mb) * Psa = 0 := (mul_eq_zero.mp F2).resolve_left hηa
  have hE : Psb ^ 2 * Psa ^ 2 * ηb * ηa + Pab ^ 2 * Psa ^ 2 * (ηa - ηb) * ηa -
      Pab ^ 2 * Psb ^ 2 * (ηa - ηb) * ηb = 0 := by
    linear_combination (-(Psb ^ 2 * Psa ^ 2 * ηb * ηa)) * dab + (-(Pab ^ 2 * Psa ^ 2 * (ηa - ηb) * ηa)) * dbs +
      (Pab ^ 2 * Psb ^ 2 * (ηa - ηb) * ηb) * dsa
  have hF : ηa ^ 2 * (mb * (ma + mb) * Pab ^ 2 * Psa ^ 2 + ma * (ma + mb) * Pab ^ 2 * Psb ^ 2 -
      ma * mb * Psb ^ 2 * Psa ^ 2) = 0 := by
    linear_combination mb ^ 2 * hE - (Psb ^ 2 * Psa ^ 2 * mb * ηa - Pab ^ 2 * Psa ^ 2 * mb * ηa -
      Pab ^ 2 * Psb ^ 2 * ((2 * ma + mb) * ηa - (ma * ηa + mb * ηb))) * hroot
  have H := (mul_eq_zero.mp hF).resolve_left (pow_ne_zero 2 hηa)
  rw [hPsb] at H
  refine ⟨hω3, ?_⟩
  have key : Psa ^ 4 * (ma * mb ^ 5 - ms ^ 2 * (ma + mb) ^ 3 * (ma + ω * mb)) = 0 := by
    linear_combination (-(mb ^ 4 * ω)) * H + mb ^ 4 * Psa ^ 2 * (ma * (ma + mb) * Pab ^ 2 - ma * mb * Psa ^ 2) * hω3 +
      Psa ^ 2 * (ma + mb) * (ma + mb * ω) * (mb ^ 2 * Pab - ms * (ma + mb) * Psa) * F2'
  linear_combination (mul_eq_zero.mp key).resolve_left (pow_ne_zero 4 hPsa)

/-- `∏_{ω³ = 1} (x − y ω) = x³ − y³`: for a root `j` of `t² + t + 1`, `(x − y)(x − yj)(x − yj²) = x³ − y³`. -/
theorem prod_cube_roots {K : Type*} [CommRing K] (x y j : K) (hj : j ^ 2 + j + 1 = 0) :
    (x - y) * (x - y * j) * (x - y * j ^ 2) = x ^ 3 - y ^ 3 := by
  linear_combination (x - y) * (-(x * y) + y ^ 2 * (j - 1)) * hj

/-- **Lemma 9.12**, the product of the differences of the two sides over the three values of `ω`
(`1, j, j²`): `(m_a m_b⁵ − m_s²(m_a + m_b)³ m_a)³ − (m_s²(m_a + m_b)³ m_b)³`. -/
theorem handR6_product {K : Type*} [CommRing K] (ma mb ms j : K) (hj : j ^ 2 + j + 1 = 0) :
    (ma * mb ^ 5 - ms ^ 2 * (ma + mb) ^ 3 * (ma + 1 * mb)) *
        (ma * mb ^ 5 - ms ^ 2 * (ma + mb) ^ 3 * (ma + j * mb)) *
        (ma * mb ^ 5 - ms ^ 2 * (ma + mb) ^ 3 * (ma + j ^ 2 * mb)) =
      (ma * mb ^ 5 - ms ^ 2 * (ma + mb) ^ 3 * ma) ^ 3 - (ms ^ 2 * (ma + mb) ^ 3 * mb) ^ 3 := by
  have := prod_cube_roots (ma * mb ^ 5 - ms ^ 2 * (ma + mb) ^ 3 * ma) (ms ^ 2 * (ma + mb) ^ 3 * mb) j hj
  rw [← this]; ring

/-- The polynomial of `handR6_product` in `ℤ[m_a, m_b, m_s]`. -/
noncomputable def H6poly : MvPolynomial (Fin 3) ℤ :=
  (MvPolynomial.X 0 * MvPolynomial.X 1 ^ 5 -
      MvPolynomial.X 2 ^ 2 * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ 3 * MvPolynomial.X 0) ^ 3 -
    (MvPolynomial.X 2 ^ 2 * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ 3 * MvPolynomial.X 1) ^ 3

/-- **Lemma 9.12**: at `m_s = 0` the product is `(m_a m_b⁵)³`; so it is a nonzero polynomial. -/
theorem H6poly_ms_zero (ma mb : ℤ) : MvPolynomial.eval ![ma, mb, 0] H6poly = (ma * mb ^ 5) ^ 3 := by
  simp [H6poly]

theorem H6poly_ne_zero : H6poly ≠ 0 := by
  intro h
  have := H6poly_ms_zero 1 1
  rw [h, map_zero] at this
  norm_num at this

/-- **Lemma 9.12** at positive masses: the left side `m_a m_b⁵` is positive, so `m_a + ω m_b` is real and `ω = 1`;
hence `m_s² (m_a + m_b)⁴ = m_a m_b⁵`. -/
theorem handR6_pos (ma mb ms : ℝ) (hma : 0 < ma) (hmb : 0 < mb) (hms : 0 < ms) (ω : ℂ) (hω3 : ω ^ 3 = 1)
    (h : (ma : ℂ) * mb ^ 5 = ms ^ 2 * (ma + mb) ^ 3 * (ma + ω * mb)) :
    ω = 1 ∧ ms ^ 2 * (ma + mb) ^ 4 = ma * mb ^ 5 := by
  have hd : (ms : ℂ) ^ 2 * (ma + mb) ^ 3 ≠ 0 := by
    have : (0 : ℝ) < ms ^ 2 * (ma + mb) ^ 3 := by positivity
    exact_mod_cast this.ne'
  have hreal : (ma : ℂ) + mb * ω = ((ma * mb ^ 5 / (ms ^ 2 * (ma + mb) ^ 3) : ℝ) : ℂ) := by
    push_cast
    rw [eq_div_iff hd]
    linear_combination -h
  have hw : ω = 1 := real_forces_one hmb.ne' hω3 hreal
  refine ⟨hw, ?_⟩
  rw [hw] at h
  have h' : ((ms ^ 2 * (ma + mb) ^ 4 : ℝ) : ℂ) = ((ma * mb ^ 5 : ℝ) : ℂ) := by
    push_cast; linear_combination -h
  exact_mod_cast h'

/-! ## H9.10, Lemma 9.13 -/

/-- **Lemma 9.13**, the core: `α + β + γ = 0` with `α³ u₁ = β³ u₂ = γ³ u₃ = c ≠ 0` gives
`H_W = (u₁u₂ + u₂u₃ + u₃u₁)³ − 27 (u₁u₂u₃)² = 0` (from `α³ + β³ + γ³ = 3αβγ`, cubed). -/
theorem handW3_core {K : Type*} [Field K] (α β γ c u1 u2 u3 : K) (h : α + β + γ = 0) (h1 : α ^ 3 * u1 = c)
    (h2 : β ^ 3 * u2 = c) (h3 : γ ^ 3 * u3 = c) (hc : c ≠ 0) :
    (u1 * u2 + u2 * u3 + u3 * u1) ^ 3 - 27 * (u1 * u2 * u3) ^ 2 = 0 := by
  have hα : α ≠ 0 := by rintro rfl; simp at h1; exact hc h1.symm
  have hβ : β ≠ 0 := by rintro rfl; simp at h2; exact hc h2.symm
  have hγ : γ ≠ 0 := by rintro rfl; simp at h3; exact hc h3.symm
  have e1 : u1 = c / α ^ 3 := by field_simp; linear_combination h1
  have e2 : u2 = c / β ^ 3 := by field_simp; linear_combination h2
  have e3 : u3 = c / γ ^ 3 := by field_simp; linear_combination h3
  have hg : γ = -α - β := by linear_combination h
  rw [e1, e2, e3]
  rw [hg] at hγ ⊢
  field_simp
  ring

/-- **Lemma 9.13** (`c = w`). With `η = τ e` on the three children (`τ ≠ 0`), `(G_ab, G_bs, G_sa) = λ(m_s, m_a, m_b)`
(`λ ≠ 0`) and the three distance rows, `H_W(u₁, u₂, u₃) = 0` for `u₁ = m_s²(e_a − e_b)`, `u₂ = m_a²(e_b − e_s)`,
`u₃ = m_b²(e_s − e_a)`. -/
theorem handW3 {K : Type*} [Field K] (ma mb ms τ lam ea eb es ξa ξb ξs Pab Pbs Psa : K) (hτ : τ ≠ 0)
    (hlam : lam ≠ 0) (hma : ma ≠ 0) (hmb : mb ≠ 0) (hms : ms ≠ 0)
    (Gab : Pab ^ 3 * (τ * (ea - eb)) = lam * ms) (Gbs : Pbs ^ 3 * (τ * (eb - es)) = lam * ma)
    (Gsa : Psa ^ 3 * (τ * (es - ea)) = lam * mb)
    (dab : Pab ^ 2 * (ξa - ξb) * (τ * (ea - eb)) = 1) (dbs : Pbs ^ 2 * (ξb - ξs) * (τ * (eb - es)) = 1)
    (dsa : Psa ^ 2 * (ξs - ξa) * (τ * (es - ea)) = 1) :
    ((ms ^ 2 * (ea - eb)) * (ma ^ 2 * (eb - es)) + (ma ^ 2 * (eb - es)) * (mb ^ 2 * (es - ea)) +
        (mb ^ 2 * (es - ea)) * (ms ^ 2 * (ea - eb))) ^ 3 -
      27 * ((ms ^ 2 * (ea - eb)) * (ma ^ 2 * (eb - es)) * (mb ^ 2 * (es - ea))) ^ 2 = 0 := by
  have x1 : Pab * ma * mb + Pbs * ms * mb + Psa * ms * ma = 0 := by
    linear_combination ma * mb * (ξa - ξb) * Gab - ma * mb * Pab * dab + ms * mb * (ξb - ξs) * Gbs -
      ms * mb * Pbs * dbs + ms * ma * (ξs - ξa) * Gsa - ms * ma * Psa * dsa
  refine handW3_core (Pab / ms) (Pbs / ma) (Psa / mb) (lam / τ) _ _ _ ?_ ?_ ?_ ?_ (div_ne_zero hlam hτ)
  · field_simp; linear_combination x1
  · field_simp; linear_combination Gab
  · field_simp; linear_combination Gbs
  · field_simp; linear_combination Gsa

end Lean6.Special.Hand.Sec9
