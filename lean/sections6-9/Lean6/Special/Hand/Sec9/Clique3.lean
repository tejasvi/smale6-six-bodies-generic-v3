import Lean6.Special.Hand.Sec9.Basic

/-!
# Algebra inside the hand proofs of Section 9 (II): Theorem 9.9 and the polynomial `Q_T`

Theorem 9.9 (`thm:clique3`) concerns a triangle `{a, b, s}` with `Φ^w = 0` (and conditions on `Φ^z`). Its proof
first uses linear algebra (the matrix `L` with `L 1 = 0` has rank one, or `1, ξ, η` are dependent); that step stays a
hand argument. The algebra that follows is checked here.

* H9.6 (i): `collinear_dist`, `collinear_force` (the collinear form of `Φ^z`), `clique3_i_ratios` (the two
  equations `Φ^z_a = Φ^z_b = 0` give `ξ_as² m_b = ε₁ m_s ξ_ab²`, `ξ_bs² m_a = ε₂ m_s ξ_ab²` with signs `ε`),
  `one_is_sum` (`n_s + β n_a = α n_b` with `α², β² = ±1` at positive `n`), `clique3_i` (one of `m_a^{−1/2}`,
  `m_b^{−1/2}`, `m_s^{−1/2}` is the sum of the other two).
* H9.6 (ii): `clique3_ii_rank` (from the rank-one form `P³ = λ u u` and `Φ^z_a = Φ^z_b ≠ 0`: `P_bs³ = P_as³` and
  `P_ab³(m_a + m_b) = −m_s P_as³`), `clique3_ii_relation` (`m_a³ m_b³ = m_s² (m_a + m_b)(w² m_a + m_b)³` with
  `w = P_bs/P_as`), `clique3_ii` (at positive masses `w = 1` and `m_s² (m_a + m_b)⁴ = m_a³ m_b³`).
* H9.6 (iii): `clique3_iii`.
* H9.7: `QT_identity` (`Q_T = m_a² m_b² m_s² ∏(n_a ± n_b ± n_s)` with `m_t n_t² = 1`), `QT_zero_iff` (at positive
  masses `Q_T = 0` iff one of the `n_t = m_t^{−1/2}` is the sum of the other two).
-/

namespace Lean6.Special.Hand.Sec9

open Complex

/-! ## Theorem 9.9 (i) -/

/-- If `η = λ ξ + ν` on the triangle, the distance row `P² (ξ_t − ξ_u)(η_t − η_u) = 1` reads
`(P (ξ_t − ξ_u))² λ = 1`. -/
theorem collinear_dist {K : Type*} [Field K] (P ξt ξu ηt ηu lam ν : K) (ht : ηt = lam * ξt + ν)
    (hu : ηu = lam * ξu + ν) (h : P ^ 2 * (ξt - ξu) * (ηt - ηu) = 1) : (P * (ξt - ξu)) ^ 2 * lam = 1 := by
  rw [ht, hu] at h; linear_combination h

/-- With `P ξ_{tt′} = σ ψ` and `σ² = 1`, the force term is `P³ ξ_{tt′} = σ ψ³ ξ_{tt′}^{−2}`. -/
theorem collinear_force {K : Type*} [Field K] (P ξ σ ψ : K) (hσ : σ ^ 2 = 1) (hξ : ξ ≠ 0) (h : P * ξ = σ * ψ) :
    P ^ 3 * ξ = σ * ψ ^ 3 / ξ ^ 2 := by
  have hP : P = σ * ψ / ξ := by field_simp; linear_combination h
  rw [hP]
  field_simp
  linear_combination σ * ψ ^ 3 * hσ

/-- **Theorem 9.9 (i)**, the two equations. With `Φ^z_t = ψ³ Σ_{t′ ≠ t} σ_{tt′} m_{t′} ξ_{tt′}^{−2}`
(antisymmetric signs, `ξ_ba = −ξ_ab`), `Φ^z_a = 0` and `Φ^z_b = 0` read `σ_ab m_b ξ_ab^{−2} + σ_as m_s ξ_as^{−2} = 0`
and `−σ_ab m_a ξ_ab^{−2} + σ_bs m_s ξ_bs^{−2} = 0`. They give `ξ_as² m_b = ε₁ m_s ξ_ab²` and
`ξ_bs² m_a = ε₂ m_s ξ_ab²` with `ε₁ = −σ_as σ_ab`, `ε₂ = σ_bs σ_ab`. -/
theorem clique3_i_ratios {K : Type*} [Field K] (ma mb ms ξab ξas ξbs σab σas σbs : K) (hab : ξab ≠ 0)
    (has : ξas ≠ 0) (hbs : ξbs ≠ 0) (hσ : σab ^ 2 = 1)
    (ha : σab * mb / ξab ^ 2 + σas * ms / ξas ^ 2 = 0) (hb : -σab * ma / ξab ^ 2 + σbs * ms / ξbs ^ 2 = 0) :
    ξas ^ 2 * mb = (-σas * σab) * ms * ξab ^ 2 ∧ ξbs ^ 2 * ma = (σbs * σab) * ms * ξab ^ 2 := by
  field_simp at ha hb
  constructor
  · linear_combination σab * ha - mb * ξas ^ 2 * hσ
  · linear_combination -(σab * hb) - ma * ξbs ^ 2 * hσ

/-- **Theorem 9.9 (i)**, the last step: if `n_s + β n_a = α n_b` with `α, β ∈ {±1, ±i}` (`α² = ±1`, `β² = ±1`) and
positive `n_a, n_b, n_s`, then one of them is the sum of the other two. -/
theorem one_is_sum (na nb ns : ℝ) (ha : 0 < na) (hb : 0 < nb) (hs : 0 < ns) (α β : ℂ)
    (hα : α ^ 2 = 1 ∨ α ^ 2 = -1) (hβ : β ^ 2 = 1 ∨ β ^ 2 = -1) (h : (ns : ℂ) + β * na = α * nb) :
    na = nb + ns ∨ nb = na + ns ∨ ns = na + nb := by
  have cases : ∀ z : ℂ, z ^ 2 = 1 ∨ z ^ 2 = -1 → z = 1 ∨ z = -1 ∨ z = I ∨ z = -I := by
    intro z hz
    rcases hz with hz | hz
    · have : (z - 1) * (z + 1) = 0 := by linear_combination hz
      rcases mul_eq_zero.mp this with h1 | h1
      · left; linear_combination h1
      · right; left; linear_combination h1
    · have : (z - I) * (z + I) = 0 := by linear_combination hz - I_sq
      rcases mul_eq_zero.mp this with h1 | h1
      · right; right; left; linear_combination h1
      · right; right; right; linear_combination h1
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  rcases cases α hα with rfl | rfl | rfl | rfl <;> rcases cases β hβ with rfl | rfl | rfl | rfl <;>
    simp at hre him <;>
    first
    | (left; linarith)
    | (right; left; linarith)
    | (right; right; linarith)

/-- **Theorem 9.9 (i).** At positive masses, the two equations `Φ^z_a = Φ^z_b = 0` in the collinear form, with
`ξ_as = ξ_ab + ξ_bs` and signs `σ = ±1`, force one of `n_t = m_t^{−1/2}` to be the sum of the other two. -/
theorem clique3_i (ma mb ms : ℝ) (hma : 0 < ma) (hmb : 0 < mb) (hms : 0 < ms) (ξab ξas ξbs σab σas σbs : ℂ)
    (hab : ξab ≠ 0) (has : ξas ≠ 0) (hbs : ξbs ≠ 0) (hsum : ξas = ξab + ξbs)
    (hσab : σab = 1 ∨ σab = -1) (hσas : σas = 1 ∨ σas = -1) (hσbs : σbs = 1 ∨ σbs = -1)
    (ha : σab * mb / ξab ^ 2 + σas * ms / ξas ^ 2 = 0) (hb : -σab * ma / ξab ^ 2 + σbs * ms / ξbs ^ 2 = 0) :
    (Real.sqrt ma)⁻¹ = (Real.sqrt mb)⁻¹ + (Real.sqrt ms)⁻¹ ∨ (Real.sqrt mb)⁻¹ = (Real.sqrt ma)⁻¹ + (Real.sqrt ms)⁻¹ ∨
      (Real.sqrt ms)⁻¹ = (Real.sqrt ma)⁻¹ + (Real.sqrt mb)⁻¹ := by
  set na := (Real.sqrt ma)⁻¹ with hna
  set nb := (Real.sqrt mb)⁻¹ with hnb
  set ns := (Real.sqrt ms)⁻¹ with hns
  have pa : 0 < na := inv_pos.mpr (Real.sqrt_pos.mpr hma)
  have pb : 0 < nb := inv_pos.mpr (Real.sqrt_pos.mpr hmb)
  have ps : 0 < ns := inv_pos.mpr (Real.sqrt_pos.mpr hms)
  have sqa : (na : ℂ) ^ 2 * ma = 1 := by
    have : na ^ 2 * ma = 1 := by
      rw [hna, inv_pow, Real.sq_sqrt hma.le, inv_mul_cancel₀ hma.ne']
    exact_mod_cast this
  have sqb : (nb : ℂ) ^ 2 * mb = 1 := by
    have : nb ^ 2 * mb = 1 := by
      rw [hnb, inv_pow, Real.sq_sqrt hmb.le, inv_mul_cancel₀ hmb.ne']
    exact_mod_cast this
  have sqs : (ns : ℂ) ^ 2 * ms = 1 := by
    have : ns ^ 2 * ms = 1 := by
      rw [hns, inv_pow, Real.sq_sqrt hms.le, inv_mul_cancel₀ hms.ne']
    exact_mod_cast this
  have hσ2 : σab ^ 2 = 1 := by rcases hσab with h | h <;> rw [h] <;> norm_num
  obtain ⟨r1, r2⟩ := clique3_i_ratios (ma : ℂ) mb ms ξab ξas ξbs σab σas σbs hab has hbs hσ2 ha hb
  have hnb0 : (nb : ℂ) ≠ 0 := by exact_mod_cast pb.ne'
  have hna0 : (na : ℂ) ≠ 0 := by exact_mod_cast pa.ne'
  set α : ℂ := ξas / ξab * (ns / nb) with hα
  set β : ℂ := ξbs / ξab * (ns / na) with hβ
  have hε : ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ∀ σ : ℂ, (σ = 1 ∨ σ = -1) → (ε * σ = 1 ∨ ε * σ = -1) := by
    intro ε hε σ hσ
    rcases hε with rfl | rfl <;> rcases hσ with rfl | rfl <;> norm_num
  have hα2 : α ^ 2 = -σas * σab := by
    have e : α ^ 2 = ξas ^ 2 * ns ^ 2 / (ξab ^ 2 * nb ^ 2) := by rw [hα]; ring
    rw [e, div_eq_iff (mul_ne_zero (pow_ne_zero 2 hab) (pow_ne_zero 2 hnb0))]
    linear_combination (nb : ℂ) ^ 2 * ns ^ 2 * r1 - ξas ^ 2 * ns ^ 2 * sqb + (-σas * σab) * ξab ^ 2 * nb ^ 2 * sqs
  have hβ2 : β ^ 2 = σbs * σab := by
    have e : β ^ 2 = ξbs ^ 2 * ns ^ 2 / (ξab ^ 2 * na ^ 2) := by rw [hβ]; ring
    rw [e, div_eq_iff (mul_ne_zero (pow_ne_zero 2 hab) (pow_ne_zero 2 hna0))]
    linear_combination (na : ℂ) ^ 2 * ns ^ 2 * r2 - ξbs ^ 2 * ns ^ 2 * sqa + (σbs * σab) * ξab ^ 2 * na ^ 2 * sqs
  have heq : (ns : ℂ) + β * na = α * nb := by
    rw [hα, hβ, hsum]; field_simp
  have hneg : -σas = 1 ∨ -σas = -1 := by rcases hσas with h | h <;> rw [h] <;> norm_num
  refine one_is_sum na nb ns pa pb ps α β ?_ ?_ heq
  · rw [hα2]; exact hε _ hneg _ hσab
  · rw [hβ2]; exact hε _ hσbs _ hσab

/-! ## Theorem 9.9 (ii) -/

/-- **Theorem 9.9 (ii)**, after the rank argument: `P_tt′³ = λ u_t u_t′`, `Σ m_t u_t = 0` and `Φ^z = c u` with
`c ≠ 0` (`c = −λ ⟨m ∘ u, ξ⟩`). If `Φ^z_a = Φ^z_b`, then `u_a = u_b`, `u_s = −u_a (m_a + m_b)/m_s`, so
`P_bs³ = P_as³` and `(P_ab/P_as)³ = −m_s/(m_a + m_b)`. -/
theorem clique3_ii_rank {K : Type*} [Field K] (ma mb ms lam ua ub us c Pab Pas Pbs : K) (hms : ms ≠ 0)
    (hc : c ≠ 0) (hab3 : Pab ^ 3 = lam * ua * ub) (has3 : Pas ^ 3 = lam * ua * us) (hbs3 : Pbs ^ 3 = lam * ub * us)
    (hm : ma * ua + mb * ub + ms * us = 0) (hΦ : c * ua = c * ub) :
    ua = ub ∧ us = -(ua * (ma + mb)) / ms ∧ Pbs ^ 3 = Pas ^ 3 ∧ Pab ^ 3 * (ma + mb) = -(ms * Pas ^ 3) := by
  have hu : ua = ub := mul_left_cancel₀ hc hΦ
  subst hu
  refine ⟨rfl, ?_, ?_, ?_⟩
  · field_simp; linear_combination hm
  · rw [hbs3, has3]
  · rw [hab3, has3]; linear_combination lam * ua * hm

/-- **Theorem 9.9 (ii)**, the relation. With `P_bs = w P_as` (`w³ = 1`), `P_ab³ (m_a + m_b) = −m_s P_as³`,
`η_as = m_b ν`, `η_bs = −m_a ν`, `η_ab = (m_a + m_b) ν`, `ξ_ab = ξ_as − ξ_bs` and the three distance rows:
`m_a³ m_b³ = m_s² (m_a + m_b) (w² m_a + m_b)³` (the paper's `j^{2k} = w²`). -/
theorem clique3_ii_relation {K : Type*} [Field K] (ma mb ms w ν ξab ξas ξbs Pab Pas Pbs : K)
    (hw3 : w ^ 3 = 1) (hPbs : Pbs = w * Pas) (hPab : Pab ^ 3 * (ma + mb) = -(ms * Pas ^ 3))
    (hξ : ξab = ξas - ξbs) (das : Pas ^ 2 * ξas * (mb * ν) = 1) (dbs : Pbs ^ 2 * ξbs * (-(ma * ν)) = 1)
    (dab : Pab ^ 2 * ξab * ((ma + mb) * ν) = 1) :
    ma ^ 3 * mb ^ 3 = ms ^ 2 * (ma + mb) * (w ^ 2 * ma + mb) ^ 3 := by
  have hPas : Pas ≠ 0 := by intro h0; rw [h0] at das; simp at das
  have hν : ν ≠ 0 := by intro h0; rw [h0] at das; simp at das
  rw [hPbs] at dbs
  rw [hξ] at dab
  have hx0 : Pas ^ 2 * ν * (ξas * mb + w ^ 2 * ma * ξbs) = 0 := by linear_combination das - dbs
  have hx : ξas * mb + w ^ 2 * ma * ξbs = 0 :=
    (mul_eq_zero.mp hx0).resolve_left (mul_ne_zero (pow_ne_zero 2 hPas) hν)
  have hstar : Pab ^ 2 * (ma + mb) * (w ^ 2 * ma + mb) = w ^ 2 * ma * mb * Pas ^ 2 := by
    linear_combination -(Pab ^ 2 * (ma + mb) * (w ^ 2 * ma + mb)) * das + mb * Pas ^ 2 * w ^ 2 * ma * dab +
      mb * Pas ^ 2 * Pab ^ 2 * (ma + mb) * ν * hx
  have h6a : (Pab ^ 2 * (ma + mb) * (w ^ 2 * ma + mb)) ^ 3 = (w ^ 2 * ma * mb * Pas ^ 2) ^ 3 := by rw [hstar]
  have h6b : (Pab ^ 3 * (ma + mb)) ^ 2 = (ms * Pas ^ 3) ^ 2 := by rw [hPab]; ring
  have key : Pas ^ 6 * (ms ^ 2 * (ma + mb) * (w ^ 2 * ma + mb) ^ 3 - ma ^ 3 * mb ^ 3) = 0 := by
    linear_combination h6a - (ma + mb) * (w ^ 2 * ma + mb) ^ 3 * h6b + ma ^ 3 * mb ^ 3 * Pas ^ 6 * (w ^ 3 + 1) * hw3
  linear_combination -((mul_eq_zero.mp key).resolve_left (pow_ne_zero 6 hPas))

/-- **Theorem 9.9 (ii)** at positive masses: the relation forces `w = 1` (the paper's `k = 0`), hence
`m_s² (m_a + m_b)⁴ = m_a³ m_b³`. -/
theorem clique3_ii (ma mb ms : ℝ) (hma : 0 < ma) (hmb : 0 < mb) (hms : 0 < ms) (w : ℂ) (hw3 : w ^ 3 = 1)
    (h : (ma : ℂ) ^ 3 * mb ^ 3 = ms ^ 2 * (ma + mb) * (w ^ 2 * ma + mb) ^ 3) :
    w = 1 ∧ ms ^ 2 * (ma + mb) ^ 4 = ma ^ 3 * mb ^ 3 := by
  set r : ℝ := ma ^ 3 * mb ^ 3 / (ms ^ 2 * (ma + mb)) with hr
  have hr0 : 0 < r := by positivity
  have hd : (ms : ℂ) ^ 2 * (ma + mb) ≠ 0 := by
    have : (0 : ℝ) < ms ^ 2 * (ma + mb) := by positivity
    exact_mod_cast this.ne'
  have hcube : ((mb : ℂ) + ma * w ^ 2) ^ 3 = r := by
    rw [hr]; push_cast
    rw [eq_div_iff hd]
    linear_combination -h
  have hw2 : w ^ 2 = 1 := by
    refine cube_pos_forces_one hmb hma ?_ hr0 hcube
    rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hw3, one_pow]
  have hw : w = 1 := by linear_combination -w * hw2 + hw3
  refine ⟨hw, ?_⟩
  rw [hw] at h
  have h' : ((ms ^ 2 * (ma + mb) ^ 4 : ℝ) : ℂ) = ((ma ^ 3 * mb ^ 3 : ℝ) : ℂ) := by
    push_cast; linear_combination -h
  exact_mod_cast h'

/-! ## Theorem 9.9 (iii) -/

/-- **Theorem 9.9 (iii)**: if `Φ^z = c u` (the rank-one form) with `u_a ≠ 0` and `Φ^z_a = 0`, then `Φ^z = 0`. -/
theorem clique3_iii {K ι : Type*} [Field K] (Φ u : ι → K) (c : K) (a : ι) (hΦ : ∀ t, Φ t = c * u t)
    (hua : u a ≠ 0) (h : Φ a = 0) : ∀ t, Φ t = 0 := by
  have hc : c = 0 := by
    rw [hΦ a] at h
    exact (mul_eq_zero.mp h).resolve_right hua
  intro t; rw [hΦ t, hc, zero_mul]

/-! ## H9.7, the polynomial `Q_T` -/

/-- **`Q_T`** (after Theorem 9.9): with `m_t n_t² = 1`,
`m_a²m_b² + m_b²m_s² + m_s²m_a² − 2 m_a m_b m_s (m_a + m_b + m_s) = m_a² m_b² m_s² ∏ (n_a ± n_b ± n_s)`. -/
theorem QT_identity {K : Type*} [Field K] (ma mb ms na nb ns : K) (ha : ma * na ^ 2 = 1) (hb : mb * nb ^ 2 = 1)
    (hs : ms * ns ^ 2 = 1) :
    ma ^ 2 * mb ^ 2 + mb ^ 2 * ms ^ 2 + ms ^ 2 * ma ^ 2 - 2 * ma * mb * ms * (ma + mb + ms) =
      ma ^ 2 * mb ^ 2 * ms ^ 2 * ((na + nb + ns) * (na + nb - ns) * (na - nb + ns) * (na - nb - ns)) := by
  linear_combination
    (-(mb ^ 2 * ms ^ 2 * (ma * na ^ 2 + 1) - 2 * ma * mb * ms ^ 2 * (mb * nb ^ 2) -
      2 * ma * mb ^ 2 * ms * (ms * ns ^ 2))) * ha +
    (-(ma ^ 2 * ms ^ 2 * (mb * nb ^ 2 + 1) - 2 * ma * mb * ms ^ 2 - 2 * ma ^ 2 * mb * ms * (ms * ns ^ 2))) * hb +
    (-(ma ^ 2 * mb ^ 2 * (ms * ns ^ 2 + 1) - 2 * ma ^ 2 * mb * ms - 2 * ma * mb ^ 2 * ms)) * hs

/-- **`Q_T`** at positive masses: `Q_T = 0` exactly when one of `n_t = m_t^{−1/2}` is the sum of the other two. -/
theorem QT_zero_iff (ma mb ms : ℝ) (hma : 0 < ma) (hmb : 0 < mb) (hms : 0 < ms) :
    ma ^ 2 * mb ^ 2 + mb ^ 2 * ms ^ 2 + ms ^ 2 * ma ^ 2 - 2 * ma * mb * ms * (ma + mb + ms) = 0 ↔
      ((Real.sqrt ma)⁻¹ = (Real.sqrt mb)⁻¹ + (Real.sqrt ms)⁻¹ ∨
        (Real.sqrt mb)⁻¹ = (Real.sqrt ma)⁻¹ + (Real.sqrt ms)⁻¹ ∨
        (Real.sqrt ms)⁻¹ = (Real.sqrt ma)⁻¹ + (Real.sqrt mb)⁻¹) := by
  set na := (Real.sqrt ma)⁻¹ with hna
  set nb := (Real.sqrt mb)⁻¹ with hnb
  set ns := (Real.sqrt ms)⁻¹ with hns
  have pa : 0 < na := inv_pos.mpr (Real.sqrt_pos.mpr hma)
  have pb : 0 < nb := inv_pos.mpr (Real.sqrt_pos.mpr hmb)
  have ps : 0 < ns := inv_pos.mpr (Real.sqrt_pos.mpr hms)
  have sqa : ma * na ^ 2 = 1 := by rw [hna, inv_pow, Real.sq_sqrt hma.le, mul_inv_cancel₀ hma.ne']
  have sqb : mb * nb ^ 2 = 1 := by rw [hnb, inv_pow, Real.sq_sqrt hmb.le, mul_inv_cancel₀ hmb.ne']
  have sqs : ms * ns ^ 2 = 1 := by rw [hns, inv_pow, Real.sq_sqrt hms.le, mul_inv_cancel₀ hms.ne']
  rw [QT_identity ma mb ms na nb ns sqa sqb sqs]
  have hm : ma ^ 2 * mb ^ 2 * ms ^ 2 ≠ 0 := by positivity
  have h1 : na + nb + ns ≠ 0 := by positivity
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hm
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h h1
        · right; right; linarith
      · right; left; linarith
    · left; linarith
  · rintro (h | h | h)
    · rw [h]; ring
    · rw [h]; ring
    · rw [h]; ring

end Lean6.Special.Hand.Sec9
