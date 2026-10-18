import Mathlib
import Lean6.Special.Hand.Identities

/-!
# Algebra inside the hand proofs of Section 9 (I)

Section 9 explains the exclusion of most cells by lemmas proved by hand. This file checks the algebraic steps of
Lemmas 9.1–9.8, 9.16, 9.17 and 9.20, and the facts about cube roots of unity used in Section 9. The hypotheses are the
relations among leading coefficients that the proofs derive from the initial forms (the argmin sets, the trees and
the identities of §2.3 supply them, by hand); the conclusions are those of the paper. Exponents are rational numbers,
leading coefficients complex numbers (or elements of any field where the step is purely algebraic).

* Cube roots of unity: `cube_root_cases`, `primitive_re_im`, `normSq_cube_root`, `cube_re_im`,
  `cube_pos_forces_one` (if `a, b > 0`, `ω³ = 1` and `(a + bω)³` is a positive real, then `ω = 1`),
  `real_forces_one`.
* H9.1, Lemma 9.1 (`lem:Ssum`): `ssum`, `ssum_zero`.
* H9.2, Lemmas 9.2–9.4: `handT_le_of_below`, `handT_le_of_not_below`, `handP_pos`, `forced_x2`, `forced_x4`,
  `handC_ne_zero`.
* H9.3, Lemmas 9.5, 9.6: `handB0`, `handK_c`, `handK_c'`, `handK`.
* H9.4, Lemma 9.7: `handL_relations`, `handL_impossible`, `handL`.
* H9.5, Lemma 9.8 (`lem:cliquesum`): `cliquesum`.
* H9.13, Lemmas 9.16, 9.17: `clique_x_zero`, `clique_orders`.
* H9.14, Lemma 9.20: `handP4`, `handP4_pos`.
-/

namespace Lean6.Special.Hand.Sec9

open Complex Finset

/-! ## Cube roots of unity -/

/-- A cube root of unity is `1` or a root of `t² + t + 1`. -/
theorem cube_root_cases {ω : ℂ} (h : ω ^ 3 = 1) : ω = 1 ∨ ω ^ 2 + ω + 1 = 0 := by
  have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · left; linear_combination h1
  · right; exact h1

/-- A primitive cube root of unity has real part `−1/2` and squared imaginary part `3/4`. -/
theorem primitive_re_im {ω : ℂ} (h : ω ^ 2 + ω + 1 = 0) : ω.re = -1 / 2 ∧ ω.im ^ 2 = 3 / 4 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.one_re, Complex.zero_re, Complex.add_im,
    Complex.mul_im, Complex.one_im, Complex.zero_im] at hre him
  have him' : ω.im * (2 * ω.re + 1) = 0 := by linarith
  rcases mul_eq_zero.mp him' with h0 | h0
  · exfalso
    rw [h0] at hre
    nlinarith [sq_nonneg (ω.re + 1 / 2)]
  · have hx : ω.re = -1 / 2 := by linarith
    refine ⟨hx, ?_⟩
    rw [hx] at hre
    nlinarith

/-- A cube root of unity has `normSq = 1`. -/
theorem normSq_cube_root {ω : ℂ} (h : ω ^ 3 = 1) : Complex.normSq ω = 1 := by
  have h1 : Complex.normSq ω ^ 3 = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg ω) (by norm_num)).mp h1

/-- The real and imaginary parts of a cube. -/
theorem cube_re_im (z : ℂ) : (z ^ 3).re = z.re ^ 3 - 3 * z.re * z.im ^ 2 ∧
    (z ^ 3).im = 3 * z.re ^ 2 * z.im - z.im ^ 3 := by
  constructor <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

/-- **The argument step** of Theorem 9.9(ii) and Lemma 9.11: if `a, b > 0`, `ω³ = 1` and `(a + bω)³` is a positive
real, then `ω = 1`. (For `ω ≠ 1` the argument of `a + bω` lies strictly between `0` and `±2π/3`.) -/
theorem cube_pos_forces_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {ω : ℂ} (hω : ω ^ 3 = 1) {r : ℝ} (hr : 0 < r)
    (h : ((a : ℂ) + b * ω) ^ 3 = r) : ω = 1 := by
  rcases cube_root_cases hω with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨hre, him⟩ := primitive_re_im h1
    obtain ⟨c1, c2⟩ := cube_re_im ((a : ℂ) + b * ω)
    have hzre : ((a : ℂ) + b * ω).re = a + b * ω.re := by simp
    have hzim : ((a : ℂ) + b * ω).im = b * ω.im := by simp
    rw [h, hzre, hzim, Complex.ofReal_re] at c1
    rw [h, hzre, hzim, Complex.ofReal_im] at c2
    rw [hre] at c1 c2
    set y := ω.im with hy
    have hy0 : y ≠ 0 := by
      intro h0; rw [h0] at him; norm_num at him
    have hv : b * y ≠ 0 := mul_ne_zero hb.ne' hy0
    -- the imaginary part: `v (3u² − v²) = 0` with `u = a − b/2`, `v = b y`
    have e1 : (b * y) * (3 * (a + b * (-1 / 2)) ^ 2 - (b * y) ^ 2) = 0 := by linear_combination -c2
    have e2 : 3 * (a + b * (-1 / 2)) ^ 2 = (b * y) ^ 2 := by
      have := (mul_eq_zero.mp e1).resolve_left hv
      linarith
    have hyy : (b * y) ^ 2 = 3 / 4 * b ^ 2 := by rw [mul_pow, him]; ring
    have e3 : a * (a - b) = 0 := by nlinarith
    rcases mul_eq_zero.mp e3 with h3 | h3
    · linarith
    · have hab : a = b := by linarith
      rw [hab, hyy] at c1
      nlinarith [pow_pos hb 3]

/-- If `ω³ = 1`, `b ≠ 0` and `a + bω` is real, then `ω = 1`. -/
theorem real_forces_one {a b : ℝ} (hb : b ≠ 0) {ω : ℂ} (hω : ω ^ 3 = 1) {r : ℝ} (h : (a : ℂ) + b * ω = r) :
    ω = 1 := by
  rcases cube_root_cases hω with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨-, him⟩ := primitive_re_im h1
    have := congrArg Complex.im h
    simp at this
    rcases this with h0 | h0
    · exact hb h0
    · rw [h0] at him; norm_num at him

/-! ## H9.1, Lemma 9.1 -/

/-- **Lemma 9.1.** For a finite set `S` of bodies, a symmetric relation `F` ("the force of `l` on `k` is minimal")
and antisymmetric leading coefficients `Z k l = −Z l k` of the forces, the sum of the initial forms
`δ_k ĉ_k − Σ_{l ∈ S, F k l} m_l Z_kl` weighted by the masses is `Σ_{k ∈ S, δ_k} m_k ĉ_k`. -/
theorem ssum {K ι : Type*} [Field K] [CharZero K] (S : Finset ι) (m c : ι → K) (δ : ι → Prop) [DecidablePred δ]
    (F : ι → ι → Prop) [DecidableRel F] (hF : ∀ k l, F k l → F l k) (Z : ι → ι → K)
    (hZ : ∀ k l, Z k l = -Z l k) :
    (∑ k ∈ S, m k * ((if δ k then c k else 0) - ∑ l ∈ S.filter (F k), m l * Z k l)) =
      ∑ k ∈ S.filter δ, m k * c k := by
  set T := ∑ k ∈ S, ∑ l ∈ S, if F k l then m k * (m l * Z k l) else 0 with hT
  have hT1 : (∑ k ∈ S, m k * ∑ l ∈ S.filter (F k), m l * Z k l) = T := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  have hT2 : T = -T := by
    calc T = ∑ l ∈ S, ∑ k ∈ S, (if F k l then m k * (m l * Z k l) else 0) := Finset.sum_comm
      _ = ∑ k ∈ S, ∑ l ∈ S, (if F l k then m l * (m k * Z l k) else 0) := rfl
      _ = ∑ k ∈ S, ∑ l ∈ S, -(if F k l then m k * (m l * Z k l) else 0) := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          by_cases h : F k l
          · have h' := hF k l h
            simp only [h, h', ↓reduceIte]
            rw [hZ l k]; ring
          · have h' : ¬ F l k := fun h' => h (hF l k h')
            simp only [h, h', ↓reduceIte, neg_zero]
      _ = -T := by simp [hT, Finset.sum_neg_distrib]
  have hT0 : T = 0 := by
    have : (2 : K) * T = 0 := by linear_combination hT2
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  rw [Finset.sum_filter]
  simp only [mul_sub, Finset.sum_sub_distrib, hT1, hT0, sub_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/-- **Lemma 9.1**, the conclusion: if every initial form vanishes, `Σ_{k ∈ S, δ_k} m_k ĉ_k = 0`. -/
theorem ssum_zero {K ι : Type*} [Field K] [CharZero K] (S : Finset ι) (m c : ι → K) (δ : ι → Prop)
    [DecidablePred δ] (F : ι → ι → Prop) [DecidableRel F] (hF : ∀ k l, F k l → F l k) (Z : ι → ι → K)
    (hZ : ∀ k l, Z k l = -Z l k)
    (h0 : ∀ k ∈ S, (if δ k then c k else 0) - ∑ l ∈ S.filter (F k), m l * Z k l = 0) :
    ∑ k ∈ S.filter δ, m k * c k = 0 := by
  rw [← ssum S m c δ F hF Z hZ]
  exact Finset.sum_eq_zero fun k hk => by rw [h0 k hk, mul_zero]

/-! ## H9.2, Lemmas 9.2–9.4: exponent comparisons -/

/-- **Lemma 9.2**, first case (`O` below `t′`): `a_k ≥ ζ_kl`, `ζ_kl ≤ ζ_pq` and `a_p ≤ ζ_pq` give
`a_k − (3/2)ζ_kl ≥ a_p − (3/2)ζ_pq`, strictly if `ζ_kl < ζ_pq` or `a_p < ζ_pq`. -/
theorem handT_le_of_below (ak zkl zpq ap : ℚ) (h1 : zkl ≤ ak) (h2 : zkl ≤ zpq) (h3 : ap ≤ zpq) :
    ap - 3 / 2 * zpq ≤ ak - 3 / 2 * zkl ∧ (zkl < zpq ∨ ap < zpq → ap - 3 / 2 * zpq < ak - 3 / 2 * zkl) := by
  refine ⟨by linarith, fun h => ?_⟩
  rcases h with h | h <;> linarith

/-- **Lemma 9.2**, second case (`O` not below `t′`, so `a_k = a_p`): `ζ_kl ≤ ζ_pq` gives the same inequality,
strictly if `ζ_kl < ζ_pq`. -/
theorem handT_le_of_not_below (ak zkl zpq ap : ℚ) (h1 : ak = ap) (h2 : zkl ≤ zpq) :
    ap - 3 / 2 * zpq ≤ ak - 3 / 2 * zkl ∧ (zkl < zpq → ap - 3 / 2 * zpq < ak - 3 / 2 * zkl) :=
  ⟨by linarith, fun h => by linarith⟩

/-- **Lemma 9.3**: `a_k ≥ ζ_kl`, `b_k ≥ ω_kl` and `x_kl = (ζ_kl + ω_kl)/2 > 0` give `a_k + b_k ≥ 2x_kl > 0 = e(E)`. -/
theorem handP_pos (ak bk zkl wkl : ℚ) (h1 : zkl ≤ ak) (h2 : wkl ≤ bk) (hx : 0 < (zkl + wkl) / 2) :
    2 * ((zkl + wkl) / 2) ≤ ak + bk ∧ 0 < ak + bk :=
  ⟨by linarith, by linarith⟩

/-- **(x2)**: on a `z`-stroke `3x − 2 = ζ ≥ min(a_k, a_l) > −2` gives `x > 0`. -/
theorem forced_x2 (x z ak al : ℚ) (h1 : z = 3 * x - 2) (h2 : min ak al ≤ z) (hk : -2 < ak) (hl : -2 < al) :
    0 < x := by
  have : -2 < min ak al := lt_min hk hl
  linarith

/-- **(x4)**: `−(ζ + 3ω)/2 = e(Z_kl) < a_k = ζ` gives `x = (ζ + ω)/2 > 0`. -/
theorem forced_x4 (z w ak : ℚ) (h1 : -(z + 3 * w) / 2 < ak) (h2 : ak = z) : 0 < (z + w) / 2 := by
  linarith

/-- **Lemma 9.4**, the last step: `(Σ_{k ∈ I} m_k) X ≠ 0` for positive masses, nonempty `I` and `X ≠ 0`. -/
theorem handC_ne_zero {ι : Type*} (I : Finset ι) (hI : I.Nonempty) (m : ι → ℝ) (hm : ∀ k ∈ I, 0 < m k) (X : ℂ)
    (hX : X ≠ 0) : ((∑ k ∈ I, m k : ℝ) : ℂ) * X ≠ 0 := by
  have : 0 < ∑ k ∈ I, m k := Finset.sum_pos hm hI
  exact mul_ne_zero (by exact_mod_cast this.ne') hX

/-! ## H9.3, Lemmas 9.5 and 9.6 -/

/-- **Lemma 9.5.** With `P = P_kl`: the initial form `ĉ_l − m_k P³ ĉ_l` of the `c`-equation of `l` (by (i)) and the
initial form `ĉ′_l − m_k P³ (ĉ′_l − ĉ′_k)` of its `c′`-equation (by (ii)) cannot both vanish when `ĉ_l, ĉ′_k ≠ 0`:
the first gives `m_k P³ = 1`, and then the second is `ĉ′_k`. -/
theorem handB0 {K : Type*} [Field K] (mk P cl cl' ck' : K) (hcl : cl ≠ 0) (hck' : ck' ≠ 0)
    (h1 : cl - mk * P ^ 3 * cl = 0) (h2 : cl' - mk * P ^ 3 * (cl' - ck') = 0) : False := by
  have hP : mk * P ^ 3 = 1 := by
    have : cl * (1 - mk * P ^ 3) = 0 := by linear_combination h1
    linear_combination -((mul_eq_zero.mp this).resolve_left hcl)
  apply hck'
  linear_combination h2 + (cl' - ck') * hP

/-- **Lemma 9.6**, colour `c`: `m_k ĉ_k + m_l ĉ_l = 0` (Lemma 9.1) and the initial form
`ĉ_k − m_l P³ (ĉ_k − ĉ_l)` of the equation of `k` give `(m_k + m_l) P³ = 1`. -/
theorem handK_c {K : Type*} [Field K] (mk ml P ck cl : K) (hck : ck ≠ 0)
    (hs : mk * ck + ml * cl = 0) (h : ck - ml * P ^ 3 * (ck - cl) = 0) : (mk + ml) * P ^ 3 = 1 := by
  have : ck * (1 - (mk + ml) * P ^ 3) = 0 := by linear_combination h - P ^ 3 * hs
  linear_combination -((mul_eq_zero.mp this).resolve_left hck)

/-- **Lemma 9.6**, colour `c′`: with `(m_p + m_q) P³ = 1`, the initial form `ĉ′_p − m_q P³ (ĉ′_p − ĉ′_q)` of the
equation of `p` is `P³ (m_p ĉ′_p + m_q ĉ′_q)`, so `m_p ĉ′_p + m_q ĉ′_q = 0`. -/
theorem handK_c' {K : Type*} [Field K] (mp mq P cp cq : K) (hP : (mp + mq) * P ^ 3 = 1)
    (h : cp - mq * P ^ 3 * (cp - cq) = 0) : mp * cp + mq * cq = 0 := by
  have hP0 : P ^ 3 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hP; exact zero_ne_one hP
  have : P ^ 3 * (mp * cp + mq * cq) = 0 := by linear_combination h + cp * hP
  exact (mul_eq_zero.mp this).resolve_left hP0

/-- **Lemma 9.6.** The initial forms cannot vanish together. Colour `c`: Lemma 9.1 for `{k, l}` and the initial form
of the equation of `k`. Colour `c′`, with the labelling `p = k`, `q = l` (the other labelling is the same statement
with `k`, `l` exchanged; by (i) both `A^c_k` and `A^c_l` have the required form): the initial form of the equation of
`p`, and that of `q`, `ĉ′_q − m_p P³ (ĉ′_q − ĉ′_p) − f`, where `f = m_j ⟨Z^{c′}_{qj}⟩ ≠ 0` is the leading coefficient
of the force of the body `j`; it equals `−f`. -/
theorem handK {K : Type*} [Field K] (mk ml P ck cl cp cq f : K) (hck : ck ≠ 0) (hf : f ≠ 0)
    (hs : mk * ck + ml * cl = 0) (hk : ck - ml * P ^ 3 * (ck - cl) = 0)
    (hp : cp - ml * P ^ 3 * (cp - cq) = 0) (hq : cq - mk * P ^ 3 * (cq - cp) - f = 0) : False := by
  have hP := handK_c mk ml P ck cl hck hs hk
  have hpq := handK_c' mk ml P cp cq hP hp
  apply hf
  linear_combination -hq + P ^ 3 * hpq - cq * hP

/-! ## H9.4, Lemma 9.7 -/

/-- **Lemma 9.7**, the relations. With `X_k = ĉ_k`, `Y_k = ĉ′_k` (`a, b` only), the hypotheses are Lemma 9.1 in both
colours, the initial forms of the `c′`- and `c`-equations of `s` and of the `c′`-equation of `a`, and the three
distance rows (the leading coefficients of `c′_b − c′_s`, `c′_s − c′_a` are `Y_b`, `−Y_a`). Then
`P_sa³ = P_sb³`, `P_sa³ M_T = 1`, `P_ab³ M_T = 1` (`M_T = m_a + m_b + m_s`), and with the cube roots of unity
`e_bs = (P_ab/P_bs)²`, `e_sa = (P_ab/P_sa)²` (the paper's `ε_bs/ε_ab`, `ε_sa/ε_ab`),
`m_a m_b = m_b(m_a + m_b) e_bs + m_a(m_a + m_b) e_sa`. -/
theorem handL_relations {K : Type*} [Field K] (ma mb ms Xa Xb Xs Ya Yb Pab Pbs Psa : K)
    (hma : ma ≠ 0) (hmb : mb ≠ 0) (hab : ma + mb ≠ 0) (hYa : Ya ≠ 0) (hXs : Xs ≠ 0)
    (hY : ma * Ya + mb * Yb = 0) (hs' : ma * Psa ^ 3 * Ya + mb * Pbs ^ 3 * Yb = 0)
    (hX : ma * Xa + mb * Xb + ms * Xs = 0)
    (hs : Xs - ma * Psa ^ 3 * (Xs - Xa) - mb * Pbs ^ 3 * (Xs - Xb) = 0)
    (ha' : Ya - ms * Psa ^ 3 * Ya - mb * Pab ^ 3 * (Ya - Yb) = 0)
    (dab : Pab ^ 2 * (Xa - Xb) * (Ya - Yb) = 1) (dbs : Pbs ^ 2 * (Xb - Xs) * Yb = 1)
    (dsa : Psa ^ 2 * (Xs - Xa) * (-Ya) = 1) :
    Psa ^ 3 = Pbs ^ 3 ∧ Psa ^ 3 * (ma + mb + ms) = 1 ∧ Pab ^ 3 * (ma + mb + ms) = 1 ∧
      ((Pab / Pbs) ^ 2) ^ 3 = 1 ∧ ((Pab / Psa) ^ 2) ^ 3 = 1 ∧
      ma * mb = mb * (ma + mb) * (Pab / Pbs) ^ 2 + ma * (ma + mb) * (Pab / Psa) ^ 2 := by
  have hPbs0 : Pbs ≠ 0 := by intro h0; rw [h0] at dbs; simp at dbs
  have hPsa0 : Psa ≠ 0 := by intro h0; rw [h0] at dsa; simp at dsa
  -- `P_sa³ = P_sb³`
  have h1 : Psa ^ 3 = Pbs ^ 3 := by
    have : ma * Ya * (Psa ^ 3 - Pbs ^ 3) = 0 := by linear_combination hs' - Pbs ^ 3 * hY
    linear_combination (mul_eq_zero.mp this).resolve_left (mul_ne_zero hma hYa)
  -- `Q = 1/M_T`
  have h2 : Psa ^ 3 * (ma + mb + ms) = 1 := by
    have : Xs * (1 - Psa ^ 3 * (ma + mb + ms)) = 0 := by
      linear_combination hs - Psa ^ 3 * hX - mb * (Xs - Xb) * h1
    linear_combination -((mul_eq_zero.mp this).resolve_left hXs)
  -- `P_ab³ = 1/M_T`
  have h3' : mb * Ya * (ma + mb) * (Psa ^ 3 - Pab ^ 3) = 0 := by
    linear_combination mb * ha' - mb * Pab ^ 3 * hY + mb * Ya * h2
  have h3e : Psa ^ 3 = Pab ^ 3 := by
    linear_combination (mul_eq_zero.mp h3').resolve_left (mul_ne_zero (mul_ne_zero hmb hYa) hab)
  have h3 : Pab ^ 3 * (ma + mb + ms) = 1 := by rw [← h3e]; exact h2
  -- the cube roots of unity
  have hc1 : ((Pab / Pbs) ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, div_pow, ← h3e, h1, div_self (pow_ne_zero 3 hPbs0),
      one_pow]
  have hc2 : ((Pab / Psa) ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, div_pow, ← h3e, div_self (pow_ne_zero 3 hPsa0),
      one_pow]
  -- the sum of the separations `ξ` vanishes
  have hE : Pbs ^ 2 * Psa ^ 2 * Yb * Ya + Pab ^ 2 * Psa ^ 2 * (Ya - Yb) * Ya -
      Pab ^ 2 * Pbs ^ 2 * (Ya - Yb) * Yb = 0 := by
    linear_combination (-(Pbs ^ 2 * Psa ^ 2 * Yb * Ya)) * dab + (-(Pab ^ 2 * Psa ^ 2 * (Ya - Yb) * Ya)) * dbs +
      (Pab ^ 2 * Pbs ^ 2 * (Ya - Yb) * Yb) * dsa
  have hF : Ya ^ 2 * (mb * (ma + mb) * Pab ^ 2 * Psa ^ 2 + ma * (ma + mb) * Pab ^ 2 * Pbs ^ 2 -
      ma * mb * Pbs ^ 2 * Psa ^ 2) = 0 := by
    linear_combination mb ^ 2 * hE - (Pbs ^ 2 * Psa ^ 2 * mb * Ya - Pab ^ 2 * Psa ^ 2 * mb * Ya -
      Pab ^ 2 * Pbs ^ 2 * ((2 * ma + mb) * Ya - (ma * Ya + mb * Yb))) * hY
  have hG := (mul_eq_zero.mp hF).resolve_left (pow_ne_zero 2 hYa)
  refine ⟨h1, h2, h3, hc1, hc2, ?_⟩
  rw [div_pow, div_pow]
  field_simp
  linear_combination -hG

/-- **Lemma 9.7**, the last step: for positive `m_a, m_b` and cube roots of unity `ε_ab, ε_bs, ε_sa`,
`m_a m_b ε_ab ≠ m_b(m_a + m_b) ε_bs + m_a(m_a + m_b) ε_sa`. (If `ε_bs = ε_sa` the right side has modulus
`(m_a + m_b)²`; otherwise its squared modulus is `β² + γ² − βγ ≥ βγ` with `β, γ` its coefficients.) -/
theorem handL_impossible {ma mb : ℝ} (ha : 0 < ma) (hb : 0 < mb) {e1 e2 e3 : ℂ} (h1 : e1 ^ 3 = 1)
    (h2 : e2 ^ 3 = 1) (h3 : e3 ^ 3 = 1) :
    (ma : ℂ) * mb * e1 ≠ mb * (ma + mb) * e2 + ma * (ma + mb) * e3 := by
  intro h
  have he2 : e2 ≠ 0 := by intro h0; rw [h0] at h2; norm_num at h2
  set u := e3 / e2 with hu
  have hu3 : u ^ 3 = 1 := by rw [hu, div_pow, h3, h2, div_one]
  set β : ℝ := mb * (ma + mb) with hβ
  set γ : ℝ := ma * (ma + mb) with hγ
  have hrhs : (mb : ℂ) * (ma + mb) * e2 + ma * (ma + mb) * e3 = e2 * ((β : ℂ) + (γ : ℂ) * u) := by
    rw [hu, hβ, hγ]; push_cast; field_simp
  have hn := congrArg Complex.normSq h
  rw [hrhs, map_mul, map_mul, map_mul, normSq_cube_root h1, normSq_cube_root h2, mul_one, one_mul,
    Complex.normSq_ofReal, Complex.normSq_ofReal] at hn
  have hnsq : Complex.normSq ((β : ℂ) + (γ : ℂ) * u) = (β + γ * u.re) ^ 2 + (γ * u.im) ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [hnsq] at hn
  have hβ0 : 0 < β := by positivity
  have hγ0 : 0 < γ := by positivity
  have hbg : β * γ = ma * mb * (ma + mb) ^ 2 := by rw [hβ, hγ]; ring
  have hk : ma * mb < (ma + mb) ^ 2 := by nlinarith [mul_pos ha hb]
  have hk2 : (ma * mb) ^ 2 < ma * mb * (ma + mb) ^ 2 := by
    have := mul_pos ha hb
    nlinarith
  rcases cube_root_cases hu3 with h0 | h0
  · rw [h0] at hn
    simp only [Complex.one_re, Complex.one_im, mul_one, mul_zero] at hn
    nlinarith [sq_nonneg (β - γ)]
  · obtain ⟨hre, him⟩ := primitive_re_im h0
    rw [hre, mul_pow, him] at hn
    nlinarith [sq_nonneg (β - γ)]

/-- **Lemma 9.7**: at positive masses the relations of `handL_relations` are impossible, so the cell is excluded. -/
theorem handL (ma mb ms : ℝ) (ha : 0 < ma) (hb : 0 < mb) (Xa Xb Xs Ya Yb Pab Pbs Psa : ℂ)
    (hYa : Ya ≠ 0) (hXs : Xs ≠ 0)
    (hY : (ma : ℂ) * Ya + mb * Yb = 0) (hs' : (ma : ℂ) * Psa ^ 3 * Ya + mb * Pbs ^ 3 * Yb = 0)
    (hX : (ma : ℂ) * Xa + mb * Xb + ms * Xs = 0)
    (hs : Xs - ma * Psa ^ 3 * (Xs - Xa) - mb * Pbs ^ 3 * (Xs - Xb) = 0)
    (ha' : Ya - ms * Psa ^ 3 * Ya - mb * Pab ^ 3 * (Ya - Yb) = 0)
    (dab : Pab ^ 2 * (Xa - Xb) * (Ya - Yb) = 1) (dbs : Pbs ^ 2 * (Xb - Xs) * Yb = 1)
    (dsa : Psa ^ 2 * (Xs - Xa) * (-Ya) = 1) : False := by
  have hma : (ma : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hmb : (mb : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hab : (ma : ℂ) + mb ≠ 0 := by exact_mod_cast (add_pos ha hb).ne'
  obtain ⟨-, -, -, hc1, hc2, hrel⟩ :=
    handL_relations (ma : ℂ) mb ms Xa Xb Xs Ya Yb Pab Pbs Psa hma hmb hab hYa hXs hY hs' hX hs ha' dab dbs dsa
  exact handL_impossible ha hb (one_pow 3) hc1 hc2 (by rw [mul_one]; exact hrel)

/-! ## H9.5, Lemma 9.8 -/

/-- Sums over ordered pairs of a symmetric weight times an antisymmetric expression vanish. -/
theorem sum_symm_antisymm {R ι : Type*} [CommRing R] (S : Finset ι) (g h : ι → ι → R)
    (hg : ∀ t u, g t u = g u t) : (∑ t ∈ S, ∑ u ∈ S, g t u * (h t u - h u t)) = 0 := by
  have e : (∑ t ∈ S, ∑ u ∈ S, g t u * h u t) = ∑ t ∈ S, ∑ u ∈ S, g t u * h t u := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
    rw [hg]
  simp only [mul_sub, Finset.sum_sub_distrib, e, sub_self]

/-- **Lemma 9.8.** For a finite set `S` of bodies, the symmetric `P` and any `ξ`, `η`, with
`Φ^z_t = Σ_{t′ ∈ S ∖ t} m_{t′} P_{tt′}³ (ξ_t − ξ_{t′})` and `Φ^w_t` likewise:
`Σ m_t Φ^z_t = Σ m_t Φ^w_t = Σ m_t (ξ_t Φ^w_t − η_t Φ^z_t) = 0`. -/
theorem cliquesum {R ι : Type*} [CommRing R] [DecidableEq ι] (S : Finset ι) (m ξ η : ι → R) (P : ι → ι → R)
    (hP : ∀ t u, P t u = P u t) :
    (∑ t ∈ S, m t * ∑ u ∈ S.erase t, m u * P t u ^ 3 * (ξ t - ξ u)) = 0 ∧
    (∑ t ∈ S, m t * ∑ u ∈ S.erase t, m u * P t u ^ 3 * (η t - η u)) = 0 ∧
    (∑ t ∈ S, m t * (ξ t * ∑ u ∈ S.erase t, m u * P t u ^ 3 * (η t - η u) -
        η t * ∑ u ∈ S.erase t, m u * P t u ^ 3 * (ξ t - ξ u))) = 0 := by
  have er : ∀ (a : ι → R) (t : ι), (∑ u ∈ S.erase t, m u * P t u ^ 3 * (a t - a u)) =
      ∑ u ∈ S, m u * P t u ^ 3 * (a t - a u) := fun a t => by
    by_cases ht : t ∈ S
    · exact Finset.sum_erase S (by simp)
    · rw [Finset.erase_eq_of_notMem ht]
  have hg : ∀ t u, m t * m u * P t u ^ 3 = m u * m t * P u t ^ 3 := fun t u => by rw [hP]; ring
  have one : ∀ a : ι → R, (∑ t ∈ S, m t * ∑ u ∈ S.erase t, m u * P t u ^ 3 * (a t - a u)) = 0 := by
    intro a
    have := sum_symm_antisymm S (fun t u => m t * m u * P t u ^ 3) (fun t _ => a t) hg
    rw [← this]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [er a t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  refine ⟨one ξ, one η, ?_⟩
  have := sum_symm_antisymm S (fun t u => m t * m u * P t u ^ 3) (fun t u => η t * ξ u) hg
  rw [← this]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [er η t, er ξ t, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

/-! ## H9.13, Lemmas 9.16 and 9.17 -/

/-- **Lemma 9.16(b)**: if `x_K = 0`, then `ζ = −2` on the pairs, and `ζ_kl ≥ min(a_k, a_l) ≥ −2` makes one body of
each pair `z`-circled. -/
theorem clique_x_zero (x z ak al : ℚ) (hz : z = 3 * x - 2) (hx : x = 0) (hm : min ak al ≤ z) (hk : -2 ≤ ak)
    (hl : -2 ≤ al) : z = -2 ∧ (ak = -2 ∨ al = -2) := by
  have hz' : z = -2 := by rw [hz, hx]; norm_num
  refine ⟨hz', ?_⟩
  rcases min_choice ak al with h | h
  · left; rw [h] at hm; linarith
  · right; rw [h] at hm; linarith

/-- **Lemma 9.17**: the internal separations of a clean clique have exponents larger than its internal order:
`1 > −2`, and for `x_K > 0`, `3x_K − 2 > −2` and `2 − x_K > 2 − 4x_K`. -/
theorem clique_orders (x : ℚ) (hx : 0 < x) : (-2 : ℚ) < 1 ∧ -2 < 3 * x - 2 ∧ 2 - 4 * x < 2 - x :=
  ⟨by norm_num, by linarith, by linarith⟩

/-! ## H9.14, Lemma 9.20 -/

/-- **Lemma 9.20.** With `Y_k = ⟨c_k − c_s⟩`, `ξ` the common leading coefficient of `c′_s − c′_a`, `c′_s − c′_b`: the
relations (i) `m_a Y_a + m_b Y_b = 0`, (ii) `m_a P_sa³ Y_a + m_b P_sb³ Y_b = 0` and the distance rows
`P_sk² (−Y_k) ξ = 1` give `m_a P_sa + m_b P_sb = 0`, and then the computation of Lemma 6.3 gives `m_a³ + m_b³ = 0`. -/
theorem handP4 {K : Type*} [Field K] (ma mb Ya Yb ξ Psa Psb : K) (h1 : ma * Ya + mb * Yb = 0)
    (h2 : ma * Psa ^ 3 * Ya + mb * Psb ^ 3 * Yb = 0) (hda : Psa ^ 2 * (-Ya) * ξ = 1)
    (hdb : Psb ^ 2 * (-Yb) * ξ = 1) : ma * Psa = -(mb * Psb) ∧ ma ^ 3 + mb ^ 3 = 0 := by
  have h4 : ma * Psa = -(mb * Psb) := by
    linear_combination -ξ * h2 - ma * Psa * hda - mb * Psb * hdb
  exact ⟨h4, binary_masses ma mb Ya Yb ξ Psa Psb h1 (by linear_combination -hda) (by linear_combination -hdb) h4⟩

/-- **Lemma 9.20** at positive masses: the relations are impossible, so the cell is excluded. -/
theorem handP4_pos (ma mb : ℝ) (ha : 0 < ma) (hb : 0 < mb) (Ya Yb ξ Psa Psb : ℂ)
    (h1 : (ma : ℂ) * Ya + mb * Yb = 0) (h2 : (ma : ℂ) * Psa ^ 3 * Ya + mb * Psb ^ 3 * Yb = 0)
    (hda : Psa ^ 2 * (-Ya) * ξ = 1) (hdb : Psb ^ 2 * (-Yb) * ξ = 1) : False := by
  have h := (handP4 (ma : ℂ) mb Ya Yb ξ Psa Psb h1 h2 hda hdb).2
  have h' : ((ma ^ 3 + mb ^ 3 : ℝ) : ℂ) = 0 := by push_cast; exact h
  have : ma ^ 3 + mb ^ 3 = 0 := by exact_mod_cast h'
  have : 0 < ma ^ 3 + mb ^ 3 := by positivity
  linarith

end Lean6.Special.Hand.Sec9
