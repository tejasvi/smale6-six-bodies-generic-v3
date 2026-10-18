import Lean6.Special.D98.Lemma69Check
import Lean6.Special.Comp.D98.RootsRun

/-!
# The check of Lemma 6.13 at `(1, 2, 7)` (the paragraph after the lemma)

* **`check_1_2_7`**: every root `t` of `S_μ`, `μ = (1, 2, 7)`, has `ℓ₁ℓ₂ℓ₃(t) ≠ 0` and
  `ρ(t) ≥ 0.7641079385 > 1/√2`; **`check_1_2_7_min`**: some root (a root of `N₁₁`) has `ρ(t) ≤ 0.7641079386`, so the
  minimum of `ρ` over the roots lies in `[0.7641079385, 0.7641079386]`.
* **`check_1_2_8`**: at `μ = (1, 2, 8)`, `ρ(t) ≥ 0.7990358445` at every root; **`check_rho_product`**:
  `ρ(t) ρ'(t') > 1/2` for roots `t` at `(1, 2, 7)` and `t'` at `(1, 2, 8)`.

The count of the roots (`34` with multiplicity, `32` distinct) is `lemma69_check_1_2_7`. Method: for each of the eight
factors `f` of `S_μ` (degree `d`) and each of `d` centres `c` (Gaussian rationals proposed by mpmath),
`|f(c)| < |lc f| r^d` gives a root in `D(c, r)` (from the factorization of `f` over `ℂ`); the `d` disks are disjoint, so
they hold `d` distinct roots, which are all the roots of `f`; on each disk exact bounds of `|ℓ_k|` bound `ρ`.
Not checked: the direct evaluation of all `1024 × 256` signed sums (`≥ 0.4537`).
-/

namespace Lean6.Special.D98

open Polynomial Lean6.Special.Comp.D98 Complex

/-! ## Gaussian rationals -/

/-- `(x, y) ↦ x + y i`. -/
noncomputable def toC (x : GQ) : ℂ := (x.1 : ℂ) + (x.2 : ℂ) * I

theorem toC_gmul (x y : GQ) : toC (gmul x y) = toC x * toC y := by
  simp only [toC, gmul]
  push_cast
  linear_combination (-(x.2 : ℂ) * (y.2 : ℂ)) * I_sq

theorem norm_sq_toC (x : GQ) : ‖toC x‖ ^ 2 = ((gnorm2 x : ℚ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [toC, gnorm2]

theorem hornerQ_sound (f : UP) (c : GQ) :
    toC (hornerQ f c) = ((toPoly f).map (Int.castRingHom ℂ)).eval (toC c) := by
  induction f with
  | nil => simp [hornerQ, toC]
  | cons a rest ih =>
    have e : toC (hornerQ (a :: rest) c) = (a : ℂ) + toC (gmul c (hornerQ rest c)) := by
      simp only [hornerQ, toC]; push_cast; ring
    rw [e, toC_gmul, ih]
    simp

/-! ## Roots in disks -/

theorem pow_card_le_prod_map {s : Multiset ℂ} {g : ℂ → ℝ} {r : ℝ} (hr : 0 ≤ r) (h : ∀ x ∈ s, r ≤ g x) :
    r ^ Multiset.card s ≤ (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ]
    have ha := h a (Multiset.mem_cons_self a s)
    have ih' := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    rw [mul_comm]
    exact mul_le_mul ha ih' (pow_nonneg hr _) (hr.trans ha)

/-- **A small value at `c` gives a root near `c`.** -/
theorem exists_root_near (g : ℂ[X]) (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (h : ‖g.eval c‖ < ‖g.leadingCoeff‖ * r ^ g.natDegree) : ∃ α ∈ g.roots, ‖c - α‖ ≤ r := by
  by_contra hall
  push Not at hall
  have hcard : Multiset.card g.roots = g.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have he : g.eval c = g.leadingCoeff * (g.roots.map fun α => c - α).prod := by
    conv_lhs => rw [← hfac]
    simp [eval_multiset_prod, Multiset.map_map, Function.comp_def]
  have hn : ‖g.eval c‖ = ‖g.leadingCoeff‖ * (g.roots.map fun α => ‖c - α‖).prod := by
    rw [he, norm_mul, Multiset.norm_prod, Multiset.map_map]
    rfl
  have hp := pow_card_le_prod_map (g := fun α => ‖c - α‖) hr (fun x hx => (hall x hx).le)
  rw [hcard] at hp
  rw [hn] at h
  have := mul_le_mul_of_nonneg_left hp (norm_nonneg g.leadingCoeff)
  linarith

/-- **Disjoint disks with small values hold all the roots.** -/
theorem roots_in_disks (g : ℂ[X]) {n : ℕ} (hn : g.natDegree = n) (c : Fin n → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (h1 : ∀ i, ‖g.eval (c i)‖ < ‖g.leadingCoeff‖ * r ^ n) (h2 : ∀ i j, i ≠ j → 2 * r < ‖c i - c j‖) :
    ∀ β ∈ g.roots, ∃ i, ‖β - c i‖ ≤ r := by
  have hroot : ∀ i, ∃ α ∈ g.roots, ‖c i - α‖ ≤ r := fun i => exists_root_near g (c i) hr (by rw [hn]; exact h1 i)
  choose α hα hαr using hroot
  have hinj : Function.Injective α := by
    intro i j hij
    by_contra hne
    have := h2 i j hne
    have e : c i - c j = (c i - α i) - (c j - α j) := by rw [hij]; ring
    have := norm_sub_le (c i - α i) (c j - α j)
    rw [← e] at this
    linarith [hαr i, hαr j]
  set s : Multiset ℂ := Finset.univ.val.map α
  have hnd : s.Nodup := Multiset.Nodup.map hinj Finset.univ.nodup
  have hsub : s ≤ g.roots := by
    rw [Multiset.le_iff_subset hnd]
    intro x hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    exact hα i
  have hcard : Multiset.card g.roots ≤ Multiset.card s := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hn]
    simp [s]
  have heq := Multiset.eq_of_le_of_card_le hsub hcard
  intro β hβ
  rw [← heq] at hβ
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hβ
  exact ⟨i, by rw [norm_sub_rev]; exact hαr i⟩

/-! ## `ρ` on a disk -/

/-- `A_j(t) = μ_j |Λ_j(t)|^{1/2}` for real masses. -/
noncomputable def AjG (μ : Fin 3 → ℝ) (t : ℂ) (j : Fin 3) : ℝ := μ j * Real.sqrt ‖Lam (fun i => (μ i : ℂ)) t j‖

/-- `ρ(t) = A₃ / (A₁ + A₂ + A₃)`. -/
noncomputable def rhoG (μ : Fin 3 → ℝ) (t : ℂ) : ℝ := AjG μ t 2 / (AjG μ t 0 + AjG μ t 1 + AjG μ t 2)

theorem ellOK_sound {p q : ℤ} {c : GQ} {r : ℚ} {l u : ℕ} (h : ellOK p q c r l u = true) {t : ℂ}
    (ht : ‖t - toC c‖ ≤ r) :
    0 < (l : ℝ) / 2 ^ 256 - |(q : ℝ)| * r ∧ (l : ℝ) / 2 ^ 256 - |(q : ℝ)| * r ≤ ‖(p : ℂ) + q * t‖ ∧
      ‖(p : ℂ) + q * t‖ ≤ (u : ℝ) / 2 ^ 256 + |(q : ℝ)| * r := by
  simp only [ellOK, KS, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  replace h1 := of_decide_eq_true h1
  replace h2 := of_decide_eq_true h2
  replace h3 := of_decide_eq_true h3
  have hc : toC (ellAt p q c) = (p : ℂ) + q * toC c := by
    simp only [toC, ellAt]; push_cast; ring
  set n := ‖(p : ℂ) + q * toC c‖
  have hn2 : n ^ 2 = ((gnorm2 (ellAt p q c) : ℚ) : ℝ) := by rw [← norm_sq_toC, hc]
  have hlam : (l : ℝ) / 2 ^ 256 ≤ n := by
    have h1' : (((l : ℚ) / 2 ^ 256 * ((l : ℚ) / 2 ^ 256) : ℚ) : ℝ) ≤ ((gnorm2 (ellAt p q c) : ℚ) : ℝ) := by
      exact_mod_cast h1
    rw [← hn2] at h1'
    push_cast at h1'
    nlinarith [norm_nonneg ((p : ℂ) + q * toC c), (by positivity : (0 : ℝ) ≤ (l : ℝ) / 2 ^ 256)]
  have hups : n ≤ (u : ℝ) / 2 ^ 256 := by
    have h2' : ((gnorm2 (ellAt p q c) : ℚ) : ℝ) ≤ (((u : ℚ) / 2 ^ 256 * ((u : ℚ) / 2 ^ 256) : ℚ) : ℝ) := by
      exact_mod_cast h2
    rw [← hn2] at h2'
    push_cast at h2'
    nlinarith [norm_nonneg ((p : ℂ) + q * toC c), (by positivity : (0 : ℝ) ≤ (u : ℝ) / 2 ^ 256)]
  have hq : ‖(q : ℂ) * (t - toC c)‖ ≤ |(q : ℝ)| * r := by
    rw [norm_mul, Complex.norm_intCast]
    exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  have e : (p : ℂ) + q * t = ((p : ℂ) + q * toC c) + (q : ℂ) * (t - toC c) := by ring
  have h3' : (0 : ℝ) < (l : ℝ) / 2 ^ 256 - |(q : ℝ)| * r := by
    have : ((0 : ℚ) : ℝ) < (((l : ℚ) / 2 ^ 256 - (q.natAbs : ℚ) * r : ℚ) : ℝ) := by exact_mod_cast h3
    push_cast at this
    rwa [Nat.cast_natAbs, Int.cast_abs] at this
  refine ⟨h3', ?_, ?_⟩
  · rw [e]
    have := norm_sub_norm_le ((p : ℂ) + q * toC c) (-((q : ℂ) * (t - toC c)))
    rw [sub_neg_eq_add, norm_neg] at this
    linarith
  · rw [e]
    have := norm_add_le ((p : ℂ) + q * toC c) ((q : ℂ) * (t - toC c))
    linarith

theorem ell_eqs (m1 m2 m3 : ℤ) (t : ℂ) :
    ell1 (fun i => ((![(m1 : ℝ), m2, m3] i : ℝ) : ℂ)) t = (m2 : ℂ) + m3 * t ∧
    ell2 (fun i => ((![(m1 : ℝ), m2, m3] i : ℝ) : ℂ)) t = ((m2 - (m1 + m2 + m3) : ℤ) : ℂ) + m3 * t ∧
    ell3 (fun i => ((![(m1 : ℝ), m2, m3] i : ℝ) : ℂ)) t = (m2 : ℂ) + ((m3 - (m1 + m2 + m3) : ℤ) : ℂ) * t := by
  simp only [ell1, ell2, ell3, Mtot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  push_cast
  refine ⟨rfl, by ring, by ring⟩

/-- **The bounds of `ρ` on a disk.** -/
theorem diskOK_sound {m1 m2 m3 : ℤ} (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) {θ r : ℚ} {D : Disk}
    (h : diskOK m1 m2 m3 θ r D = true) {t : ℂ} (ht : ‖t - toC D.c‖ ≤ r) :
    ell1 (fun i => ((![(m1 : ℝ), m2, m3] i : ℝ) : ℂ)) t * ell2 (fun i => ((![(m1 : ℝ), m2, m3] i : ℝ) : ℂ)) t *
        ell3 (fun i => ((![(m1 : ℝ), m2, m3] i : ℝ) : ℂ)) t ≠ 0 ∧
      (θ : ℝ) ≤ rhoG ![(m1 : ℝ), m2, m3] t := by
  simp only [diskOK, KS, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, hx1⟩, hx2⟩, hθ⟩ := h
  replace hx1 := of_decide_eq_true hx1
  replace hx2 := of_decide_eq_true hx2
  replace hθ := of_decide_eq_true hθ
  obtain ⟨E1, E2, E3⟩ := ell_eqs m1 m2 m3 t
  obtain ⟨p1, lo1, -⟩ := ellOK_sound e1 ht
  obtain ⟨p2, lo2, -⟩ := ellOK_sound e2 ht
  obtain ⟨-, -, up3⟩ := ellOK_sound e3 ht
  set μR : Fin 3 → ℝ := ![(m1 : ℝ), m2, m3]
  set μC : Fin 3 → ℂ := fun i => ((μR i : ℝ) : ℂ)
  set n1 := ‖ell1 μC t‖
  set n2 := ‖ell2 μC t‖
  set n3 := ‖ell3 μC t‖
  have hn1 : n1 = ‖(m2 : ℂ) + m3 * t‖ := by simp only [n1, μC, μR, E1]
  have hn2 : n2 = ‖((m2 - (m1 + m2 + m3) : ℤ) : ℂ) + m3 * t‖ := by simp only [n2, μC, μR, E2]
  have hn3 : n3 = ‖(m2 : ℂ) + ((m3 - (m1 + m2 + m3) : ℤ) : ℂ) * t‖ := by simp only [n3, μC, μR, E3]
  set L1 : ℝ := (D.l1 : ℝ) / 2 ^ 256 - |(m3 : ℝ)| * r
  set L2 : ℝ := (D.l2 : ℝ) / 2 ^ 256 - |(m3 : ℝ)| * r
  set U3 : ℝ := (D.u3 : ℝ) / 2 ^ 256 + |((m3 - (m1 + m2 + m3) : ℤ) : ℝ)| * r
  have b1 : L1 ≤ n1 := by rw [hn1]; exact lo1
  have b2 : L2 ≤ n2 := by rw [hn2]; exact lo2
  have b3 : n3 ≤ U3 := by rw [hn3]; exact up3
  have pos1 : 0 < n1 := lt_of_lt_of_le p1 b1
  have pos2 : 0 < n2 := lt_of_lt_of_le p2 b2
  have hl3 : 0 < n3 := by
    obtain ⟨p3, lo3, -⟩ := ellOK_sound e3 ht
    rw [hn3]; exact lt_of_lt_of_le p3 lo3
  refine ⟨?_, ?_⟩
  · have : n1 * n2 * n3 ≠ 0 := by positivity
    simpa [n1, n2, n3, norm_mul] using this
  -- the ratios
  set x1 : ℝ := (D.x1 : ℝ) / 2 ^ 256
  set x2 : ℝ := (D.x2 : ℝ) / 2 ^ 256
  have hx1' : (m1 : ℝ) * m1 * U3 ≤ x1 * x1 * ((m3 : ℝ) * m3) * L1 := by
    have : (((m1 : ℚ) * m1 * ((D.u3 : ℚ) / 2 ^ 256 + ((m3 - (m1 + m2 + m3)).natAbs : ℚ) * r) : ℚ) : ℝ) ≤
        ((((D.x1 : ℚ) / 2 ^ 256) * ((D.x1 : ℚ) / 2 ^ 256) * ((m3 : ℚ) * m3) *
          ((D.l1 : ℚ) / 2 ^ 256 - (m3.natAbs : ℚ) * r) : ℚ) : ℝ) := by exact_mod_cast hx1
    push_cast at this
    simpa only [Nat.cast_natAbs, Int.cast_abs, U3, L1, x1] using this
  have hx2' : (m2 : ℝ) * m2 * U3 ≤ x2 * x2 * ((m3 : ℝ) * m3) * L2 := by
    have : (((m2 : ℚ) * m2 * ((D.u3 : ℚ) / 2 ^ 256 + ((m3 - (m1 + m2 + m3)).natAbs : ℚ) * r) : ℚ) : ℝ) ≤
        ((((D.x2 : ℚ) / 2 ^ 256) * ((D.x2 : ℚ) / 2 ^ 256) * ((m3 : ℚ) * m3) *
          ((D.l2 : ℚ) / 2 ^ 256 - (m3.natAbs : ℚ) * r) : ℚ) : ℝ) := by exact_mod_cast hx2
    push_cast at this
    simpa only [Nat.cast_natAbs, Int.cast_abs, U3, L2, x2] using this
  have hθ' : (θ : ℝ) * (1 + x1 + x2) ≤ 1 := by
    have : ((θ * (1 + (D.x1 : ℚ) / 2 ^ 256 + (D.x2 : ℚ) / 2 ^ 256) : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by
      exact_mod_cast hθ
    push_cast at this
    simpa only [x1, x2] using this
  have hm1' : (0 : ℝ) < m1 := by exact_mod_cast hm1
  have hm2' : (0 : ℝ) < m2 := by exact_mod_cast hm2
  have hm3' : (0 : ℝ) < m3 := by exact_mod_cast hm3
  have hx1n : 0 ≤ x1 := by positivity
  have hx2n : 0 ≤ x2 := by positivity
  -- A_j in terms of the n_k
  have hA0 : AjG μR t 0 = m1 * Real.sqrt (n2 * n3) := by simp [AjG, μR, Lam, norm_mul, n2, n3, μC]
  have hA1 : AjG μR t 1 = m2 * Real.sqrt (n1 * n3) := by simp [AjG, μR, Lam, norm_mul, n1, n3, μC]
  have hA2 : AjG μR t 2 = m3 * Real.sqrt (n1 * n2) := by simp [AjG, μR, Lam, norm_mul, n1, n2, μC]
  have hA2p : 0 < AjG μR t 2 := by rw [hA2]; exact mul_pos hm3' (Real.sqrt_pos.mpr (mul_pos pos1 pos2))
  -- A₁ ≤ x₁ A₃ and A₂ ≤ x₂ A₃, through the squares
  have r1 : AjG μR t 0 ≤ x1 * AjG μR t 2 := by
    rw [hA0, hA2]
    have hk : (m1 : ℝ) * m1 * n3 ≤ x1 * x1 * (m3 * m3) * n1 := by
      have s1 := mul_le_mul_of_nonneg_left b3 (by positivity : (0 : ℝ) ≤ m1 * m1)
      have s2 := mul_le_mul_of_nonneg_left b1 (by positivity : (0 : ℝ) ≤ x1 * x1 * (m3 * m3))
      linarith
    have hsq : (m1 * Real.sqrt (n2 * n3)) ^ 2 ≤ (x1 * (m3 * Real.sqrt (n1 * n2))) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      have := mul_le_mul_of_nonneg_right hk pos2.le
      calc (m1 : ℝ) ^ 2 * (n2 * n3) = (m1 * m1 * n3) * n2 := by ring
        _ ≤ (x1 * x1 * (m3 * m3) * n1) * n2 := this
        _ = x1 ^ 2 * (m3 ^ 2 * (n1 * n2)) := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hsq
  have r2 : AjG μR t 1 ≤ x2 * AjG μR t 2 := by
    rw [hA1, hA2]
    have hk : (m2 : ℝ) * m2 * n3 ≤ x2 * x2 * (m3 * m3) * n2 := by
      have s1 := mul_le_mul_of_nonneg_left b3 (by positivity : (0 : ℝ) ≤ m2 * m2)
      have s2 := mul_le_mul_of_nonneg_left b2 (by positivity : (0 : ℝ) ≤ x2 * x2 * (m3 * m3))
      linarith
    have hsq : (m2 * Real.sqrt (n1 * n3)) ^ 2 ≤ (x2 * (m3 * Real.sqrt (n1 * n2))) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      have := mul_le_mul_of_nonneg_right hk pos1.le
      calc (m2 : ℝ) ^ 2 * (n1 * n3) = (m2 * m2 * n3) * n1 := by ring
        _ ≤ (x2 * x2 * (m3 * m3) * n2) * n1 := this
        _ = x2 ^ 2 * (m3 ^ 2 * (n1 * n2)) := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hsq
  have hA0n : 0 ≤ AjG μR t 0 := by rw [hA0]; positivity
  have hA1n : 0 ≤ AjG μR t 1 := by rw [hA1]; positivity
  rw [rhoG, le_div_iff₀ (by linarith)]
  nlinarith

/-- **The upper bound of `ρ` on a disk.** -/
theorem upperOK_sound {m1 m2 m3 : ℤ} (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) {θ θ' r : ℚ} {D : Disk}
    (hD : diskOK m1 m2 m3 θ r D = true) {Y1 Y2 : ℕ} (h : upperOK m1 m2 m3 θ' r D Y1 Y2 = true) {t : ℂ}
    (ht : ‖t - toC D.c‖ ≤ r) : rhoG ![(m1 : ℝ), m2, m3] t ≤ θ' := by
  simp only [diskOK, KS, Bool.and_eq_true] at hD
  obtain ⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, -⟩, -⟩, -⟩ := hD
  simp only [upperOK, KS, Bool.and_eq_true] at h
  obtain ⟨⟨hy1, hy2⟩, hθ⟩ := h
  replace hy1 := of_decide_eq_true hy1
  replace hy2 := of_decide_eq_true hy2
  replace hθ := of_decide_eq_true hθ
  obtain ⟨E1, E2, E3⟩ := ell_eqs m1 m2 m3 t
  obtain ⟨p1, lo1, up1⟩ := ellOK_sound e1 ht
  obtain ⟨p2, lo2, up2⟩ := ellOK_sound e2 ht
  obtain ⟨p3, lo3, -⟩ := ellOK_sound e3 ht
  set μR : Fin 3 → ℝ := ![(m1 : ℝ), m2, m3]
  set μC : Fin 3 → ℂ := fun i => ((μR i : ℝ) : ℂ)
  set n1 := ‖ell1 μC t‖
  set n2 := ‖ell2 μC t‖
  set n3 := ‖ell3 μC t‖
  have hn1 : n1 = ‖(m2 : ℂ) + m3 * t‖ := by simp only [n1, μC, μR, E1]
  have hn2 : n2 = ‖((m2 - (m1 + m2 + m3) : ℤ) : ℂ) + m3 * t‖ := by simp only [n2, μC, μR, E2]
  have hn3 : n3 = ‖(m2 : ℂ) + ((m3 - (m1 + m2 + m3) : ℤ) : ℂ) * t‖ := by simp only [n3, μC, μR, E3]
  set U1 : ℝ := (D.u1 : ℝ) / 2 ^ 256 + |(m3 : ℝ)| * r
  set U2 : ℝ := (D.u2 : ℝ) / 2 ^ 256 + |(m3 : ℝ)| * r
  set L3 : ℝ := (D.l3 : ℝ) / 2 ^ 256 - |((m3 - (m1 + m2 + m3) : ℤ) : ℝ)| * r
  have c1 : n1 ≤ U1 := by rw [hn1]; exact up1
  have c2 : n2 ≤ U2 := by rw [hn2]; exact up2
  have c3 : L3 ≤ n3 := by rw [hn3]; exact lo3
  have pos1 : 0 < n1 := by rw [hn1]; exact lt_of_lt_of_le p1 lo1
  have pos2 : 0 < n2 := by rw [hn2]; exact lt_of_lt_of_le p2 lo2
  set y1 : ℝ := (Y1 : ℝ) / 2 ^ 256
  set y2 : ℝ := (Y2 : ℝ) / 2 ^ 256
  have hy1' : y1 * y1 * ((m3 : ℝ) * m3) * U1 ≤ (m1 : ℝ) * m1 * L3 := by
    have : ((((Y1 : ℚ) / 2 ^ 256) * ((Y1 : ℚ) / 2 ^ 256) * ((m3 : ℚ) * m3) *
        ((D.u1 : ℚ) / 2 ^ 256 + (m3.natAbs : ℚ) * r) : ℚ) : ℝ) ≤
        (((m1 : ℚ) * m1 * ((D.l3 : ℚ) / 2 ^ 256 - ((m3 - (m1 + m2 + m3)).natAbs : ℚ) * r) : ℚ) : ℝ) := by
      exact_mod_cast hy1
    push_cast at this
    simpa only [Nat.cast_natAbs, Int.cast_abs, U1, L3, y1] using this
  have hy2' : y2 * y2 * ((m3 : ℝ) * m3) * U2 ≤ (m2 : ℝ) * m2 * L3 := by
    have : ((((Y2 : ℚ) / 2 ^ 256) * ((Y2 : ℚ) / 2 ^ 256) * ((m3 : ℚ) * m3) *
        ((D.u2 : ℚ) / 2 ^ 256 + (m3.natAbs : ℚ) * r) : ℚ) : ℝ) ≤
        (((m2 : ℚ) * m2 * ((D.l3 : ℚ) / 2 ^ 256 - ((m3 - (m1 + m2 + m3)).natAbs : ℚ) * r) : ℚ) : ℝ) := by
      exact_mod_cast hy2
    push_cast at this
    simpa only [Nat.cast_natAbs, Int.cast_abs, U2, L3, y2] using this
  have hθ' : (1 : ℝ) ≤ θ' * (1 + y1 + y2) := by
    have : ((1 : ℚ) : ℝ) ≤ ((θ' * (1 + (Y1 : ℚ) / 2 ^ 256 + (Y2 : ℚ) / 2 ^ 256) : ℚ) : ℝ) := by exact_mod_cast hθ
    push_cast at this
    simpa only [y1, y2] using this
  have hm1' : (0 : ℝ) < m1 := by exact_mod_cast hm1
  have hm2' : (0 : ℝ) < m2 := by exact_mod_cast hm2
  have hm3' : (0 : ℝ) < m3 := by exact_mod_cast hm3
  have hA0 : AjG μR t 0 = m1 * Real.sqrt (n2 * n3) := by simp [AjG, μR, Lam, norm_mul, n2, n3, μC]
  have hA1 : AjG μR t 1 = m2 * Real.sqrt (n1 * n3) := by simp [AjG, μR, Lam, norm_mul, n1, n3, μC]
  have hA2 : AjG μR t 2 = m3 * Real.sqrt (n1 * n2) := by simp [AjG, μR, Lam, norm_mul, n1, n2, μC]
  have hA2p : 0 < AjG μR t 2 := by rw [hA2]; exact mul_pos hm3' (Real.sqrt_pos.mpr (mul_pos pos1 pos2))
  have hn3 : 0 ≤ n3 := norm_nonneg _
  -- A₁ ≥ y₁ A₃, A₂ ≥ y₂ A₃
  have r1 : y1 * AjG μR t 2 ≤ AjG μR t 0 := by
    rw [hA0, hA2]
    have hk : y1 * y1 * (m3 * m3) * n1 ≤ (m1 : ℝ) * m1 * n3 := by
      have s1 := mul_le_mul_of_nonneg_left c1 (by positivity : (0 : ℝ) ≤ y1 * y1 * (m3 * m3))
      have s2 := mul_le_mul_of_nonneg_left c3 (by positivity : (0 : ℝ) ≤ m1 * m1)
      linarith
    have hsq : (y1 * (m3 * Real.sqrt (n1 * n2))) ^ 2 ≤ (m1 * Real.sqrt (n2 * n3)) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      have := mul_le_mul_of_nonneg_right hk pos2.le
      calc y1 ^ 2 * (m3 ^ 2 * (n1 * n2)) = (y1 * y1 * (m3 * m3) * n1) * n2 := by ring
        _ ≤ (m1 * m1 * n3) * n2 := this
        _ = (m1 : ℝ) ^ 2 * (n2 * n3) := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hsq
  have r2 : y2 * AjG μR t 2 ≤ AjG μR t 1 := by
    rw [hA1, hA2]
    have hk : y2 * y2 * (m3 * m3) * n2 ≤ (m2 : ℝ) * m2 * n3 := by
      have s1 := mul_le_mul_of_nonneg_left c2 (by positivity : (0 : ℝ) ≤ y2 * y2 * (m3 * m3))
      have s2 := mul_le_mul_of_nonneg_left c3 (by positivity : (0 : ℝ) ≤ m2 * m2)
      linarith
    have hsq : (y2 * (m3 * Real.sqrt (n1 * n2))) ^ 2 ≤ (m2 * Real.sqrt (n1 * n3)) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      have := mul_le_mul_of_nonneg_right hk pos1.le
      calc y2 ^ 2 * (m3 ^ 2 * (n1 * n2)) = (y2 * y2 * (m3 * m3) * n2) * n1 := by ring
        _ ≤ (m2 * m2 * n3) * n1 := this
        _ = (m2 : ℝ) ^ 2 * (n1 * n3) := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hsq
  have hy1n : 0 ≤ y1 := by positivity
  have hy2n : 0 ≤ y2 := by positivity
  have hA0n : 0 ≤ AjG μR t 0 := by rw [hA0]; positivity
  have hA1n : 0 ≤ AjG μR t 1 := by rw [hA1]; positivity
  have hθp : 0 < (θ' : ℝ) := by
    by_contra hneg
    push Not at hneg
    have : (θ' : ℝ) * (1 + y1 + y2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg (by positivity)
    linarith
  rw [rhoG, div_le_iff₀ (by linarith)]
  have hs := mul_le_mul_of_nonneg_left (add_le_add (add_le_add r1 r2) (le_refl (AjG μR t 2))) hθp.le
  calc AjG μR t 2 = 1 * AjG μR t 2 := (one_mul _).symm
    _ ≤ (θ' * (1 + y1 + y2)) * AjG μR t 2 := mul_le_mul_of_nonneg_right hθ' hA2p.le
    _ = θ' * (y1 * AjG μR t 2 + y2 * AjG μR t 2 + AjG μR t 2) := by ring
    _ ≤ θ' * (AjG μR t 0 + AjG μR t 1 + AjG μR t 2) := hs

/-- `p` holds for all pairs of a list. -/
theorem pairwiseB_sound {α : Type} {p : α → α → Bool} : ∀ {l : List α}, pairwiseB p l = true →
    l.Pairwise (fun a b => p a b = true)
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    simp only [pairwiseB, Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons h.1 (pairwiseB_sound h.2)

/-- **What `facOK` means**: every complex root of the factor `f` lies in one of its disks, on which `diskOK`
holds; and every disk contains a root of `f`. -/
theorem facOK_sound {m1 m2 m3 : ℤ} {θ : ℚ} {f : UP} {F : FacDisks} (h : facOK m1 m2 m3 θ f F = true) :
    (∀ t : ℂ, ((toPoly f).map (Int.castRingHom ℂ)).eval t = 0 →
      ∃ D ∈ F.disks, ‖t - toC D.c‖ ≤ (((1 : ℚ) / 2 ^ F.m : ℚ) : ℝ) ∧ diskOK m1 m2 m3 θ (1 / 2 ^ F.m) D = true) ∧
    (∀ D ∈ F.disks, (∃ t : ℂ, ((toPoly f).map (Int.castRingHom ℂ)).eval t = 0 ∧
      ‖t - toC D.c‖ ≤ (((1 : ℚ) / 2 ^ F.m : ℚ) : ℝ)) ∧ diskOK m1 m2 m3 θ (1 / 2 ^ F.m) D = true) := by
  simp only [facOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hlc, hd⟩, hlen⟩, hsmall⟩, hpw⟩, hdisk⟩ := h
  replace hlc := of_decide_eq_true hlc
  replace hd := of_decide_eq_true hd
  set d := f.length - 1
  set lc := f.getLast?.getD 0
  set r : ℚ := 1 / 2 ^ F.m
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by simp only [r]; positivity
  -- degree and leading coefficient of the factor
  have hlast : f.getLast? = some lc := by
    cases hf : f.getLast? with
    | none => simp [lc, hf] at hlc
    | some x => simp [lc, hf]
  have hdl : UP.degLead f d lc = true := by
    simp only [UP.degLead, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, hlast]
    refine ⟨⟨by omega, trivial⟩, hlc⟩
  obtain ⟨hnd, hlcd⟩ := degLead_sound hdl
  set g := (toPoly f).map (Int.castRingHom ℂ)
  have hinj : Function.Injective (Int.castRingHom ℂ) := (Int.castRingHom ℂ).injective_int
  have hgd : g.natDegree = d := by rw [natDegree_map_eq_of_injective hinj, hnd]
  have hgl : g.leadingCoeff = (lc : ℂ) := by rw [leadingCoeff_map_of_injective hinj, hlcd]; simp
  have hg0 : g ≠ 0 := by
    intro h0; rw [h0, natDegree_zero] at hgd; omega
  -- the values at the centres
  have hval : ∀ D ∈ F.disks, ‖g.eval (toC D.c)‖ < ‖g.leadingCoeff‖ * (r : ℝ) ^ d := by
    intro D hD
    have h1 := of_decide_eq_true (hsmall D hD)
    rw [← hornerQ_sound, hgl]
    have h2 : ‖toC (hornerQ f D.c)‖ ^ 2 < (‖(lc : ℂ)‖ * (r : ℝ) ^ d) ^ 2 := by
      rw [norm_sq_toC, mul_pow, Complex.norm_intCast, sq_abs, ← pow_mul]
      have : ((gnorm2 (hornerQ f D.c) : ℚ) : ℝ) < (((lc : ℚ) * lc * r ^ (2 * d) : ℚ) : ℝ) := by exact_mod_cast h1
      push_cast at this
      calc ((gnorm2 (hornerQ f D.c) : ℚ) : ℝ) < (lc : ℝ) * lc * (r : ℝ) ^ (2 * d) := this
        _ = (lc : ℝ) ^ 2 * (r : ℝ) ^ (d * 2) := by rw [mul_comm d 2]; ring
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp h2
  refine ⟨fun t ht => ?_, fun D hD => ⟨?_, hdisk D hD⟩⟩
  · -- every root lies in a disk
    have hroot : t ∈ g.roots := (mem_roots hg0).mpr ht
    have hlen' : F.disks.length = d := hlen
    set c : Fin d → ℂ := fun i => toC (F.disks.get ⟨i, by omega⟩).c
    have h1 : ∀ i, ‖g.eval (c i)‖ < ‖g.leadingCoeff‖ * (r : ℝ) ^ d := fun i => hval _ (List.get_mem _ _)
    have hpw' := pairwiseB_sound hpw
    have h2 : ∀ i j, i ≠ j → 2 * (r : ℝ) < ‖c i - c j‖ := by
      intro i j hij
      have key : ∀ a b : Fin d, a.1 < b.1 → 2 * (r : ℝ) < ‖c a - c b‖ := by
        intro a b hab
        have := List.pairwise_iff_getElem.mp hpw' a.1 b.1 (by omega) (by omega) hab
        have h4 := of_decide_eq_true this
        have h5 : (2 * (r : ℝ)) ^ 2 < ‖c a - c b‖ ^ 2 := by
          have e : c a - c b = toC (((F.disks.get ⟨a, by omega⟩).c.1 - (F.disks.get ⟨b, by omega⟩).c.1),
              ((F.disks.get ⟨a, by omega⟩).c.2 - (F.disks.get ⟨b, by omega⟩).c.2)) := by
            simp only [c, toC]; push_cast; ring
          rw [e, norm_sq_toC]
          have : (((4 * r * r : ℚ)) : ℝ) < ((gnorm2 ((F.disks.get ⟨a, by omega⟩).c.1 -
              (F.disks.get ⟨b, by omega⟩).c.1, (F.disks.get ⟨a, by omega⟩).c.2 -
              (F.disks.get ⟨b, by omega⟩).c.2) : ℚ) : ℝ) := by exact_mod_cast h4
          push_cast at this
          linarith
        exact (pow_lt_pow_iff_left₀ (by positivity) (norm_nonneg _) (by norm_num)).mp h5
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
      · exact key i j hlt
      · rw [norm_sub_rev]; exact key j i hlt
    obtain ⟨i, hi⟩ := roots_in_disks g hgd c hr0 h1 h2 t hroot
    exact ⟨_, List.get_mem _ _, hi, hdisk _ (List.get_mem _ _)⟩
  · -- every disk contains a root
    obtain ⟨α, hα, hαr⟩ := exists_root_near g (toC D.c) hr0 (by rw [hgd]; exact hval D hD)
    refine ⟨α, (mem_roots hg0).mp hα, ?_⟩
    rw [norm_sub_rev]; exact hαr

end Lean6.Special.D98
