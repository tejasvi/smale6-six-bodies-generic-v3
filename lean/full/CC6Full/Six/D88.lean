import CC6Full.Six.D88Sys
import CC6Full.Six.D88Lead

/-!
# Diagram 88: the polynomial of Theorem 6.20 (`thm:d88`, the half about `P₈₈`)

§6.7 of the paper (`ss:d88`). At a singular place with diagram `88` the leading data of Lemma 6.16 (a)
(`d88_lead`) solve `N₄(m_K)` together with the cross relations `p̂_jl² ẑ_j X_l = −1` and the torque relation
(eq:t88) `Σ_{j∈{5,6}, l∈K} m_j m_l p̂_jl = 0`. Theorem 6.20 gives a nonzero `P₈₈ ∈ ℤ[m₁, …, m₆]` vanishing at the
masses of every such place. The paper proves it from Lemma 6.18 (`lem:goodred`), the computations of Lemma 6.19
(`lem:d88comp`) at `μ₀ = (1, 2, 3, 30)` and `p = 65521`, the implicit function theorem and constructible sets. Here the
last two are replaced by the integral elimination lemma at one point (`elim_gInt`, from `CC6Full.elim_integral_int`).

## The computations as hypotheses

* `D88Int`: `O[v]/(S12)` is integral over `O = Opt p μ₀ = ℤ[μ]_𝔪`, `𝔪 = (p, μ − μ₀)` (Lemma 6.18 with Lemma 6.19 (a);
  it is the conclusion of `CC6Full.goodred`).
* `D88Dim`: `dim_{𝔽_p} 𝔽_p[v]/⟨S12(μ₀) mod p⟩ ≤ 20316` (Lemma 6.19 (b)).
* `D88Box`: a set `Z` of `20316` complex zeros of `S11(μ₀)` with `X₃ − X₄ ≠ 0`, all `X_l ≠ 0`, at which the `T`-test of
  Lemma 6.17 (a) holds strictly for some `k` (Lemma 6.19 (c)). The condition `X_l ≠ 0` is part of the `T`-test of the
  paper, which uses `|X_l|^{−1/2}`; in Lean `‖0‖ ^ (−1/2) = 0`, so it is stated separately.

## The proof

* `d88_encard_le`, `d88_zeros_mem`, `d88_Ttest_zeros` (the count of §6.7 and the proof of Theorem 6.20): `S12(μ₀)`
  has at most `20316` complex zeros (`encard_zeros_le_of_isIntegral`, "by Nakayama's lemma"); the points of `Z` are
  zeros of `S12(μ₀)` by the torque identity (`D88.S12_of_S11`); so every complex zero of `S12(μ₀)` lies in `Z`, and the
  `T`-test holds at every zero.
* The elimination. The parameters are the six masses `m` (`μ = m ∘ quad` for `K`, `(m₅, m₆) = m ∘ bin`), the unknowns
  are `v ∈ ℂ¹¹` and `q_jl` (`K88`). The system `S88` consists of `S12` (with the denominators cleared, `D88.rows12`),
  the cross relations `binEq` and the torque relation `torqEq`: with the scale `c` of the binary normalized to `1`
  (`ẑ₅ = m₆`, `ẑ₆ = −m₅`) and `q_jl = p̂_jl X_l`, they read `q_5l² m₆ + X_l = 0`, `−q_6l² m₅ + X_l = 0` and
  `Σ_l m_l (m₅ q_5l + m₆ q_6l) Π_{l'≠l} X_l' = 0`, multiplied by powers of `μ₄`.
  - `sol88`: the leading data give a solution at the masses of the place, after the rotation that makes
    `X₁ − X₂ = 1` (`D88.slice`) and the normalization of `c` (a square root of `c (X₁ − X₂)` rescales the `p̂_jl`).
  - `exists_g88`: every unknown is integral over `ℚ[m][1/g]` modulo `S88`, for some `g` with `g(μ₀, 1, 1) ≠ 0`: the
    `v_i` by `D88Int`, after clearing the denominators of the monic relations over `O`, which do not vanish at `μ₀`
    (`exists_rel_of_isIntegral_Opt`); the `q_jl` as square roots of `−X_l/m₆` and `X_l/m₅`.
  - `hnone88`: no complex solution at `(μ₀, 1, 1)`: a solution has `v` a zero of `S12(μ₀)`, so the `T`-test holds at
    `v` and `Ttest_a` contradicts the torque relation.
* `d88_poly`: **Theorem 6.20** for diagram `88`, from `elim_gInt`.
-/

namespace CC6Full.Six

open MvPolynomial Finset

noncomputable section

/-! ## The computations of Lemma 6.19 as hypotheses -/

/-- **Lemma 6.18 with Lemma 6.19 (a)** for `S12`: with `O = Opt p μ₀ = ℤ[μ]_𝔪`, `𝔪 = (p, μ − μ₀)`, `p = 65521`,
`μ₀ = (1, 2, 3, 30)`, the quotient of `O[v]` by the ideal of `S12` (`D88.S12P`, the denominators `μ₄` cleared) is
integral over `O`. This is the conclusion of `CC6Full.goodred` for the certificates of Lemma 6.19 (a). -/
def D88Int : Prop :=
  Algebra.IsIntegral (Opt 65521 μ0Z) (MvPolynomial (Fin 11) (Opt 65521 μ0Z) ⧸
    Ideal.span (Set.range fun i =>
      MvPolynomial.map (algebraMap (MvPolynomial (Fin 4) ℤ) (Opt 65521 μ0Z)) (D88.S12P i)))

/-- **Lemma 6.19 (b)** for `S12`: `dim_{𝔽_p} 𝔽_p[v]/⟨S12(μ₀)⟩ ≤ 20316`, where `S12(μ₀)` is `D88.S12P` with its
coefficients evaluated at `μ₀ = (1, 2, 3, 30)` and reduced modulo `p = 65521` (`redPt`). -/
def D88Dim : Prop :=
  Module.finrank (ZMod 65521) (MvPolynomial (Fin 11) (ZMod 65521) ⧸
    Ideal.span (Set.range fun i => MvPolynomial.map (redPt 65521 μ0Z) (D88.S12P i))) ≤ 20316

/-- **Lemma 6.19 (c)**: there is a set `Z` of `20316` points of `ℂ¹¹`, each a zero of `S11(μ₀)` with `X₃ − X₄ ≠ 0`
and all `X_l ≠ 0`, at which the `T`-test of Lemma 6.17 (a) holds strictly for some `k`, with the masses `μ₀`:
`m_k |X_k|^{−1/2} > Σ_{l≠k} m_l |X_l|^{−1/2}`. -/
def D88Box : Prop :=
  ∃ Z : Finset (Fin 11 → ℂ), Z.card = 20316 ∧ ∀ v ∈ Z, D88.S11 D88.μ0 v = 0 ∧
    D88.X D88.μ0 v 2 - D88.X D88.μ0 v 3 ≠ 0 ∧ (∀ l, D88.X D88.μ0 v l ≠ 0) ∧
    ∃ k : Fin 4, D88.μ0R k * ‖D88.X D88.μ0 v k‖ ^ (-(1 / 2 : ℝ)) >
      ∑ l ∈ univ.erase k, D88.μ0R l * ‖D88.X D88.μ0 v l‖ ^ (-(1 / 2 : ℝ))

/-! ## The zeros of `S12(μ₀)` -/

/-- **The count** of §6.7: by Lemma 6.18 and Lemma 6.19 (a), (b), `S12(μ₀)` has at most `20316` complex zeros
(`encard_zeros_le_of_isIntegral`). -/
theorem d88_encard_le (h1 : D88Int) (h2 : D88Dim) :
    {v : Fin 11 → ℂ | D88.S12 D88.μ0 v = 0}.encard ≤ 20316 := by
  have h := encard_zeros_le_of_isIntegral 65521 μ0Z D88.S12P h1 h2
  have hset : {v : Fin 11 → ℂ | D88.S12 D88.μ0 v = 0} =
      {z : Fin 11 → ℂ | ∀ i, eval z (MvPolynomial.map ((Int.castRingHom ℂ).comp (eval μ0Z)) (D88.S12P i)) = 0} := by
    ext v
    simp only [Set.mem_ofPred_eq, D88.eval_S12P_μ0]
    rw [← D88.rows12_eq_zero_iff D88.μ0_three_ne, funext_iff]
    rfl
  rw [hset]
  exact_mod_cast h

/-- **Every complex zero of `S12(μ₀)` lies in a set of `20316` zeros**: the count `d88_encard_le`. -/
theorem d88_zeros_mem (h1 : D88Int) (h2 : D88Dim) {Z : Finset (Fin 11 → ℂ)} (hZ : Z.card = 20316)
    (hsub : ∀ v ∈ Z, D88.S12 D88.μ0 v = 0) {v : Fin 11 → ℂ} (hv : D88.S12 D88.μ0 v = 0) : v ∈ Z := by
  have heq : (Z : Set (Fin 11 → ℂ)) = {v | D88.S12 D88.μ0 v = 0} := by
    refine Set.Finite.eq_of_subset_of_encard_le Z.finite_toSet (fun v hv => hsub v hv) ?_
    rw [Set.encard_coe_eq_coe_finsetCard, hZ]
    exact_mod_cast d88_encard_le h1 h2
  have hv' : v ∈ ({v | D88.S12 D88.μ0 v = 0} : Set (Fin 11 → ℂ)) := hv
  rw [← heq] at hv'
  exact hv'

/-- **The `T`-test at every zero** (the proof of Theorem 6.20): every complex zero of `S12(μ₀)` lies in the set `Z`
of Lemma 6.19 (c), since the points of `Z` are zeros of `S12(μ₀)` by the torque identity (`D88.S12_of_S11`) and
there are at most `20316` zeros; so all `X_l ≠ 0` and the `T`-test of Lemma 6.17 (a) holds for some `k`. -/
theorem d88_Ttest_zeros (h1 : D88Int) (h2 : D88Dim) (h3 : D88Box) {v : Fin 11 → ℂ}
    (hv : D88.S12 D88.μ0 v = 0) :
    (∀ l, D88.X D88.μ0 v l ≠ 0) ∧ ∃ k : Fin 4, D88.μ0R k * ‖D88.X D88.μ0 v k‖ ^ (-(1 / 2 : ℝ)) >
      ∑ l ∈ univ.erase k, D88.μ0R l * ‖D88.X D88.μ0 v l‖ ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨Z, hcard, hZ⟩ := h3
  have hvZ := d88_zeros_mem h1 h2 hcard
    (fun w hw => D88.S12_of_S11 D88.μ0_two_ne D88.μ0_three_ne (hZ w hw).1 (hZ w hw).2.1) hv
  exact (hZ v hvZ).2.2

/-- **Every complex zero of `S12(μ₀)` lies in the set `Z` of Lemma 6.19 (c)** (`D88Box`): the points of `Z` are
zeros of `S12(μ₀)` (`D88.S12_of_S11`), and there are at most `20316` zeros (`d88_encard_le`). -/
theorem d88_zeros_in_box (h1 : D88Int) (h2 : D88Dim) (h3 : D88Box) :
    ∃ Z : Finset (Fin 11 → ℂ), Z.card = 20316 ∧ (∀ v ∈ Z, D88.S11 D88.μ0 v = 0 ∧
      D88.X D88.μ0 v 2 - D88.X D88.μ0 v 3 ≠ 0 ∧ (∀ l, D88.X D88.μ0 v l ≠ 0) ∧
      ∃ k : Fin 4, D88.μ0R k * ‖D88.X D88.μ0 v k‖ ^ (-(1 / 2 : ℝ)) >
        ∑ l ∈ univ.erase k, D88.μ0R l * ‖D88.X D88.μ0 v l‖ ^ (-(1 / 2 : ℝ))) ∧
      ∀ v, D88.S12 D88.μ0 v = 0 → v ∈ Z := by
  obtain ⟨Z, hcard, hZ⟩ := h3
  have hsub : ∀ v ∈ Z, D88.S12 D88.μ0 v = 0 := fun w hw =>
    D88.S12_of_S11 D88.μ0_two_ne D88.μ0_three_ne (hZ w hw).1 (hZ w hw).2.1
  exact ⟨Z, hcard, hZ, fun v hv => d88_zeros_mem h1 h2 hcard hsub hv⟩

/-! ## The system of the elimination -/

/-- The unknowns of the elimination: `v ∈ ℂ¹¹` (`Sum.inl`) and the `q_jl = p̂_jl X_l`, `j ∈ {5, 6}` (`Fin 2`),
`l ∈ K` (`Fin 4`) (`Sum.inr`). -/
abbrev K88 := Fin 11 ⊕ (Fin 2 × Fin 4)

/-- The polynomial ring `ℚ[m, v, q]`; the parameters `m_k = X (Sum.inl k)`, `k : Fin 6`, are the masses of the
six bodies (`K = {1, 2, 3, 4}` renumbered by `quad`, the binary `{5, 6}` by `bin`). -/
abbrev R88 := MvPolynomial (Fin 6 ⊕ K88) ℚ

/-- The masses `μ_k = m_{quad k}` of `K`. -/
def μ88 (k : Fin 4) : R88 := X (Sum.inl (quad k))

/-- The masses `m_{bin j}` of the binary. -/
def mb88 (j : Fin 2) : R88 := X (Sum.inl (bin j))

/-- The unknowns `v_i`. -/
def v88 (i : Fin 11) : R88 := X (Sum.inr (Sum.inl i))

/-- The unknowns `q_jl`. -/
def q88 (j : Fin 2) (l : Fin 4) : R88 := X (Sum.inr (Sum.inr (j, l)))

/-- **The system of the elimination**: `S12` (`D88.rows12`), the cross relations `binEq` and the torque relation
`torqEq` (with the scale of the binary normalized to `1` and `q_jl = p̂_jl X_l`), the positions with the denominator
`μ₄` cleared (`D88.Xh`). -/
def S88 : Set R88 :=
  Set.range (D88.rows12 μ88 v88) ∪
    Set.range (fun jl : Fin 2 × Fin 4 => binEq (μ88 3) mb88 q88 (D88.Xh μ88 v88) jl.1 jl.2) ∪
    {torqEq μ88 mb88 q88 (D88.Xh μ88 v88)}

theorem row88_mem (i : Fin 12) : D88.rows12 μ88 v88 i ∈ S88 := Or.inl (Or.inl ⟨i, rfl⟩)

theorem bin88_mem (j : Fin 2) (l : Fin 4) : binEq (μ88 3) mb88 q88 (D88.Xh μ88 v88) j l ∈ S88 :=
  Or.inl (Or.inr ⟨(j, l), rfl⟩)

theorem torq88_mem : torqEq μ88 mb88 q88 (D88.Xh μ88 v88) ∈ S88 := Or.inr rfl

/-- The parameter point `(μ₀, m₅, m₆) = (1, 2, 3, 30, 1, 1)`. -/
def μ₀88 : Fin 6 → ℚ := ![1, 2, 3, 30, 1, 1]

section Eval

variable (θ : Fin 6 → ℂ) (x : K88 → ℂ)

@[simp] theorem aeval_μ88 (k : Fin 4) : aeval (Sum.elim θ x) (μ88 k) = θ (quad k) := by simp [μ88]

@[simp] theorem aeval_mb88 (j : Fin 2) : aeval (Sum.elim θ x) (mb88 j) = θ (bin j) := by simp [mb88]

@[simp] theorem aeval_v88 (i : Fin 11) : aeval (Sum.elim θ x) (v88 i) = x (Sum.inl i) := by simp [v88]

@[simp] theorem aeval_q88 (j : Fin 2) (l : Fin 4) : aeval (Sum.elim θ x) (q88 j l) = x (Sum.inr (j, l)) := by
  simp [q88]

theorem aeval_row88 (i : Fin 12) : aeval (Sum.elim θ x) (D88.rows12 μ88 v88 i) =
    D88.rows12 (fun k => θ (quad k)) (fun i => x (Sum.inl i)) i := by
  rw [D88.map_rows12]
  simp

theorem aeval_Xh88 (l : Fin 4) : aeval (Sum.elim θ x) (D88.Xh μ88 v88 l) =
    D88.Xh (fun k => θ (quad k)) (fun i => x (Sum.inl i)) l := by
  rw [D88.map_Xh]
  simp

theorem aeval_bin88 (j : Fin 2) (l : Fin 4) : aeval (Sum.elim θ x) (binEq (μ88 3) mb88 q88 (D88.Xh μ88 v88) j l) =
    binEq (θ (quad 3)) (fun j => θ (bin j)) (fun j l => x (Sum.inr (j, l)))
      (D88.Xh (fun k => θ (quad k)) (fun i => x (Sum.inl i))) j l := by
  rw [map_binEq]
  simp [aeval_Xh88]

theorem aeval_torq88 : aeval (Sum.elim θ x) (torqEq μ88 mb88 q88 (D88.Xh μ88 v88)) =
    torqEq (fun k => θ (quad k)) (fun j => θ (bin j)) (fun j l => x (Sum.inr (j, l)))
      (D88.Xh (fun k => θ (quad k)) (fun i => x (Sum.inl i))) := by
  rw [map_torqEq]
  simp [aeval_Xh88]

end Eval

/-! ## The leading data give a solution -/

/-- The algebra of `sol88`, for masses `θ` and data `(X, Y, P)` solving `N₄(θ_K)`, cross coefficients `p̂_jl` with
`p̂_jl² ẑ_j X_l = −1`, `ẑ_j = c ẑ'_j` for the normalized `ẑ' = zb θ_bin`, and the torque relation
`Σ_{j,l} m_j m_l p̂_jl = 0`. With `v = D88.slice X Y P` (the rotation that makes `X₁ − X₂ = 1`) and
`q_jl = r p̂_jl X_l/(X₁ − X₂)`, `r² = c (X₁ − X₂)`, the point `(v, q)` solves `S88` at `θ`. -/
theorem sol88_alg {θ : Fin 6 → ℂ} (hμ3 : θ (quad 3) ≠ 0) {Xo Yo : Fin 4 → ℂ} {P : Fin 4 → Fin 4 → ℂ}
    (hN : IsNSys (fun l => θ (quad l)) Xo Yo P) {zh : Fin 2 → ℂ} {ph : Fin 2 → Fin 4 → ℂ} {c : ℂ}
    (hzc : ∀ j, zh j = c * zb (fun j => θ (bin j)) j) (hcross : ∀ j l, ph j l ^ 2 * zh j * Xo l = -1)
    (hsum : ∑ j, ∑ l, θ (bin j) * θ (quad l) * ph j l = 0) :
    ∃ x : K88 → ℂ, ∀ f ∈ S88, aeval (Sum.elim θ x) f = 0 := by
  have h01 : Xo 0 - Xo 1 ≠ 0 := (distEqs_ne hN.2.2.2 (by decide : (0 : Fin 4) ≠ 1)).2.1
  have ha : (Xo 0 - Xo 1)⁻¹ * (Xo 0 - Xo 1) = 1 := inv_mul_cancel₀ h01
  have hcom := (isNSys_com hN).1
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (c * (Xo 0 - Xo 1)) two_pos
  have hXh : ∀ l, D88.Xh (fun k => θ (quad k)) (D88.slice Xo Yo P) l =
      θ (quad 3) * (Xo 0 - Xo 1)⁻¹ * Xo l := fun l => by
    rw [D88.Xh_eq (μ := fun k => θ (quad k)) hμ3, D88.X_slice (μ := fun k => θ (quad k)) (Yo := Yo) (P := P) hμ3 h01
      hcom]
    ring
  refine ⟨Sum.elim (D88.slice Xo Yo P) fun jl => r * ph jl.1 jl.2 * ((Xo 0 - Xo 1)⁻¹ * Xo jl.2), ?_⟩
  rintro f ((⟨i, rfl⟩ | ⟨⟨j, l⟩, rfl⟩) | rfl)
  · -- the equations of `S12`
    rw [aeval_row88]
    exact congrFun ((D88.rows12_eq_zero_iff (μ := fun k => θ (quad k)) hμ3 (D88.slice Xo Yo P)).mpr
      (D88.S12_slice (μ := fun k => θ (quad k)) hμ3 hN)) i
  · -- the cross relations
    show aeval (Sum.elim θ _) (binEq (μ88 3) mb88 q88 (D88.Xh μ88 v88) j l) = 0
    rw [aeval_bin88]
    show θ (quad 3) * zb (fun j => θ (bin j)) j * (r * ph j l * ((Xo 0 - Xo 1)⁻¹ * Xo l)) ^ 2 +
      D88.Xh (fun k => θ (quad k)) (D88.slice Xo Yo P) l = 0
    rw [hXh l]
    linear_combination θ (quad 3) * zb (fun j => θ (bin j)) j * ph j l ^ 2 * (Xo 0 - Xo 1)⁻¹ ^ 2 * Xo l ^ 2 * hr +
      θ (quad 3) * zb (fun j => θ (bin j)) j * c * ph j l ^ 2 * (Xo 0 - Xo 1)⁻¹ * Xo l ^ 2 * ha -
      θ (quad 3) * (Xo 0 - Xo 1)⁻¹ * Xo l ^ 2 * ph j l ^ 2 * hzc j +
      θ (quad 3) * (Xo 0 - Xo 1)⁻¹ * Xo l * hcross j l
  · -- the torque relation
    rw [aeval_torq88]
    show torqEq (fun k => θ (quad k)) (fun j => θ (bin j))
      (fun j l => r * ph j l * ((Xo 0 - Xo 1)⁻¹ * Xo l)) (D88.Xh (fun k => θ (quad k)) (D88.slice Xo Yo P)) = 0
    rw [torqEq_eq (fun k => θ (quad k)) (fun j => θ (bin j))
      (q := fun j l => r * ph j l * ((Xo 0 - Xo 1)⁻¹ * Xo l)) (X := Xo) (P := ph)
      (a := θ (quad 3) * (Xo 0 - Xo 1)⁻¹) (b := r * (Xo 0 - Xo 1)⁻¹) hXh (fun j l => by ring)]
    simp only [hsum, mul_zero]

/-- **The leading data of Lemma 6.16 (a) give a solution of `S88`** at the masses of the place (`d88_lead`,
`sol88_alg`): `ẑ₅ = c m₆`, `ẑ₆ = −c m₅` with `c = ẑ₅/m₆` (`bin_c`). -/
theorem sol88 {m : Fin 6 → ℝ} (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d88) :
    ∃ x : K88 → ℂ, ∀ f ∈ S88, aeval (Sum.elim (fun k => (m k : ℂ)) x) f = 0 := by
  obtain ⟨hbin, hN, -, hcross, hsum⟩ := d88_lead hm G hD
  obtain ⟨-, hc0, hc1⟩ := bin_c (hm (bin 1)) hbin ((bin_com G (d88_facts hD).2.2.1).2 0)
  refine sol88_alg (θ := fun k => (m k : ℂ)) (Complex.ofReal_ne_zero.mpr (hm _).ne') hN
    (zh := fun j => (G.z (bin j)).coeff (-2)) (ph := fun j l => (G.p (bin j) (quad l)).coeff 2)
    (c := (G.z (bin 0)).coeff (-2) / (m (bin 1) : ℂ)) (fun j => ?_) hcross hsum
  fin_cases j
  · exact hc0
  · show (G.z (bin 1)).coeff (-2) = (G.z (bin 0)).coeff (-2) / (m (bin 1) : ℂ) * -(m (bin 0) : ℂ)
    rw [hc1]
    ring

/-! ## Integrality -/

/-- The coefficient map `ℤ[μ] → ℚ[m]`, `μ_k ↦ m_{quad k}`. -/
def c88 : MvPolynomial (Fin 4) ℤ →+* MvPolynomial (Fin 6) ℚ :=
  (MvPolynomial.map (Int.castRingHom ℚ)).comp (rename quad).toRingHom

theorem eval_c88 (s : MvPolynomial (Fin 4) ℤ) : eval μ₀88 (c88 s) = (eval μ0Z s : ℚ) := by
  have h : (eval μ₀88).comp c88 = (Int.castRingHom ℚ).comp (eval μ0Z) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)
    · simp [c88]
    · fin_cases k <;> norm_num [c88, μ₀88, μ0Z, quad]
  exact RingHom.congr_fun h s

/-- **Integrality** (the hypothesis of `elim_gInt`): there is `g ∈ ℚ[m]` with `g(μ₀, 1, 1) ≠ 0` such that every
unknown is integral over `ℚ[m][1/g]` modulo `S88`. For `v_i`: by `D88Int` and `exists_rel_of_isIntegral_Opt`,
`s_i v_i^d + Σ_k α_k v_i^k` lies in the ideal of `S12` over `ℤ[μ]` with `s_i(μ₀) ≢ 0 mod p`; its image lies in the
ideal of `S88`. For `q_jl`: `μ₄ ẑ_j q_jl² = −μ₄X_l` is integral, and `μ₄ ẑ_j` divides `g`. Here
`g = (Π_i s_i) m₅ m₆ μ₄`. -/
theorem exists_g88 (h1 : D88Int) : ∃ g : MvPolynomial (Fin 6) ℚ, eval μ₀88 g ≠ 0 ∧
    ∀ i : K88, Ideal.Quotient.mk (Ideal.span S88) (X (Sum.inr i)) ∈
      gInt ((Ideal.Quotient.mk (Ideal.span S88)).comp (rename Sum.inl).toRingHom) g := by
  classical
  choose s d α hs hrel using fun i => exists_rel_of_isIntegral_Opt 65521 μ0Z D88.S12P h1 i
  have hs0 : ∀ i, eval μ₀88 (c88 (s i)) ≠ 0 := fun i => by
    rw [eval_c88]
    exact_mod_cast eval_ne_zero_of_notMem_ptIdeal 65521 μ0Z (hs i)
  refine ⟨(∏ i, c88 (s i)) * X (bin 0) * X (bin 1) * X (quad 3), ?_, ?_⟩
  · simp only [map_mul, map_prod, eval_X]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hs0 i) ?_) ?_) ?_ <;>
      norm_num [μ₀88, bin, quad]
  set g : MvPolynomial (Fin 6) ℚ := (∏ i, c88 (s i)) * X (bin 0) * X (bin 1) * X (quad 3) with hg
  set φ := (Ideal.Quotient.mk (Ideal.span S88)).comp (rename Sum.inl).toRingHom with hφ
  -- the map `ℤ[μ][v] → ℚ[m, v, q]`
  let Ψ : MvPolynomial (Fin 11) (MvPolynomial (Fin 4) ℤ) →+* R88 :=
    eval₂Hom ((rename Sum.inl).toRingHom.comp c88) v88
  have hΨS : ∀ i, Ψ (D88.S12P i) = D88.rows12 μ88 v88 i := fun i => by
    simp only [Ψ, D88.S12P]
    rw [D88.map_rows12]
    congr 1
    · funext k
      simp [μ88, c88]
    · funext j
      simp
  have hΨspan : ∀ y ∈ Ideal.span (Set.range D88.S12P), Ψ y ∈ Ideal.span S88 := fun y hy => by
    have h := Ideal.mem_map_of_mem Ψ hy
    rw [Ideal.map_span] at h
    refine Ideal.span_mono ?_ h
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [hΨS]
    exact row88_mem i
  -- the unknowns `v_i`
  have hv : ∀ i : Fin 11, Ideal.Quotient.mk (Ideal.span S88) (X (Sum.inr (Sum.inl i))) ∈ gInt φ g := fun i => by
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hΨspan _ (hrel i))
    have hy : φ (c88 (s i)) * Ideal.Quotient.mk (Ideal.span S88) (X (Sum.inr (Sum.inl i))) ^ d i +
        ∑ k, φ (c88 (α i k)) * Ideal.Quotient.mk (Ideal.span S88) (X (Sum.inr (Sum.inl i))) ^ (k : ℕ) = 0 := by
      simpa [Ψ, φ, v88] using h0
    refine mem_gInt_of_rel φ g (s := c88 (s i))
      (u := (∏ i' ∈ univ.erase i, c88 (s i')) * X (bin 0) * X (bin 1) * X (quad 3)) (a := 1) ?_ ?_
      (fun k => c88 (α i k)) hy
    · intro h0
      apply hs0 i
      rw [h0, map_zero]
    · rw [pow_one, hg, ← Finset.mul_prod_erase univ (fun i => c88 (s i)) (Finset.mem_univ i)]
      ring
  rintro (i | ⟨j, l⟩)
  · exact hv i
  · -- the unknowns `q_jl`
    have hμ : ∀ k, μ88 k ∈ (gInt φ g).comap (Ideal.Quotient.mk (Ideal.span S88)) := fun k => by
      show Ideal.Quotient.mk (Ideal.span S88) (μ88 k) ∈ gInt φ g
      have e : Ideal.Quotient.mk (Ideal.span S88) (μ88 k) = φ (X (quad k)) := by simp [φ, μ88]
      rw [e]
      exact map_mem_gInt φ g _
    have hXh : Ideal.Quotient.mk (Ideal.span S88) (D88.Xh μ88 v88 l) ∈ gInt φ g :=
      D88.Xh_mem ((gInt φ g).comap (Ideal.Quotient.mk (Ideal.span S88))) hμ (fun i => hv i) l
    have hb := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (bin88_mem j l))
    rw [map_binEq] at hb
    simp only [binEq] at hb
    have hzb : Ideal.Quotient.mk (Ideal.span S88) (μ88 3) *
        zb (fun j => Ideal.Quotient.mk (Ideal.span S88) (mb88 j)) j = φ (X (quad 3) * zb (fun j => X (bin j)) j) := by
      rw [map_mul, map_zb]
      simp [φ, μ88, mb88]
    rw [hzb] at hb
    have hsq : φ (X (quad 3) * zb (fun j => X (bin j)) j) *
        Ideal.Quotient.mk (Ideal.span S88) (q88 j l) ^ 2 ∈ gInt φ g := by
      rw [eq_neg_of_add_eq_zero_left hb]
      exact neg_mem hXh
    obtain ⟨u, hu⟩ : ∃ u, g ^ 1 = u * (X (quad 3) * zb (fun j => X (bin j)) j) := by
      fin_cases j
      · refine ⟨(∏ i, c88 (s i)) * X (bin 0), ?_⟩
        show g ^ 1 = _ * (X (quad 3) * X (bin 1))
        rw [pow_one, hg]
        ring
      · refine ⟨-((∏ i, c88 (s i)) * X (bin 1)), ?_⟩
        show g ^ 1 = _ * (X (quad 3) * -X (bin 0))
        rw [pow_one, hg]
        ring
    exact mem_gInt_of_sq φ g (mem_gInt_of_mul φ g hu hsq)

/-! ## No solution at `(μ₀, 1, 1)` -/

/-- **No complex solution at `(μ₀, m₅, m₆) = (1, 2, 3, 30, 1, 1)`.** A solution has `v` a zero of `S12(μ₀)`, so all
`X_l ≠ 0` and the `T`-test holds at `v` (`d88_Ttest_zeros`). With `p̂_jl = q_jl / X_l` the cross relations are those of
Lemma 6.17 with `c = 1`, so `Σ_{j,l} m_j m_l p̂_jl ≠ 0` (`Ttest_a`), while the torque relation says that
`30³ (Π_l X_l) Σ_{j,l} m_j m_l p̂_jl = 0`. -/
theorem hnone88 (h1 : D88Int) (h2 : D88Dim) (h3 : D88Box) (x : K88 → ℂ) :
    ∃ f ∈ S88, aeval (Sum.elim (fun k => (μ₀88 k : ℂ)) x) f ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hμ : (fun k => ((μ₀88 (quad k) : ℚ) : ℂ)) = D88.μ0 := by
    funext k
    fin_cases k <;> norm_num [μ₀88, quad, D88.μ0]
  have hmb : (fun j => ((μ₀88 (bin j) : ℚ) : ℂ)) = fun _ => 1 := by
    funext j
    fin_cases j <;> norm_num [μ₀88, bin]
  have h30 : ((μ₀88 (quad 3) : ℚ) : ℂ) = 30 := by norm_num [μ₀88, quad]
  have hrow : ∀ i, D88.rows12 D88.μ0 (fun i => x (Sum.inl i)) i = 0 := fun i => by
    have h := hcon _ (row88_mem i)
    rw [aeval_row88, hμ] at h
    exact h
  have hbin0 : ∀ j l, binEq 30 (fun _ => (1 : ℂ)) (fun j l => x (Sum.inr (j, l)))
      (D88.Xh D88.μ0 (fun i => x (Sum.inl i))) j l = 0 := fun j l => by
    have h := hcon _ (bin88_mem j l)
    rw [aeval_bin88, hμ, hmb, h30] at h
    exact h
  have htorq : torqEq D88.μ0 (fun _ => (1 : ℂ)) (fun j l => x (Sum.inr (j, l)))
      (D88.Xh D88.μ0 (fun i => x (Sum.inl i))) = 0 := by
    have h := hcon _ torq88_mem
    rw [aeval_torq88, hμ, hmb] at h
    exact h
  set v : Fin 11 → ℂ := fun i => x (Sum.inl i) with hv
  set q : Fin 2 → Fin 4 → ℂ := fun j l => x (Sum.inr (j, l)) with hq
  have hrows : D88.S12 D88.μ0 v = 0 := (D88.rows12_eq_zero_iff D88.μ0_three_ne v).mp (funext hrow)
  obtain ⟨hX0, k, hk⟩ := d88_Ttest_zeros h1 h2 h3 hrows
  have hXh : ∀ l, D88.Xh D88.μ0 v l = 30 * D88.X D88.μ0 v l := fun l => by
    rw [D88.Xh_eq D88.μ0_three_ne]
    norm_num [D88.μ0]
  set Xv : Fin 4 → ℂ := D88.X D88.μ0 v with hXv
  have hinv : ∀ l, Xv l * (Xv l)⁻¹ = 1 := fun l => mul_inv_cancel₀ (hX0 l)
  -- the cross relations: `ẑ_j q_jl² + X_l = 0` with `ẑ = (1, −1)`
  have hbin : ∀ j l, zb (fun _ => (1 : ℂ)) j * q j l ^ 2 + Xv l = 0 := fun j l => by
    have h := hbin0 j l
    simp only [binEq, hXh] at h
    linear_combination h / 30
  -- the torque relation gives `Σ_{j,l} m_j μ_l p̂_jl = 0` for `p̂_jl = q_jl / X_l`
  have hsum : ∑ j, ∑ l, (fun _ => (1 : ℂ)) j * D88.μ0 l * (q j l * (Xv l)⁻¹) = 0 := by
    rw [torqEq_eq D88.μ0 (fun _ => (1 : ℂ)) (q := q) (X := Xv) (P := fun j l => q j l * (Xv l)⁻¹) (a := 30)
      (b := 1) hXh (fun j l => by linear_combination (-(q j l)) * hinv l)] at htorq
    have hne : (1 : ℂ) * 30 ^ (4 - 1) * ∏ l, Xv l ≠ 0 :=
      mul_ne_zero (by norm_num) (Finset.prod_ne_zero_iff.mpr fun l _ => hX0 l)
    exact (mul_eq_zero.mp htorq).resolve_left hne
  refine Ttest_a (mb := fun _ => (1 : ℝ)) (μ := D88.μ0R) (c := 1) (zh := zb (fun _ => (1 : ℂ))) (X := Xv)
    (P := fun j l => q j l * (Xv l)⁻¹) (fun _ => one_pos) (fun l => ?_) one_ne_zero ?_ ?_ (fun j l => ?_)
    ⟨k, hk⟩ ?_
  · fin_cases l <;> norm_num [D88.μ0R]
  · simp [zb]
  · simp [zb]
  · linear_combination (Xv l)⁻¹ ^ 2 * Xv l * hbin j l - (Xv l * (Xv l)⁻¹ + 1) * hinv l
  · refine Eq.trans (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_) hsum
    fin_cases l <;> norm_num [D88.μ0R, D88.μ0]

/-! ## Theorem 6.20 for diagram 88 -/

/-- **Theorem 6.20** (`thm:d88`), the polynomial `P₈₈`, given the computations of Lemma 6.19 for `S12` as
hypotheses (`D88Int`: Lemma 6.18 with 6.19 (a); `D88Dim`: 6.19 (b); `D88Box`: 6.19 (c)): there is a nonzero
`P ∈ ℤ[m₁, …, m₆]` with `P(m) = 0` for all positive masses `m` that have a germ (a singular place) with diagram `88` in
the labelling of Table 1 (binary `{5, 6}`, `K = {1, 2, 3, 4}`). `P` is the eliminant of the system `S88`
(`elim_gInt`, the integral elimination lemma in place of the implicit function theorem and constructible sets of the
paper); it is nonzero because `P(1, 2, 3, 30, 1, 1) ≠ 0`. -/
theorem d88_poly (h1 : D88Int) (h2 : D88Dim) (h3 : D88Box) : ∃ P : MvPolynomial (Fin 6) ℤ, P ≠ 0 ∧
    ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, G.HasDiagram Diagram.d88 →
      MvPolynomial.aeval m P = 0 := by
  obtain ⟨g, hg, hint⟩ := exists_g88 h1
  obtain ⟨P, hP0, hP⟩ := elim_gInt S88 g hint μ₀88 hg (hnone88 h1 h2 h3)
  refine ⟨P, fun h0 => hP0 (by rw [h0, map_zero]), fun m hm G hD => ?_⟩
  exact aeval_real_eq_zero (hP _ (sol88 hm G hD))

end

end CC6Full.Six
