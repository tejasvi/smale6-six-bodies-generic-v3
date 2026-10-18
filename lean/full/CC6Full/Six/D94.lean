import CC6Full.Six.D94Sys
import CC6Full.Six.D88Lead

/-!
# Diagram 94: the polynomial of Theorem 6.20 (`thm:d88`, the half about `P₉₄`)

§6.7 of the paper (`ss:d88`). At a singular place with diagram `94` the leading data of Lemma 6.16 (b)
(`d94_lead`) solve the centred system `KC(m₁, …, m₄)` with `X₁X₂X₃ ≠ 0`, together with the cross relations
`p̂_jl² ẑ_j X_l = −1` (`j ∈ {5, 6}`, `l ≤ 3`) and the torque relation (eq:t94) `Σ_{j∈{5,6}, l≤3} m_j m_l p̂_jl = 0`.
Theorem 6.20 gives a nonzero `P₉₄ ∈ ℤ[m₁, …, m₆]` vanishing at the masses of every such place. The paper proves it
as for diagram `88` ("the same argument applies to `KC₁₂` with the count `4788` and Lemma 6.19 (d)"), from Lemma 6.18
(`lem:goodred`), the computations of Lemma 6.19 (`lem:d88comp`) at `μ₀ = (1, 2, 3, 30)`, `p = 65521` and
`(m₅, m₆) = (1, 2)`, the implicit function theorem and constructible sets. As for diagram `88` (`CC6Full.Six.d88_poly`)
the last two are replaced by the integral elimination lemma at one point (`elim_gInt`).

## The computations as hypotheses

* `D94Int`: `O[v]/(KC₁₂)` is integral over `O = Opt p μ₀ = ℤ[μ]_𝔪`, `𝔪 = (p, μ − μ₀)` (Lemma 6.18 with Lemma 6.19 (a)
  for the ideal of `KC₁₂`; it is the conclusion of `CC6Full.goodred`).
* `D94Dim`: `dim_{𝔽_p} 𝔽_p[v]/⟨KC(μ₀) mod p⟩ ≤ 4788` (Lemma 6.19 (b)), for the system `KC` of thirteen equations in
  the twelve unknowns of `KC₁₂`: the equations of `KC₁₂` and the `Y`-equation of body `3`.
* `D94Box`: a set `Z` of `4788` complex zeros of `KC₁₂(μ₀)` with `X₁, X₂, X₃ ≠ 0`, at which, for `(m₅, m₆) = (1, 2)`
  and `ρ = (m₆/m₅)^{3/2} = 2^{3/2}`, none of the sums `Σ_{l≤3} ε_l β_l (1 + i s_l ρ)`, `β_l = m_l/√X_l`, of Lemma
  6.17 (b) vanishes, for every choice of the square roots and of the signs `ε, s ∈ {±1}³` (Lemma 6.19 (d)). The
  condition `X_l ≠ 0` is part of the definition of `β_l`; it also follows from the distance equation of `l4`
  (`D94.X_ne_of_dist`), since `X₄ = 0`.

**The system of the dimension hypothesis.** The paper computes the dimension `4788` for the system `KC′` in the
eleven unknowns `X₂, X₃, U₁, U₂, U₃, p₁₂, …, p₃₄` (`U_k = Y_k − Y₄`), whose coordinate ring is that of `KC`: in the
coordinates `U_k`, the `Y`-equation of body `1` is `Y₄ − E(U, p) = 0`, linear in `Y₄` with coefficient `1`, and
`KC′` consists of the other twelve equations of `KC` with `Y₄ = E` substituted (in these coordinates only the
`Y`-equations contain `Y₄`). This holds over any coefficient ring, in particular over `𝔽_p` at `μ₀`, without a unit
condition, so `D94Dim` for `KC` is the computation of Lemma 6.19 (b). The zero set of `KC(μ₀)` in `ℂ¹²` equals that
of `KC₁₂(μ₀)`: one inclusion is trivial, and a zero of `KC₁₂(μ₀)` is a zero of `KC(μ₀)` by the torque identity
(`D94.KC_of_KC12`, with `μ₃ = 3 ≠ 0` and `X₃ ≠ 0`). So the count bounds the zeros of `KC₁₂(μ₀)`.
For the integrality the ideal of `KC` contains that of `KC₁₂`, so `O[v]/(KC)` is a quotient of `O[v]/(KC₁₂)` and is
integral over `O` by `D94Int` (`d94_isIntegral_KC`). (The dimension hypothesis for `KC₁₂` itself would also do: over
`𝔽_p`, `3` is a unit and `X₃` is a unit modulo the distance equation of `34`, so `KC₁₂(μ₀)` and `KC(μ₀)` generate the
same ideal; this needs one more step to be compared with the computation.)

## The proof

* `d94_encard_le`, `d94_zeros_mem`, `d94_zeros_in_box` (the count of §6.7 and the proof of Theorem 6.20): `KC(μ₀)`
  has at most `4788` complex zeros (`encard_zeros_le_of_isIntegral`, "by Nakayama's lemma"); the points of `Z` are
  zeros of `KC(μ₀)` (`D94.KC_of_KC12`); so every complex zero of `KC₁₂(μ₀)` lies in `Z`.
* The elimination. The parameters are the six masses `m` (`μ = m ∘ quad` for `Q`, `(m₅, m₆) = m ∘ bin`), the
  unknowns are `v ∈ ℂ¹²` and `q_jl`, `j ∈ {5, 6}`, `l ≤ 3` (`K94`). The system `S94` consists of `KC` (`D94.KC`), the
  cross relations `binEq` and the torque relation `torqEq`: with the scale `c` of the binary normalized to `1`
  (`ẑ₅ = m₆`, `ẑ₆ = −m₅`) and `q_jl = p̂_jl X_l`, they read `q_5l² m₆ + X_l = 0`, `−q_6l² m₅ + X_l = 0` and
  `Σ_{l≤3} m_l (m₅ q_5l + m₆ q_6l) Π_{l'≠l} X_l' = 0`. On the slice `X₁ = 1` there are no denominators.
  - `sol94`: the leading data give a solution at the masses of the place, after the rotation that makes `X₁ = 1`
    (`D94.slice`, using `X₁ ≠ 0` from Lemma 6.16 (b)) and the normalization of `c` (a square root of `c X₁` rescales
    the `p̂_jl`).
  - `exists_g94`: every unknown is integral over `ℚ[m][1/g]` modulo `S94`, for some `g` with
    `g(μ₀, 1, 2) ≠ 0`: the `v_i` by `D94Int`, after clearing the denominators of the monic relations over `O`, which
    do not vanish at `μ₀` (`exists_rel_of_isIntegral_Opt`); the `q_jl` as square roots of `−X_l/m₆` and `X_l/m₅`.
  - `hnone94`: no complex solution at `(μ₀, 1, 2)`: a solution has `v` a zero of `KC(μ₀)`, so `v ∈ Z`, and
    Lemma 6.17 (b) (`Ttest_b`) turns the cross and torque relations into a vanishing sum `Σ_l ε_l β_l (1 + i s_l ρ)`.
* `d94_poly`: **Theorem 6.20** for diagram `94`, from `elim_gInt`.
-/

namespace CC6Full.Six

open MvPolynomial Finset

noncomputable section

/-! ## The computations of Lemma 6.19 as hypotheses -/

/-- **Lemma 6.18 with Lemma 6.19 (a)** for `KC₁₂`: with `O = Opt p μ₀ = ℤ[μ]_𝔪`, `𝔪 = (p, μ − μ₀)`, `p = 65521`,
`μ₀ = (1, 2, 3, 30)`, the quotient of `O[v]` by the ideal of `KC₁₂` (`D94.KC12P`, polynomial on the slice `X₁ = 1`)
is integral over `O`. This is the conclusion of `CC6Full.goodred` for the certificates of Lemma 6.19 (a). -/
def D94Int : Prop :=
  Algebra.IsIntegral (Opt 65521 μ0Z) (MvPolynomial (Fin 12) (Opt 65521 μ0Z) ⧸
    Ideal.span (Set.range fun i =>
      MvPolynomial.map (algebraMap (MvPolynomial (Fin 4) ℤ) (Opt 65521 μ0Z)) (D94.KC12P i)))

/-- **Lemma 6.19 (b)** for diagram `94`: `dim_{𝔽_p} 𝔽_p[v]/⟨KC(μ₀)⟩ ≤ 4788`, where `KC(μ₀)` is `D94.KCP` (the
equations of `KC₁₂` and the `Y`-equation of body `3`) with its coefficients evaluated at `μ₀ = (1, 2, 3, 30)` and
reduced modulo `p = 65521` (`redPt`). The coordinate ring of `KC` is that of the system `KC′` of the paper, for
which the dimension `4788` is computed: `KC′` is `KC` in the coordinates `U_k = Y_k − Y₄`, with `Y₄` eliminated
through the `Y`-equation of body `1`, which is linear in `Y₄` with coefficient `1`. -/
def D94Dim : Prop :=
  Module.finrank (ZMod 65521) (MvPolynomial (Fin 12) (ZMod 65521) ⧸
    Ideal.span (Set.range fun i => MvPolynomial.map (redPt 65521 μ0Z) (D94.KCP i))) ≤ 4788

/-- **Lemma 6.19 (d)**: there is a set `Z` of `4788` points of `ℂ¹²`, each a zero of `KC₁₂(μ₀)` with
`X₁, X₂, X₃ ≠ 0`, at which, for `(m₅, m₆) = (1, 2)`, none of the sums `Σ_{l≤3} ε_l β_l (1 + i s_l ρ)` of Lemma
6.17 (b) vanishes, with `β_l = m_l / r_l` for square roots `r_l` of `X_l` (any choice), `(m₁, m₂, m₃) = (1, 2, 3)`,
`ρ = (m₆/m₅)^{3/2} = 2^{3/2}` and signs `ε, s ∈ {±1}³`. -/
def D94Box : Prop :=
  ∃ Z : Finset (Fin 12 → ℂ), Z.card = 4788 ∧ ∀ v ∈ Z, D94.KC12 D94.μ0 v = 0 ∧
    (∀ l : Fin 3, D94.X v l.castSucc ≠ 0) ∧
    ∀ r : Fin 3 → ℂ, (∀ l, r l ^ 2 = D94.X v l.castSucc) → ∀ ε s : Fin 3 → ℂ,
      (∀ l, ε l = 1 ∨ ε l = -1) → (∀ l, s l = 1 ∨ s l = -1) →
      ∑ l, ε l * ((D94.μ3R l : ℂ) / r l) * (1 + Complex.I * s l * (((2 : ℝ) ^ ((3 : ℝ) / 2) : ℝ) : ℂ)) ≠ 0

/-! ## The zeros of `KC₁₂(μ₀)` -/

/-- `O[v]/(KC)` is integral over `O`: it is a quotient of `O[v]/(KC₁₂)` (`D94Int`), since the equations of `KC₁₂`
are among those of `KC`. -/
theorem d94_isIntegral_KC (h1 : D94Int) :
    Algebra.IsIntegral (Opt 65521 μ0Z) (MvPolynomial (Fin 12) (Opt 65521 μ0Z) ⧸
      Ideal.span (Set.range fun i =>
        MvPolynomial.map (algebraMap (MvPolynomial (Fin 4) ℤ) (Opt 65521 μ0Z)) (D94.KCP i))) := by
  have hle : Ideal.span (Set.range fun i =>
        MvPolynomial.map (algebraMap (MvPolynomial (Fin 4) ℤ) (Opt 65521 μ0Z)) (D94.KC12P i)) ≤
      Ideal.span (Set.range fun i =>
        MvPolynomial.map (algebraMap (MvPolynomial (Fin 4) ℤ) (Opt 65521 μ0Z)) (D94.KCP i)) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨i.castSucc, congrArg _ (D94.KCP_castSucc i)⟩
  have hA : Algebra.IsIntegral (Opt 65521 μ0Z) (MvPolynomial (Fin 12) (Opt 65521 μ0Z) ⧸
      Ideal.span (Set.range fun i =>
        MvPolynomial.map (algebraMap (MvPolynomial (Fin 4) ℤ) (Opt 65521 μ0Z)) (D94.KC12P i))) := h1
  exact Algebra.IsIntegral.of_surjective (Ideal.Quotient.factorₐ (Opt 65521 μ0Z) hle)
    (Ideal.Quotient.factor_surjective hle)

/-- **The count** of §6.7 for diagram `94`: by Lemma 6.18 and Lemma 6.19 (a), (b), `KC(μ₀)` has at most `4788`
complex zeros (`encard_zeros_le_of_isIntegral`). -/
theorem d94_encard_le (h1 : D94Int) (h2 : D94Dim) :
    {v : Fin 12 → ℂ | D94.KC D94.μ0 v = 0}.encard ≤ 4788 := by
  have h := encard_zeros_le_of_isIntegral 65521 μ0Z D94.KCP (d94_isIntegral_KC h1) h2
  have hset : {v : Fin 12 → ℂ | D94.KC D94.μ0 v = 0} =
      {z : Fin 12 → ℂ | ∀ i, eval z (MvPolynomial.map ((Int.castRingHom ℂ).comp (eval μ0Z)) (D94.KCP i)) = 0} := by
    ext v
    simp only [Set.mem_ofPred_eq, D94.eval_KCP_μ0]
    exact funext_iff
  rw [hset]
  exact_mod_cast h

/-- **Every complex zero of `KC₁₂(μ₀)` lies in a set of `4788` zeros of `KC₁₂(μ₀)`**: the points of the set are
zeros of `KC(μ₀)` (`D94.KC_of_KC12`), and `KC(μ₀)` has at most `4788` zeros (`d94_encard_le`). -/
theorem d94_zeros_mem (h1 : D94Int) (h2 : D94Dim) {Z : Finset (Fin 12 → ℂ)} (hZ : Z.card = 4788)
    (hsub : ∀ v ∈ Z, D94.KC12 D94.μ0 v = 0) {v : Fin 12 → ℂ} (hv : D94.KC12 D94.μ0 v = 0) : v ∈ Z := by
  have heq : (Z : Set (Fin 12 → ℂ)) = {v | D94.KC D94.μ0 v = 0} := by
    refine Set.Finite.eq_of_subset_of_encard_le Z.finite_toSet
      (fun w hw => D94.KC_of_KC12 D94.μ0_two_ne (hsub w hw)) ?_
    rw [Set.encard_coe_eq_coe_finsetCard, hZ]
    exact_mod_cast d94_encard_le h1 h2
  have hv' : v ∈ ({v | D94.KC D94.μ0 v = 0} : Set (Fin 12 → ℂ)) := D94.KC_of_KC12 D94.μ0_two_ne hv
  rw [← heq] at hv'
  exact hv'

/-- **All complex zeros of `KC₁₂(μ₀)` lie in the set `Z` of Lemma 6.19 (d)** (`D94Box`), §6.7: "by Nakayama's lemma
the two systems have at most `20,316` and `4788` complex zeros at `μ₀`, so the boxes of (c) and (d) contain all of
them" (`d94_zeros_mem`). -/
theorem d94_zeros_in_box (h1 : D94Int) (h2 : D94Dim) (h3 : D94Box) :
    ∃ Z : Finset (Fin 12 → ℂ), Z.card = 4788 ∧ (∀ v ∈ Z, D94.KC12 D94.μ0 v = 0 ∧
      (∀ l : Fin 3, D94.X v l.castSucc ≠ 0) ∧
      ∀ r : Fin 3 → ℂ, (∀ l, r l ^ 2 = D94.X v l.castSucc) → ∀ ε s : Fin 3 → ℂ,
        (∀ l, ε l = 1 ∨ ε l = -1) → (∀ l, s l = 1 ∨ s l = -1) →
        ∑ l, ε l * ((D94.μ3R l : ℂ) / r l) * (1 + Complex.I * s l * (((2 : ℝ) ^ ((3 : ℝ) / 2) : ℝ) : ℂ)) ≠ 0) ∧
      ∀ v, D94.KC12 D94.μ0 v = 0 → v ∈ Z := by
  obtain ⟨Z, hcard, hZ⟩ := h3
  exact ⟨Z, hcard, hZ, fun v hv => d94_zeros_mem h1 h2 hcard (fun w hw => (hZ w hw).1) hv⟩

/-! ## The system of the elimination -/

/-- The unknowns of the elimination: `v ∈ ℂ¹²` (`Sum.inl`) and the `q_jl = p̂_jl X_l`, `j ∈ {5, 6}` (`Fin 2`),
`l ∈ {1, 2, 3}` (`Fin 3`) (`Sum.inr`). -/
abbrev K94 := Fin 12 ⊕ (Fin 2 × Fin 3)

/-- The polynomial ring `ℚ[m, v, q]`; the parameters `m_k = X (Sum.inl k)`, `k : Fin 6`, are the masses of the
six bodies (`Q = {1, 2, 3, 4}` renumbered by `quad`, its bodies `1, 2, 3` by `triB`, the binary `{5, 6}` by `bin`). -/
abbrev R94 := MvPolynomial (Fin 6 ⊕ K94) ℚ

/-- The masses `μ_k = m_{quad k}` of `Q`. -/
def μ94 (k : Fin 4) : R94 := X (Sum.inl (quad k))

/-- The masses `m_{bin j}` of the binary. -/
def mb94 (j : Fin 2) : R94 := X (Sum.inl (bin j))

/-- The masses `m_{triB l}` of the bodies `1, 2, 3`. -/
def mt94 (l : Fin 3) : R94 := X (Sum.inl (triB l))

/-- The unknowns `v_i`. -/
def v94 (i : Fin 12) : R94 := X (Sum.inr (Sum.inl i))

/-- The unknowns `q_jl`. -/
def q94 (j : Fin 2) (l : Fin 3) : R94 := X (Sum.inr (Sum.inr (j, l)))

/-- **The system of the elimination**: `KC` on the slice `X₁ = 1` (`D94.KC`), the cross relations `binEq` and the
torque relation `torqEq` (with the scale of the binary normalized to `1` and `q_jl = p̂_jl X_l`), for the bodies
`1, 2, 3` (`D94.X3`). -/
def S94 : Set R94 :=
  Set.range (D94.KC μ94 v94) ∪
    Set.range (fun jl : Fin 2 × Fin 3 => binEq 1 mb94 q94 (D94.X3 v94) jl.1 jl.2) ∪
    {torqEq mt94 mb94 q94 (D94.X3 v94)}

theorem kc94_mem (i : Fin 13) : D94.KC μ94 v94 i ∈ S94 := Or.inl (Or.inl ⟨i, rfl⟩)

theorem kc12_94_mem (i : Fin 12) : D94.KC12 μ94 v94 i ∈ S94 := by
  rw [← D94.KC_castSucc]
  exact kc94_mem _

theorem bin94_mem (j : Fin 2) (l : Fin 3) : binEq 1 mb94 q94 (D94.X3 v94) j l ∈ S94 :=
  Or.inl (Or.inr ⟨(j, l), rfl⟩)

theorem torq94_mem : torqEq mt94 mb94 q94 (D94.X3 v94) ∈ S94 := Or.inr rfl

/-- The parameter point `(μ₀, m₅, m₆) = (1, 2, 3, 30, 1, 2)`. -/
def μ₀94 : Fin 6 → ℚ := ![1, 2, 3, 30, 1, 2]

section Eval

variable (θ : Fin 6 → ℂ) (x : K94 → ℂ)

@[simp] theorem aeval_μ94 (k : Fin 4) : aeval (Sum.elim θ x) (μ94 k) = θ (quad k) := by simp [μ94]

@[simp] theorem aeval_mb94 (j : Fin 2) : aeval (Sum.elim θ x) (mb94 j) = θ (bin j) := by simp [mb94]

@[simp] theorem aeval_mt94 (l : Fin 3) : aeval (Sum.elim θ x) (mt94 l) = θ (triB l) := by simp [mt94]

@[simp] theorem aeval_v94 (i : Fin 12) : aeval (Sum.elim θ x) (v94 i) = x (Sum.inl i) := by simp [v94]

@[simp] theorem aeval_q94 (j : Fin 2) (l : Fin 3) : aeval (Sum.elim θ x) (q94 j l) = x (Sum.inr (j, l)) := by
  simp [q94]

theorem aeval_kc94 (i : Fin 13) : aeval (Sum.elim θ x) (D94.KC μ94 v94 i) =
    D94.KC (fun k => θ (quad k)) (fun i => x (Sum.inl i)) i := by
  rw [D94.map_KC]
  simp

theorem aeval_X3_94 (l : Fin 3) : aeval (Sum.elim θ x) (D94.X3 v94 l) = D94.X3 (fun i => x (Sum.inl i)) l := by
  rw [D94.map_X3]
  simp

theorem aeval_bin94 (j : Fin 2) (l : Fin 3) : aeval (Sum.elim θ x) (binEq 1 mb94 q94 (D94.X3 v94) j l) =
    binEq 1 (fun j => θ (bin j)) (fun j l => x (Sum.inr (j, l))) (D94.X3 (fun i => x (Sum.inl i))) j l := by
  rw [map_binEq]
  simp [aeval_X3_94]

theorem aeval_torq94 : aeval (Sum.elim θ x) (torqEq mt94 mb94 q94 (D94.X3 v94)) =
    torqEq (fun l => θ (triB l)) (fun j => θ (bin j)) (fun j l => x (Sum.inr (j, l)))
      (D94.X3 (fun i => x (Sum.inl i))) := by
  rw [map_torqEq]
  simp [aeval_X3_94]

end Eval

/-! ## The leading data give a solution -/

/-- The algebra of `sol94`, for masses `θ` and data `(X, Y, P)` solving `KC(θ_Q)` with `X₁ ≠ 0`, cross coefficients
`p̂_jl` with `p̂_jl² ẑ_j X_l = −1` (`l ≤ 3`), `ẑ_j = c ẑ'_j` for the normalized `ẑ' = zb θ_bin`, and the torque
relation `Σ_{j, l≤3} m_j m_l p̂_jl = 0`. With `v = D94.slice X Y P` (the rotation that makes `X₁ = 1`) and
`q_jl = r p̂_jl X_l/X₁`, `r² = c X₁`, the point `(v, q)` solves `S94` at `θ`. -/
theorem sol94_alg {θ : Fin 6 → ℂ} {Xo Yo : Fin 4 → ℂ} {P : Fin 4 → Fin 4 → ℂ}
    (hKC : IsKC (fun l => θ (quad l)) Xo Yo P) (h0 : Xo 0 ≠ 0) {zh : Fin 2 → ℂ} {ph : Fin 2 → Fin 3 → ℂ}
    {c : ℂ} (hzc : ∀ j, zh j = c * zb (fun j => θ (bin j)) j)
    (hcross : ∀ j l, ph j l ^ 2 * zh j * Xo l.castSucc = -1)
    (hsum : ∑ j, ∑ l, θ (bin j) * θ (triB l) * ph j l = 0) :
    ∃ x : K94 → ℂ, ∀ f ∈ S94, aeval (Sum.elim θ x) f = 0 := by
  have ha : (Xo 0)⁻¹ * Xo 0 = 1 := inv_mul_cancel₀ h0
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (c * Xo 0) two_pos
  have hX3 : ∀ l, D94.X3 (D94.slice Xo Yo P) l = (Xo 0)⁻¹ * Xo l.castSucc := fun l =>
    D94.X_slice (Yo := Yo) (P := P) h0 hKC.2.1 l.castSucc
  refine ⟨Sum.elim (D94.slice Xo Yo P) fun jl => r * ph jl.1 jl.2 * ((Xo 0)⁻¹ * Xo jl.2.castSucc), ?_⟩
  rintro f ((⟨i, rfl⟩ | ⟨⟨j, l⟩, rfl⟩) | rfl)
  · -- the equations of `KC`
    rw [aeval_kc94]
    exact congrFun (D94.KC_slice hKC h0) i
  · -- the cross relations
    rw [aeval_bin94]
    show 1 * zb (fun j => θ (bin j)) j * (r * ph j l * ((Xo 0)⁻¹ * Xo l.castSucc)) ^ 2 +
      D94.X3 (D94.slice Xo Yo P) l = 0
    rw [hX3 l]
    linear_combination zb (fun j => θ (bin j)) j * ph j l ^ 2 * (Xo 0)⁻¹ ^ 2 * Xo l.castSucc ^ 2 * hr +
      zb (fun j => θ (bin j)) j * c * ph j l ^ 2 * (Xo 0)⁻¹ * Xo l.castSucc ^ 2 * ha -
      (Xo 0)⁻¹ * Xo l.castSucc ^ 2 * ph j l ^ 2 * hzc j + (Xo 0)⁻¹ * Xo l.castSucc * hcross j l
  · -- the torque relation
    rw [aeval_torq94]
    show torqEq (fun l => θ (triB l)) (fun j => θ (bin j))
      (fun j l => r * ph j l * ((Xo 0)⁻¹ * Xo l.castSucc)) (D94.X3 (D94.slice Xo Yo P)) = 0
    rw [torqEq_eq (fun l => θ (triB l)) (fun j => θ (bin j))
      (q := fun j l => r * ph j l * ((Xo 0)⁻¹ * Xo l.castSucc)) (X := fun l => (Xo 0)⁻¹ * Xo l.castSucc)
      (P := ph) (a := 1) (b := r) (fun l => by rw [hX3 l, one_mul]) (fun j l => rfl)]
    simp only [hsum, mul_zero]

/-- **The leading data of Lemma 6.16 (b) give a solution of `S94`** at the masses of the place (`d94_lead`,
`sol94_alg`): `X₁ ≠ 0`, and `ẑ₅ = c m₆`, `ẑ₆ = −c m₅` with `c = ẑ₅/m₆` (`bin_c`). -/
theorem sol94 {m : Fin 6 → ℝ} (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d94) :
    ∃ x : K94 → ℂ, ∀ f ∈ S94, aeval (Sum.elim (fun k => (m k : ℂ)) x) f = 0 := by
  obtain ⟨hbin, hKC, hX0, hcross, hsum⟩ := d94_lead hm G hD
  obtain ⟨-, hc0, hc1⟩ := bin_c (hm (bin 1)) hbin ((bin_com G (d94_facts hD).2.2.1).2 0)
  refine sol94_alg (θ := fun k => (m k : ℂ)) hKC (hX0 0)
    (zh := fun j => (G.z (bin j)).coeff (-2)) (ph := fun j l => (G.p (bin j) (triB l)).coeff 2)
    (c := (G.z (bin 0)).coeff (-2) / (m (bin 1) : ℂ)) (fun j => ?_) hcross hsum
  fin_cases j
  · exact hc0
  · show (G.z (bin 1)).coeff (-2) = (G.z (bin 0)).coeff (-2) / (m (bin 1) : ℂ) * -(m (bin 0) : ℂ)
    rw [hc1]
    ring

/-! ## Integrality -/

/-- The coefficient map `ℤ[μ] → ℚ[m]`, `μ_k ↦ m_{quad k}`. -/
def c94 : MvPolynomial (Fin 4) ℤ →+* MvPolynomial (Fin 6) ℚ :=
  (MvPolynomial.map (Int.castRingHom ℚ)).comp (rename quad).toRingHom

theorem eval_c94 (s : MvPolynomial (Fin 4) ℤ) : eval μ₀94 (c94 s) = (eval μ0Z s : ℚ) := by
  have h : (eval μ₀94).comp c94 = (Int.castRingHom ℚ).comp (eval μ0Z) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)
    · simp [c94]
    · fin_cases k <;> norm_num [c94, μ₀94, μ0Z, quad]
  exact RingHom.congr_fun h s

/-- **Integrality** (the hypothesis of `elim_gInt`): there is `g ∈ ℚ[m]` with `g(μ₀, 1, 2) ≠ 0` such that every
unknown is integral over `ℚ[m][1/g]` modulo `S94`. For `v_i`: by `D94Int` and `exists_rel_of_isIntegral_Opt`,
`s_i v_i^d + Σ_k α_k v_i^k` lies in the ideal of `KC₁₂` over `ℤ[μ]` with `s_i(μ₀) ≢ 0 mod p`; its image lies in the
ideal of `S94`. For `q_jl`: `ẑ_j q_jl² = −X_l` is integral, and `ẑ_j ∈ {m₆, −m₅}` divides `g`. Here
`g = (Π_i s_i) m₅ m₆`. -/
theorem exists_g94 (h1 : D94Int) : ∃ g : MvPolynomial (Fin 6) ℚ, eval μ₀94 g ≠ 0 ∧
    ∀ i : K94, Ideal.Quotient.mk (Ideal.span S94) (X (Sum.inr i)) ∈
      gInt ((Ideal.Quotient.mk (Ideal.span S94)).comp (rename Sum.inl).toRingHom) g := by
  classical
  choose s d α hs hrel using fun i => exists_rel_of_isIntegral_Opt 65521 μ0Z D94.KC12P h1 i
  have hs0 : ∀ i, eval μ₀94 (c94 (s i)) ≠ 0 := fun i => by
    rw [eval_c94]
    exact_mod_cast eval_ne_zero_of_notMem_ptIdeal 65521 μ0Z (hs i)
  refine ⟨(∏ i, c94 (s i)) * X (bin 0) * X (bin 1), ?_, ?_⟩
  · simp only [map_mul, map_prod, eval_X]
    refine mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hs0 i) ?_) ?_ <;>
      norm_num [μ₀94, bin]
  set g : MvPolynomial (Fin 6) ℚ := (∏ i, c94 (s i)) * X (bin 0) * X (bin 1) with hg
  set φ := (Ideal.Quotient.mk (Ideal.span S94)).comp (rename Sum.inl).toRingHom with hφ
  -- the map `ℤ[μ][v] → ℚ[m, v, q]`
  let Ψ : MvPolynomial (Fin 12) (MvPolynomial (Fin 4) ℤ) →+* R94 :=
    eval₂Hom ((rename Sum.inl).toRingHom.comp c94) v94
  have hΨS : ∀ i, Ψ (D94.KC12P i) = D94.KC12 μ94 v94 i := fun i => by
    simp only [Ψ, D94.KC12P]
    rw [D94.map_KC12]
    congr 1
    · funext k
      simp [μ94, c94]
    · funext j
      simp
  have hΨspan : ∀ y ∈ Ideal.span (Set.range D94.KC12P), Ψ y ∈ Ideal.span S94 := fun y hy => by
    have h := Ideal.mem_map_of_mem Ψ hy
    rw [Ideal.map_span] at h
    refine Ideal.span_mono ?_ h
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [hΨS]
    exact kc12_94_mem i
  -- the unknowns `v_i`
  have hv : ∀ i : Fin 12, Ideal.Quotient.mk (Ideal.span S94) (X (Sum.inr (Sum.inl i))) ∈ gInt φ g := fun i => by
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hΨspan _ (hrel i))
    have hy : φ (c94 (s i)) * Ideal.Quotient.mk (Ideal.span S94) (X (Sum.inr (Sum.inl i))) ^ d i +
        ∑ k, φ (c94 (α i k)) * Ideal.Quotient.mk (Ideal.span S94) (X (Sum.inr (Sum.inl i))) ^ (k : ℕ) = 0 := by
      simpa [Ψ, φ, v94] using h0
    refine mem_gInt_of_rel φ g (s := c94 (s i))
      (u := (∏ i' ∈ univ.erase i, c94 (s i')) * X (bin 0) * X (bin 1)) (a := 1) ?_ ?_
      (fun k => c94 (α i k)) hy
    · intro h0
      apply hs0 i
      rw [h0, map_zero]
    · rw [pow_one, hg, ← Finset.mul_prod_erase univ (fun i => c94 (s i)) (Finset.mem_univ i)]
      ring
  rintro (i | ⟨j, l⟩)
  · exact hv i
  · -- the unknowns `q_jl`
    have hX3 : Ideal.Quotient.mk (Ideal.span S94) (D94.X3 v94 l) ∈ gInt φ g := by
      fin_cases l
      · show Ideal.Quotient.mk (Ideal.span S94) 1 ∈ gInt φ g
        rw [map_one]
        exact one_mem _
      · exact hv 0
      · exact hv 1
    have hb := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (bin94_mem j l))
    rw [map_binEq] at hb
    simp only [binEq, map_one, one_mul] at hb
    have hzb : zb (fun j => Ideal.Quotient.mk (Ideal.span S94) (mb94 j)) j =
        φ (zb (fun j => X (bin j)) j) := by
      rw [map_zb]
      simp [φ, mb94]
    rw [hzb] at hb
    have hsq : φ (zb (fun j => X (bin j)) j) * Ideal.Quotient.mk (Ideal.span S94) (q94 j l) ^ 2 ∈ gInt φ g := by
      rw [eq_neg_of_add_eq_zero_left hb]
      exact neg_mem hX3
    obtain ⟨u, hu⟩ : ∃ u, g ^ 1 = u * zb (fun j => X (bin j)) j := by
      fin_cases j
      · refine ⟨(∏ i, c94 (s i)) * X (bin 0), ?_⟩
        show g ^ 1 = _ * X (bin 1)
        linear_combination hg
      · refine ⟨-((∏ i, c94 (s i)) * X (bin 1)), ?_⟩
        show g ^ 1 = _ * -X (bin 0)
        linear_combination hg
    exact mem_gInt_of_sq φ g (mem_gInt_of_mul φ g hu hsq)

/-! ## No solution at `(μ₀, 1, 2)` -/

/-- The binary masses `(m₅, m₆) = (1, 2)` of Lemma 6.19 (d), as reals. -/
def mb0R : Fin 2 → ℝ := ![1, 2]

/-- **No complex solution at `(μ₀, m₅, m₆) = (1, 2, 3, 30, 1, 2)`.** A solution has `v` a zero of `KC(μ₀)`, so
`v` lies in the set `Z` of Lemma 6.19 (d) (`d94_zeros_mem`), with `X₁, X₂, X₃ ≠ 0`. With `p̂_jl = q_jl / X_l` the
cross relations are those of Lemma 6.17 with `c = 1`, and the torque relation says that
`(Π_{l≤3} X_l) Σ_{j, l≤3} m_j m_l p̂_jl = 0`; so by Lemma 6.17 (b) (`Ttest_b`) some sum `Σ_l ε_l β_l (1 + i s_l ρ)`
vanishes, `ρ = (2/1)^{3/2}`, which `D94Box` excludes. -/
theorem hnone94 (h1 : D94Int) (h2 : D94Dim) (h3 : D94Box) (x : K94 → ℂ) :
    ∃ f ∈ S94, aeval (Sum.elim (fun k => (μ₀94 k : ℂ)) x) f ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hμ : (fun k => ((μ₀94 (quad k) : ℚ) : ℂ)) = D94.μ0 := by
    funext k
    fin_cases k <;> norm_num [μ₀94, quad, D94.μ0]
  have hmb : (fun j => ((μ₀94 (bin j) : ℚ) : ℂ)) = fun j => ((mb0R j : ℝ) : ℂ) := by
    funext j
    fin_cases j <;> norm_num [μ₀94, bin, mb0R]
  have hmt : (fun l => ((μ₀94 (triB l) : ℚ) : ℂ)) = fun l => ((D94.μ3R l : ℝ) : ℂ) := by
    funext l
    fin_cases l <;> norm_num [μ₀94, triB, D94.μ3R]
  have hrow : D94.KC D94.μ0 (fun i => x (Sum.inl i)) = 0 := by
    funext i
    have h := hcon _ (kc94_mem i)
    rw [aeval_kc94, hμ] at h
    exact h
  have hbin : ∀ j l, binEq 1 (fun j => ((mb0R j : ℝ) : ℂ)) (fun j l => x (Sum.inr (j, l)))
      (D94.X3 (fun i => x (Sum.inl i))) j l = 0 := fun j l => by
    have h := hcon _ (bin94_mem j l)
    rw [aeval_bin94, hmb] at h
    exact h
  have htorq : torqEq (fun l => ((D94.μ3R l : ℝ) : ℂ)) (fun j => ((mb0R j : ℝ) : ℂ))
      (fun j l => x (Sum.inr (j, l))) (D94.X3 (fun i => x (Sum.inl i))) = 0 := by
    have h := hcon _ torq94_mem
    rw [aeval_torq94, hmt, hmb] at h
    exact h
  set v : Fin 12 → ℂ := fun i => x (Sum.inl i) with hv
  set q : Fin 2 → Fin 3 → ℂ := fun j l => x (Sum.inr (j, l)) with hq
  -- `v` lies in the set `Z` of Lemma 6.19 (d)
  obtain ⟨Z, hcard, hZ⟩ := h3
  have hvZ : v ∈ Z := d94_zeros_mem h1 h2 hcard (fun w hw => (hZ w hw).1) (D94.KC12_of_KC hrow)
  obtain ⟨-, hX0, hsums⟩ := hZ v hvZ
  set Xv : Fin 3 → ℂ := D94.X3 v with hXv
  have hinv : ∀ l, Xv l * (Xv l)⁻¹ = 1 := fun l => mul_inv_cancel₀ (hX0 l)
  -- the cross relations: `p̂_jl² ẑ_j X_l = −1` with `p̂_jl = q_jl / X_l` and `ẑ = (m₆, −m₅) = (2, −1)`
  have hP : ∀ j l, (q j l * (Xv l)⁻¹) ^ 2 * zb (fun j => ((mb0R j : ℝ) : ℂ)) j * Xv l = -1 := fun j l => by
    have h := hbin j l
    simp only [binEq] at h
    linear_combination (Xv l)⁻¹ ^ 2 * Xv l * h - (Xv l * (Xv l)⁻¹ + 1) * hinv l
  -- the torque relation gives `Σ_{j, l} m_j m_l p̂_jl = 0`
  have hsum : ∑ j, ∑ l, ((mb0R j : ℝ) : ℂ) * ((D94.μ3R l : ℝ) : ℂ) * (q j l * (Xv l)⁻¹) = 0 := by
    rw [torqEq_eq (fun l => ((D94.μ3R l : ℝ) : ℂ)) (fun j => ((mb0R j : ℝ) : ℂ)) (q := q) (X := Xv)
      (P := fun j l => q j l * (Xv l)⁻¹) (a := 1) (b := 1) (fun l => (one_mul _).symm)
      (fun j l => by linear_combination (-(q j l)) * hinv l)] at htorq
    have hne : (1 : ℂ) * 1 ^ (3 - 1) * ∏ l, Xv l ≠ 0 :=
      mul_ne_zero (by norm_num) (Finset.prod_ne_zero_iff.mpr fun l _ => hX0 l)
    exact (mul_eq_zero.mp htorq).resolve_left hne
  -- square roots of the `X_l` and Lemma 6.17 (b)
  obtain ⟨r, hr⟩ : ∃ r : Fin 3 → ℂ, ∀ l, r l ^ 2 = Xv l :=
    ⟨fun l => Xv l ^ ((2 : ℕ) : ℂ)⁻¹, fun l => Complex.cpow_nat_inv_pow _ two_ne_zero⟩
  obtain ⟨ε, s, hε, hs, hzero⟩ := Ttest_b (mb := mb0R) (fun j => by fin_cases j <;> norm_num [mb0R])
    D94.μ3R (c := 1) one_ne_zero (zh := zb (fun j => ((mb0R j : ℝ) : ℂ))) (by simp [zb]) (by simp [zb])
    (X := Xv) (P := fun j l => q j l * (Xv l)⁻¹) hP hr hsum
  rw [show mb0R 1 / mb0R 0 = (2 : ℝ) by norm_num [mb0R]] at hzero
  exact hsums r hr ε s hε hs hzero

/-! ## Theorem 6.20 for diagram 94 -/

/-- **Theorem 6.20** (`thm:d88`), the polynomial `P₉₄`, given the computations of Lemma 6.19 for diagram `94` as
hypotheses (`D94Int`: Lemma 6.18 with 6.19 (a) for `KC₁₂`; `D94Dim`: 6.19 (b) for `KC`, whose coordinate ring is
that of `KC′`; `D94Box`: 6.19 (d)): there is a nonzero `P ∈ ℤ[m₁, …, m₆]` with `P(m) = 0` for all positive masses
`m` that have a germ (a singular place) with diagram `94` in the labelling of Table 1 (the triangle `{4, 5, 6}` with
`z`-circles at `5, 6`, `Q = {1, 2, 3, 4}` with `w`-circles at `1, 2, 3`). `P` is the eliminant of the system `S94`
(`elim_gInt`, the integral elimination lemma in place of the implicit function theorem and constructible sets of the
paper); it is nonzero because `P(1, 2, 3, 30, 1, 2) ≠ 0`. -/
theorem d94_poly (h1 : D94Int) (h2 : D94Dim) (h3 : D94Box) : ∃ P : MvPolynomial (Fin 6) ℤ, P ≠ 0 ∧
    ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, G.HasDiagram Diagram.d94 →
      MvPolynomial.aeval m P = 0 := by
  obtain ⟨g, hg, hint⟩ := exists_g94 h1
  obtain ⟨P, hP0, hP⟩ := elim_gInt S94 g hint μ₀94 hg (hnone94 h1 h2 h3)
  refine ⟨P, fun h0 => hP0 (by rw [h0, map_zero]), fun m hm G hD => ?_⟩
  exact aeval_real_eq_zero (hP _ (sol94 hm G hD))

end

end CC6Full.Six
