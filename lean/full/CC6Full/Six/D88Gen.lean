import CC6Full.Algebra.PointCount
import CC6Full.Six.D98Elim
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.Tactic.NormNum.Prime

/-!
# General pieces of the proof of Theorem 6.20 (diagrams 88 and 94)

Theorem 6.20 of the paper (`thm:d88`) gives nonzero polynomials `P₈₈`, `P₉₄` in the masses. The paper's proof
combines Lemma 6.18 (`lem:goodred`), the computations of Lemma 6.19 (`lem:d88comp`) at `μ₀ = (1, 2, 3, 30)` and
`p = 65521`, the implicit function theorem and constructible sets. Here the last two are replaced by the integral
elimination lemma `CC6Full.elim_integral_int` at one parameter point (through `CC6Full.Six.elim_gInt`). This file
collects the parts that do not depend on the diagram, so that diagram `94` can use them as well.

* `sum_ite_eq_sum_erase`, `sum_mul_force_eq_zero` and `isNSys_com` (the centre of mass of the systems `N(μ)` of
  §6.4 and §6.7), `force_smul` (the force is linear in the positions, so `N(μ)` is invariant under `X ↦ λX`,
  `Y ↦ λ⁻¹Y`).
* `fact_prime_65521`, `μ0Z`: the prime and the masses of Lemma 6.19.
* The local ring `O = Opt p μ₀ = ℤ[μ]_𝔪` (`CC6Full/Algebra/PointCount.lean`): `eval_ne_zero_of_notMem_ptIdeal`,
  `algebraMap_Opt_injective`, `resPt_comp_algebraMap`, `evalPt_comp_algebraMap`.
* `exists_rel_of_isIntegral_Opt`: if `O[v]/(S)` is integral over `O` (the conclusion of Lemma 6.18, `goodred`) for
  polynomials `S` over `ℤ[μ]`, then every `v_j` satisfies `s v_j^d + Σ_{k<d} α_k v_j^k ∈ (S)` in `ℤ[μ][v]` with
  `s ∉ 𝔪`: the denominators of a monic relation over `O` are cleared. In particular `s(μ₀) ≠ 0`, so `v_j` is integral
  over `ℚ[μ][1/s]`, the form needed by the integral elimination lemma.
* `encard_zeros_le_of_isIntegral`: the count of Theorem 6.20 (`encard_complexZeros_le`, "by Nakayama's lemma"),
  for polynomials over `ℤ[μ]`: the zeros in `ℂ^N` of `S(μ₀)` are at most `dim_{𝔽_p} 𝔽_p[v]/(S(μ₀) mod p)`.
* `mem_gInt_of_mul`, `mem_gInt_of_rel`: two closure properties of the elements integral over `A[1/g]` (`gInt`).
* The binary `{5, 6}` of diagrams `88` and `94`, normalized as in the proof of Lemma 6.17 (`lem:Ttest`): `zb`
  (`(ẑ₅, ẑ₆) = (m₆, −m₅)`, the scale `c` set to `1`), `binEq` (the cross relations `p̂_jl² ẑ_j X_l = −1` of Lemma
  6.16 written for `q_jl = p̂_jl X_l`), `torqEq` (the torque relations (6.1), (6.2) multiplied by `Π_l X_l`), their
  images under ring homomorphisms, and `torqEq_eq`, which recovers `Σ_{j,l} m_j m_l p̂_jl` from `torqEq`.
-/

namespace CC6Full.Six

open MvPolynomial Finset

noncomputable section

/-! ## The centre of mass and the scaling of `N(μ)` -/

/-- A sum over `l ≠ k` written with `if`, as a sum over `univ.erase k`. -/
theorem sum_ite_eq_sum_erase {N : ℕ} {R : Type*} [AddCommMonoid R] (k : Fin N) (f : Fin N → R) :
    (∑ l, if l = k then 0 else f l) = ∑ l ∈ univ.erase k, f l := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), ite_eq_left rfl, zero_add]
  exact Finset.sum_congr rfl fun l hl => ite_eq_right (Finset.ne_of_mem_erase hl)

/-- **The centre of mass of the forces**: `Σ_k μ_k Φ_k(h) = 0` for a symmetric family `p`, since the terms of the
pairs `kl` and `lk` cancel. At a solution of `N(μ)` (§6.4, §6.7) this gives `Σ_k μ_k z_k = 0`. -/
theorem sum_mul_force_eq_zero {N : ℕ} (μ : Fin N → ℂ) {p : Fin N → Fin N → ℂ} (hp : IsSymm p) (h : Fin N → ℂ) :
    ∑ k, μ k * force μ p h k = 0 := by
  have h1 : ∀ k, μ k * force μ p h k = ∑ l, μ k * (μ l * p k l ^ 3 * (h k - h l)) := fun k => by
    rw [force, Finset.mul_sum]
    exact Finset.sum_erase _ (by simp)
  have h2 : ∑ k, ∑ l, μ k * (μ l * p k l ^ 3 * (h k - h l)) =
      -∑ k, ∑ l, μ k * (μ l * p k l ^ 3 * (h k - h l)) := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hp l k]
    ring
  rw [Finset.sum_congr rfl fun k _ => h1 k]
  linear_combination h2 / 2

/-- The force is linear in the positions: `Φ_k(a h) = a Φ_k(h)`. -/
theorem force_smul {N : ℕ} (μ : Fin N → ℂ) (p : Fin N → Fin N → ℂ) (h : Fin N → ℂ) (a : ℂ) (k : Fin N) :
    force μ p (fun l => a * h l) k = a * force μ p h k := by
  simp only [force, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- The centre of mass of a solution of `N(μ)`: `Σ_k μ_k z_k = 0` and `Σ_k μ_k w_k = 0`. -/
theorem isNSys_com {N : ℕ} {μ z w : Fin N → ℂ} {p : Fin N → Fin N → ℂ} (h : IsNSys μ z w p) :
    ∑ k, μ k * z k = 0 ∧ ∑ k, μ k * w k = 0 := by
  obtain ⟨hp, hz, hw, -⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_congr rfl fun k _ => congrArg (fun t => μ k * t) (hz k)]
    exact sum_mul_force_eq_zero μ hp z
  · rw [Finset.sum_congr rfl fun k _ => congrArg (fun t => μ k * t) (hw k)]
    exact sum_mul_force_eq_zero μ hp w

/-! ## The prime and the masses of Lemma 6.19 -/

/-- `p = 65521` (Lemma 6.19, `lem:d88comp`) is prime. -/
instance fact_prime_65521 : Fact (Nat.Prime 65521) := ⟨by norm_num⟩

/-- The masses `μ₀ = (1, 2, 3, 30)` of Lemma 6.19 (`lem:d88comp`), as integers (the base point of `Opt p μ₀`). -/
def μ0Z : Fin 4 → ℤ := ![1, 2, 3, 30]

/-! ## The local ring `O = ℤ[μ]_𝔪` -/

section Opt

variable (p : ℕ) [Fact p.Prime] {r : ℕ} (μ₀ : Fin r → ℤ)

/-- An element of `ℤ[μ]` outside `𝔪 = (p, μ − μ₀)` does not vanish at `μ₀`. -/
theorem eval_ne_zero_of_notMem_ptIdeal {s : MvPolynomial (Fin r) ℤ} (hs : s ∉ ptIdeal p μ₀) : eval μ₀ s ≠ 0 := by
  intro h
  apply hs
  rw [ptIdeal_eq_ker, RingHom.mem_ker, redPt, RingHom.comp_apply, h, map_zero]

/-- `ℤ[μ] → O` is injective (`ℤ[μ]` is a domain). -/
theorem algebraMap_Opt_injective : Function.Injective (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀)) :=
  IsLocalization.injective (M := (ptIdeal p μ₀).primeCompl) (S := Opt p μ₀)
    (Ideal.primeCompl_le_nonZeroDivisors (ptIdeal p μ₀))

/-- The residue map of `O` restricted to `ℤ[μ]` is `f ↦ f(μ₀) mod p`. -/
theorem resPt_comp_algebraMap :
    (resPt p μ₀).comp (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀)) = redPt p μ₀ :=
  RingHom.ext fun f => by
    rw [RingHom.comp_apply, resPt_algebraMap]
    rfl

/-- The evaluation of `O` at `μ₀`, restricted to `ℤ[μ]` and followed by `ℚ → ℂ`, is `f ↦ f(μ₀)`. -/
theorem evalPt_comp_algebraMap :
    ((Rat.castHom ℂ).comp (evalPt p μ₀)).comp (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀)) =
      (Int.castRingHom ℂ).comp (eval μ₀) :=
  RingHom.ext fun f => by simp [evalPt_algebraMap]

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- **Clearing the denominators of an integrality relation over `O = ℤ[μ]_𝔪`.** Let `S` be polynomials in
`v_1, …, v_N` over `ℤ[μ]` such that `O[v]/(S)` is integral over `O` (the conclusion of Lemma 6.18, `goodred`).
Then for every `j` there are `s ∈ ℤ[μ] \ 𝔪`, `d` and `α_k ∈ ℤ[μ]` with `s v_j^d + Σ_{k<d} α_k v_j^k ∈ (S)` in
`ℤ[μ][v]`. A monic relation `v_j^d + Σ_k f_k v_j^k = Σ_i c_i S_i` over `O` is multiplied by a common denominator
`s = s₁ s₂ ∉ 𝔪` of the `f_k` (in `O`) and of the `c_i` (in `O[v]`, the localization of `ℤ[μ][v]` at the image of
`ℤ[μ] \ 𝔪`, `MvPolynomial.isLocalization`), and the relation descends to `ℤ[μ][v]` since `ℤ[μ][v] → O[v]` is
injective. -/
theorem exists_rel_of_isIntegral_Opt {N n : ℕ} (S : Fin n → MvPolynomial (Fin N) (MvPolynomial (Fin r) ℤ))
    (hS : Algebra.IsIntegral (Opt p μ₀) (MvPolynomial (Fin N) (Opt p μ₀) ⧸
      Ideal.span (Set.range fun i => MvPolynomial.map (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀)) (S i))))
    (j : Fin N) :
    ∃ (s : MvPolynomial (Fin r) ℤ) (d : ℕ) (α : Fin d → MvPolynomial (Fin r) ℤ), s ∉ ptIdeal p μ₀ ∧
      C s * X j ^ d + ∑ k : Fin d, C (α k) * X j ^ (k : ℕ) ∈ Ideal.span (Set.range S) := by
  classical
  obtain ⟨f, hfm, hf⟩ := hS.isIntegral (Ideal.Quotient.mk (Ideal.span (Set.range fun i =>
    MvPolynomial.map (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀)) (S i))) (X j))
  -- the monic relation of `v_j` over `O`
  have hmem : Polynomial.aeval (X j : MvPolynomial (Fin N) (Opt p μ₀)) f ∈ Ideal.span (Set.range fun i =>
      MvPolynomial.map (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀)) (S i)) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk (Opt p μ₀),
      ← Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk (Opt p μ₀), Polynomial.aeval_def]
    exact hf
  have hexp : Polynomial.aeval (X j : MvPolynomial (Fin N) (Opt p μ₀)) f =
      X j ^ f.natDegree + ∑ k : Fin f.natDegree, C (f.coeff k) * X j ^ (k : ℕ) := by
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hfm.coeff_natDegree, one_smul, add_comm,
      Finset.sum_range]
    simp only [MvPolynomial.smul_eq_C_mul]
  rw [hexp] at hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  -- a common denominator of the coefficients `f_k` in `O`
  obtain ⟨b₁, hb₁⟩ := IsLocalization.exist_integer_multiples (ptIdeal p μ₀).primeCompl
    (Finset.univ : Finset (Fin f.natDegree)) fun k => f.coeff k
  choose α hα using fun k => RingHom.mem_rangeS.mp (hb₁ k (Finset.mem_univ k))
  -- a common denominator of the cofactors `c_i` in `O[v]`
  obtain ⟨b₂, hb₂⟩ := IsLocalization.exist_integer_multiples
    ((ptIdeal p μ₀).primeCompl.map
      (C : MvPolynomial (Fin r) ℤ →+* MvPolynomial (Fin N) (MvPolynomial (Fin r) ℤ)))
    (Finset.univ : Finset (Fin n)) c
  choose Q hQ using fun i => RingHom.mem_rangeS.mp (hb₂ i (Finset.mem_univ i))
  obtain ⟨s₂, hs₂, hb₂s⟩ := Submonoid.mem_map.mp b₂.2
  have hQ' : ∀ i, MvPolynomial.map (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀)) (Q i) =
      C (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀) s₂) * c i := fun i => by
    have h := hQ i
    rw [Algebra.smul_def, ← hb₂s] at h
    simpa only [MvPolynomial.algebraMap_def, MvPolynomial.map_C] using h
  have hα' : ∀ k, algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀) (α k) =
      algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀) (b₁ : MvPolynomial (Fin r) ℤ) * f.coeff k :=
    fun k => (hα k).trans (Algebra.smul_def _ _)
  -- the relation multiplied by `s₁ s₂`, mapped to `O[v]`
  have key : MvPolynomial.map (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀))
      (C ((b₁ : MvPolynomial (Fin r) ℤ) * s₂) * X j ^ f.natDegree +
        ∑ k : Fin f.natDegree, C (s₂ * α k) * X j ^ (k : ℕ)) =
      MvPolynomial.map (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀))
        (∑ i, C (b₁ : MvPolynomial (Fin r) ℤ) * Q i * S i) := by
    have e1 : MvPolynomial.map (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀))
        (∑ i, C (b₁ : MvPolynomial (Fin r) ℤ) * Q i * S i) =
        C (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀) (b₁ : MvPolynomial (Fin r) ℤ)) *
          C (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀) s₂) *
          (X j ^ f.natDegree + ∑ k : Fin f.natDegree, C (f.coeff k) * X j ^ (k : ℕ)) := by
      rw [← hc, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, MvPolynomial.map_C, hQ' i]
      ring
    rw [e1]
    simp only [map_add, map_sum, map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.map_X, hα']
    rw [mul_add, Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring
  have heq := MvPolynomial.map_injective (f := algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀))
    (algebraMap_Opt_injective p μ₀) key
  refine ⟨(b₁ : MvPolynomial (Fin r) ℤ) * s₂, f.natDegree, fun k => s₂ * α k,
    Ideal.mem_primeCompl_iff.mp ((ptIdeal p μ₀).primeCompl.mul_mem b₁.2 hs₂), ?_⟩
  rw [heq]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- **The point count of Theorem 6.20** for polynomials over `ℤ[μ]` (`encard_complexZeros_le`): if `O[v]/(S)` is
integral over `O` and `dim_{𝔽_p} 𝔽_p[v]/(S mod 𝔪) ≤ d`, where `S mod 𝔪` is `S` with its coefficients evaluated at
`μ₀` and reduced modulo `p`, then `S(μ₀)` has at most `d` zeros in `ℂ^N`. -/
theorem encard_zeros_le_of_isIntegral {N n : ℕ} (S : Fin n → MvPolynomial (Fin N) (MvPolynomial (Fin r) ℤ))
    (hS : Algebra.IsIntegral (Opt p μ₀) (MvPolynomial (Fin N) (Opt p μ₀) ⧸
      Ideal.span (Set.range fun i => MvPolynomial.map (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀)) (S i))))
    {d : ℕ} (hd : Module.finrank (ZMod p) (MvPolynomial (Fin N) (ZMod p) ⧸
      Ideal.span (Set.range fun i => MvPolynomial.map (redPt p μ₀) (S i))) ≤ d) :
    {z : Fin N → ℂ | ∀ i, eval z (MvPolynomial.map ((Int.castRingHom ℂ).comp (eval μ₀)) (S i)) = 0}.encard ≤
      d := by
  classical
  have hT : ((Finset.univ.image fun i => MvPolynomial.map (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀)) (S i) :
      Finset (MvPolynomial (Fin N) (Opt p μ₀))) : Set (MvPolynomial (Fin N) (Opt p μ₀))) =
      Set.range fun i => MvPolynomial.map (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀)) (S i) := by
    simp
  have himg : MvPolynomial.map (resPt p μ₀) '' ((Finset.univ.image fun i =>
      MvPolynomial.map (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀)) (S i) :
        Finset (MvPolynomial (Fin N) (Opt p μ₀))) : Set (MvPolynomial (Fin N) (Opt p μ₀))) =
      Set.range fun i => MvPolynomial.map (redPt p μ₀) (S i) := by
    rw [hT, ← Set.range_comp]
    congr 1
    funext i
    simp only [Function.comp_apply, MvPolynomial.map_map, resPt_comp_algebraMap]
  have h := encard_complexZeros_le p μ₀ (Finset.univ.image fun i =>
    MvPolynomial.map (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀)) (S i)) (by rw [hT]; exact hS) (d := d)
    (by rw [himg]; exact hd)
  have hset : {z : Fin N → ℂ | ∀ i, eval z (MvPolynomial.map ((Int.castRingHom ℂ).comp (eval μ₀)) (S i)) = 0} =
      {z : Fin N → ℂ | ∀ f ∈ (Finset.univ.image fun i =>
        MvPolynomial.map (algebraMap (MvPolynomial (Fin r) ℤ) (Opt p μ₀)) (S i) :
          Finset (MvPolynomial (Fin N) (Opt p μ₀))),
        eval z (MvPolynomial.map ((Rat.castHom ℂ).comp (evalPt p μ₀)) f) = 0} := by
    ext z
    simp only [Set.mem_ofPred_eq, Finset.forall_mem_image, Finset.mem_univ, true_implies, MvPolynomial.map_map,
      evalPt_comp_algebraMap]
  rw [hset]
  exact h

end Opt

/-! ## Elements integral over `A[1/g]` -/

section GInt

variable {A Q : Type*} [CommRing A] [CommRing Q] (φ : A →+* Q) (g : A)

/-- Division by a divisor of a power of `g` in `gInt φ g`: if `g^a = u h` and `φ(h) z ∈ gInt φ g`, then
`z ∈ gInt φ g`. -/
theorem mem_gInt_of_mul {h u : A} {a : ℕ} (hg : g ^ a = u * h) {z : Q} (hz : φ h * z ∈ gInt φ g) :
    z ∈ gInt φ g := by
  obtain ⟨b, hb⟩ := (mem_gInt φ g).mp hz
  refine (mem_gInt φ g).mpr ⟨b + a, ?_⟩
  have e : φ g ^ (b + a) * z = φ u * (φ g ^ b * (φ h * z)) := by
    rw [pow_add, ← map_pow φ g a, hg, map_mul]
    ring
  rw [e]
  exact φ.isIntegralElem_map.mul φ hb

/-- An element `y` with a relation `φ(s) y^d + Σ_{k<d} φ(c_k) y^k = 0`, `s ≠ 0`, lies in `gInt φ g` if `g^a = u s`:
`φ(s) y` is integral over `A` (`RingHom.isIntegralElem_leadingCoeff_mul`). -/
theorem mem_gInt_of_rel {s u : A} {a d : ℕ} (hs : s ≠ 0) (hg : g ^ a = u * s) (c : Fin d → A) {y : Q}
    (hy : φ s * y ^ d + ∑ k : Fin d, φ (c k) * y ^ (k : ℕ) = 0) : y ∈ gInt φ g := by
  classical
  let F : Polynomial A :=
    Polynomial.C s * Polynomial.X ^ d + ∑ k : Fin d, Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)
  have hev : F.eval₂ φ y = 0 := by
    simp only [F, Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X_pow]
    exact hy
  have hcoeff : F.coeff d = s := by
    have h0 : (∑ k : Fin d, Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)).coeff d = 0 := by
      rw [Polynomial.finsetSum_coeff]
      exact Finset.sum_eq_zero fun k _ => by rw [Polynomial.coeff_C_mul_X_pow, ite_eq_right (Nat.ne_of_gt k.isLt)]
    rw [show F.coeff d = (Polynomial.C s * Polynomial.X ^ d).coeff d +
        (∑ k : Fin d, Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)).coeff d from Polynomial.coeff_add _ _ _, h0,
      add_zero, Polynomial.coeff_C_mul_X_pow, ite_eq_left rfl]
  have hdeg : F.natDegree = d := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [hcoeff]; exact hs)
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_)
    exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans k.isLt.le
  have hlc : F.leadingCoeff = s := by rw [Polynomial.leadingCoeff, hdeg, hcoeff]
  have hint := φ.isIntegralElem_leadingCoeff_mul F y hev
  rw [hlc] at hint
  refine (mem_gInt φ g).mpr ⟨a, ?_⟩
  rw [← map_pow, hg, map_mul, mul_assoc]
  exact φ.isIntegralElem_map.mul φ hint

end GInt

/-! ## The binary -/

section Binary

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The leading coefficients `(ẑ₅, ẑ₆) = (m₆, −m₅)` of the binary `{5, 6}` with masses `mb = (m₅, m₆)`, with the
scale `c` of `ẑ₅ = c m₆`, `ẑ₆ = −c m₅` set to `1` (the proof of Lemma 6.17, `lem:Ttest`). -/
def zb (mb : Fin 2 → R) : Fin 2 → R := ![mb 1, -mb 0]

/-- **The cross relations** `p̂_jl² ẑ_j X_l = −1` of Lemma 6.16 (`lem:d88lead`), for `q_jl = p̂_jl X_l` and the
normalized `ẑ = zb mb`: `q_jl² ẑ_j + X_l = 0`, multiplied by `κ`, where `Xh = κ X` are the positions with the
denominator `κ` cleared. -/
def binEq {N : ℕ} (κ : R) (mb : Fin 2 → R) (q : Fin 2 → Fin N → R) (Xh : Fin N → R) (j : Fin 2) (l : Fin N) :
    R :=
  κ * zb mb j * q j l ^ 2 + Xh l

/-- **The torque relation** (6.1) of Lemma 6.16 (and (6.2) for `N = 3`), `Σ_{j,l} m_j m_l p̂_jl = 0`, for
`q_jl = p̂_jl X_l` and multiplied by `Π_l Xh_l`: `Σ_l μ_l (Σ_j m_j q_jl) Π_{l'≠l} Xh_l'`. -/
def torqEq {N : ℕ} (μ : Fin N → R) (mb : Fin 2 → R) (q : Fin 2 → Fin N → R) (Xh : Fin N → R) : R :=
  ∑ l, μ l * (∑ j, mb j * q j l) * ∏ l' ∈ univ.erase l, Xh l'

variable {F : Type*} [FunLike F R S] [RingHomClass F R S]

theorem map_zb (f : F) (mb : Fin 2 → R) (j : Fin 2) : f (zb mb j) = zb (fun j => f (mb j)) j := by
  fin_cases j <;> simp [zb]

theorem map_binEq {N : ℕ} (f : F) (κ : R) (mb : Fin 2 → R) (q : Fin 2 → Fin N → R) (Xh : Fin N → R) (j : Fin 2)
    (l : Fin N) :
    f (binEq κ mb q Xh j l) = binEq (f κ) (fun j => f (mb j)) (fun j l => f (q j l)) (fun l => f (Xh l)) j l := by
  simp only [binEq, map_add, map_mul, map_pow, map_zb]

theorem map_torqEq {N : ℕ} (f : F) (μ : Fin N → R) (mb : Fin 2 → R) (q : Fin 2 → Fin N → R) (Xh : Fin N → R) :
    f (torqEq μ mb q Xh) = torqEq (fun l => f (μ l)) (fun j => f (mb j)) (fun j l => f (q j l)) (fun l => f (Xh l)) := by
  simp only [torqEq, map_sum, map_mul, map_prod]

/-- `torqEq` recovers the torque sum: if `Xh_l = a X_l` and `q_jl = b P_jl X_l`, then
`torqEq = b a^{N−1} (Π_l X_l) Σ_{j,l} m_j μ_l P_jl`. -/
theorem torqEq_eq {N : ℕ} (μ : Fin N → R) (mb : Fin 2 → R) {q P : Fin 2 → Fin N → R} {X Xh : Fin N → R} {a b : R}
    (hXh : ∀ l, Xh l = a * X l) (hq : ∀ j l, q j l = b * P j l * X l) :
    torqEq μ mb q Xh = b * a ^ (N - 1) * (∏ l, X l) * ∑ j, ∑ l, mb j * μ l * P j l := by
  classical
  have hprod : ∀ l, ∏ l' ∈ univ.erase l, Xh l' = a ^ (N - 1) * ∏ l' ∈ univ.erase l, X l' := fun l => by
    rw [Finset.prod_congr rfl fun l' _ => hXh l', Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin]
  have hterm : ∀ l, μ l * (∑ j, mb j * q j l) * ∏ l' ∈ univ.erase l, Xh l' =
      b * a ^ (N - 1) * (∏ l, X l) * ∑ j, mb j * μ l * P j l := fun l => by
    rw [hprod l, ← Finset.mul_prod_erase univ X (Finset.mem_univ l)]
    simp only [hq, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [torqEq, Finset.sum_congr rfl fun l _ => hterm l, ← Finset.mul_sum, Finset.sum_comm]

end Binary

end

end CC6Full.Six
