import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Field.ZMod
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Set.Card

/-!
# Counting complex zeros by a dimension over `𝔽_p`

In the proof of Theorem 6.20 of the paper, the coordinate ring of a system over the local ring
`O = ℤ[μ]_𝔪`, `𝔪 = (p, μ - μ₀)`, is a finite `O`-module (Lemma 6.18, `CC6Full.goodred`), and
"by Nakayama's lemma" the system has at most `dim_{𝔽_p} 𝔽_p[v] ⧸ ⟨S(μ₀) mod p⟩` complex zeros at
`μ₀`. This file proves that step.

## Main statements

* `encard_zeros_le_finrank`: let `O` be a local ring, `π : O → k` a surjective ring homomorphism
  onto a field, `ε : O → L` any ring homomorphism to a field, and `S` a set of polynomials in
  `O[v] = MvPolynomial (Fin N) O` such that `O[v] ⧸ ⟨S⟩` is integral over `O`. Then the zeros in
  `L^N` of the polynomials of `S` with coefficients mapped through `ε` are at most
  `dim_k k[v] ⧸ ⟨π(S)⟩` (counted with `Set.encard`, which is `⊤` on infinite sets, so the bound
  includes finiteness). No compatibility between `π` and `ε` is needed.
* `encard_complexZeros_le` (the statement used in the paper): for a prime `p`, `μ₀ ∈ ℤ^r`,
  `O = Opt p μ₀ = ℤ[μ]_𝔪` with `𝔪 = ptIdeal p μ₀ = (p, μ_1 - μ₀_1, …, μ_r - μ₀_r)`, and a finite
  set `S` of polynomials over `O` with `O[v] ⧸ ⟨S⟩` integral over `O`: if
  `dim_{𝔽_p} 𝔽_p[v] ⧸ ⟨S mod 𝔪⟩ ≤ d`, then the set of zeros in `ℂ^N` of `S` specialized at `μ₀`
  (coefficients mapped through `evalPt p μ₀ : O → ℚ` and `ℚ → ℂ`) has at most `d` elements.
  `ncard_complexZeros_le` states this as `Set.Finite` and `Set.ncard ≤ d`, and
  `encard_complexZeros_le_of_span` takes a finite set of polynomials over `𝔽_p` whose images span
  the quotient modulo `𝔪` (for example the standard monomials of a Gröbner basis) instead of the
  dimension. `encard_zeros_le_of_span_residue` is the general form of the latter.

The reduction `resPt p μ₀ : O → 𝔽_p` is the residue map of `O` (`ker_resPt`); it and `evalPt p μ₀`
are characterized on `ℤ[μ]` by `resPt_algebraMap` and `evalPt_algebraMap` (evaluation at `μ₀`,
followed by reduction modulo `p`, respectively by `ℤ → ℚ`). `ptIdeal_eq_ker` identifies `𝔪` with
the kernel of `f ↦ f(μ₀) mod p`, which shows that it is maximal.

## Proof

* `span_eq_top_of_span_residue` (Nakayama): `A = O[v] ⧸ ⟨S⟩` is a finite `O`-module, and the
  surjection `A → k[v] ⧸ ⟨π(S)⟩` induced by `π` has kernel `𝔪A`, since the kernel of
  `O[v] → k[v] ⧸ ⟨π(S)⟩` is `⟨S⟩ + 𝔪[v]`. So polynomials whose reductions span `k[v] ⧸ ⟨π(S)⟩`
  over `k` span `A` modulo `𝔪A`, hence span `A` over `O` by Nakayama's lemma.
* `encard_ringHom_le` (Dedekind): if `b_1, …, b_n` span an `O`-algebra `A` over `O`, at most `n`
  ring homomorphisms `A → L` restrict to `ε` on `O`. Distinct such homomorphisms are linearly
  independent over `L` as functions `A → L`, by Dedekind's lemma on characters, and each is
  determined, through a fixed `L`-linear map `L^n → (A → L)`, by its values at the `b_i`; so the
  vectors of these values are linearly independent in `L^n`.
* `encard_zeros_le_of_span`: a zero `z ∈ L^N` of `S` specialized through `ε` gives the ring
  homomorphism `A → L`, `v ↦ z`, extending `ε`, and `z` is recovered from it.
* `encard_zeros_le_finrank`: `k[v] ⧸ ⟨π(S)⟩` is integral over `k`, hence finite-dimensional; the
  lifts of a basis span `A`.

The route through `ℤ_(p)` and `ℚ[v] ⧸ ⟨S(μ₀)⟩` sketched in the paper is not needed: the count of
homomorphisms is bounded by the number of generators of `A` over `O` directly.
-/

namespace CC6Full

open MvPolynomial

noncomputable section

/-! ### Ring homomorphisms out of a finitely generated module -/

section Count

variable {O A L : Type*} [CommRing O] [CommRing A] [Algebra O A] [Field L]

/-- **Dedekind's lemma, counting form.** Let `A` be an `O`-algebra spanned over `O` by a finite
family `b : ι → A`, and `ε : O → L` a ring homomorphism to a field. At most `Fintype.card ι` ring
homomorphisms `A → L` restrict to `ε` on `O`. -/
theorem encard_ringHom_le {ι : Type*} [Fintype ι] (ε : O →+* L) (b : ι → A)
    (hb : Submodule.span O (Set.range b) = ⊤) :
    {f : A →+* L | f.comp (algebraMap O A) = ε}.encard ≤ Fintype.card ι := by
  classical
  set F := {f : A →+* L | f.comp (algebraMap O A) = ε}
  have hc : ∀ a : A, ∃ c : ι → O, ∑ i, c i • b i = a := fun a =>
    (Submodule.mem_span_range_iff_exists_fun O).1 (hb ▸ Submodule.mem_top)
  choose c hc using hc
  -- `g u` is the function `a ↦ ∑ i, ε (c a i) * u i`; it recovers `f` from the `f (b i)`.
  let g : (ι → L) →ₗ[L] (A → L) :=
    { toFun := fun u a => ∑ i, ε (c a i) * u i
      map_add' := fun u w => by
        funext a
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun t u => by
        funext a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring }
  let v : F → ι → L := fun f i => (f.1 : A →+* L) (b i)
  have hgv : g ∘ v = (fun f : A →* L => (f : A → L)) ∘ fun f : F => (f.1 : A →* L) := by
    funext f a
    obtain ⟨f, hf⟩ := f
    change ∑ i, ε (c a i) * f (b i) = f a
    conv_rhs => rw [← hc a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, ← RingHom.comp_apply f (algebraMap O A), hf]
  have hv : LinearIndependent L v := by
    refine LinearIndependent.of_comp g ?_
    rw [hgv]
    refine (linearIndependent_monoidHom A L).comp _ fun f₁ f₂ h => ?_
    exact Subtype.ext (RingHom.ext fun a => DFunLike.congr_fun h a)
  have h := hv.cardinalMk_le_finrank
  rw [Module.finrank_pi] at h
  exact Cardinal.toENat_le_natCast.2 h

/-- The zeros in `L^N` of a set `S` of polynomials over `O`, with coefficients mapped through
`ε : O → L`, are at most as many as the members of a family spanning `O[v] ⧸ ⟨S⟩` over `O`. -/
theorem encard_zeros_le_of_span {N : ℕ} {ι : Type*} [Fintype ι] (ε : O →+* L)
    (S : Set (MvPolynomial (Fin N) O)) (b : ι → MvPolynomial (Fin N) O ⧸ Ideal.span S)
    (hb : Submodule.span O (Set.range b) = ⊤) :
    {z : Fin N → L | ∀ f ∈ S, eval z (MvPolynomial.map ε f) = 0}.encard ≤ Fintype.card ι := by
  set Z := {z : Fin N → L | ∀ f ∈ S, eval z (MvPolynomial.map ε f) = 0}
  have hle : ∀ z ∈ Z, ∀ a ∈ Ideal.span S, eval₂Hom ε z a = 0 := fun z hz a ha => by
    have h : Ideal.span S ≤ RingHom.ker (eval₂Hom ε z) := Ideal.span_le.2 fun f hf => by
      rw [SetLike.mem_coe, RingHom.mem_ker, coe_eval₂Hom, ← eval_map]
      exact hz f hf
    exact RingHom.mem_ker.1 (h ha)
  let φ : Z → {f : (MvPolynomial (Fin N) O ⧸ Ideal.span S) →+* L |
      f.comp (algebraMap O _) = ε} := fun z =>
    ⟨Ideal.Quotient.lift (Ideal.span S) (eval₂Hom ε z.1) (hle z.1 z.2), RingHom.ext fun a => by
      change Ideal.Quotient.lift (Ideal.span S) (eval₂Hom ε z.1) (hle z.1 z.2)
        (Ideal.Quotient.mk (Ideal.span S) (C a)) = ε a
      rw [Ideal.Quotient.lift_mk, coe_eval₂Hom, eval₂_C]⟩
  have hφ : Function.Injective φ := by
    intro z₁ z₂ h
    apply Subtype.ext
    funext j
    have := congrArg (fun f => (f.1 : _ →+* L) (Ideal.Quotient.mk (Ideal.span S) (X j))) h
    simpa [φ] using this
  calc Z.encard = ENat.card Z := rfl
    _ ≤ ENat.card _ := ENat.card_le_card_of_injective hφ
    _ ≤ Fintype.card ι := encard_ringHom_le ε b hb

end Count

/-! ### Nakayama's lemma for a coordinate ring over a local ring -/

section Nakayama

variable {O k : Type*} [CommRing O] [IsLocalRing O] [Field k] {N : ℕ}

/-- Let `π : O → k` be a surjection from a local ring onto a field and `S` a set of polynomials
over `O` with `A = O[v] ⧸ ⟨S⟩` a finite `O`-module. If the reductions of polynomials `b i` span
`k[v] ⧸ ⟨π(S)⟩` over `k`, then the `b i` span `A` over `O`. -/
theorem span_eq_top_of_span_residue (π : O →+* k) (hπ : Function.Surjective π)
    (S : Set (MvPolynomial (Fin N) O)) [Module.Finite O (MvPolynomial (Fin N) O ⧸ Ideal.span S)]
    {ι : Type*} [Fintype ι] (b : ι → MvPolynomial (Fin N) O)
    (hb : Submodule.span k (Set.range fun i =>
      Ideal.Quotient.mk (Ideal.span (MvPolynomial.map π '' S)) (MvPolynomial.map π (b i))) = ⊤) :
    Submodule.span O (Set.range fun i => Ideal.Quotient.mk (Ideal.span S) (b i)) = ⊤ := by
  set I := Ideal.span S
  set J := Ideal.span (MvPolynomial.map π '' S)
  have hJ : J = Ideal.map (MvPolynomial.map π) I := by rw [Ideal.map_span]
  have hker : RingHom.ker π = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π hπ)
  refine top_unique (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_)
  rintro x -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1
    (hb ▸ Submodule.mem_top : Ideal.Quotient.mk J (MvPolynomial.map π f) ∈ _)
  choose o ho using fun i => hπ (c i)
  -- `f - ∑ i, o i * b i` reduces into `⟨π(S)⟩`
  have hg : MvPolynomial.map π (f - ∑ i, C (o i) * b i) ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have e : ∀ i, Ideal.Quotient.mk J (MvPolynomial.map π (C (o i) * b i)) =
        c i • Ideal.Quotient.mk J (MvPolynomial.map π (b i)) := fun i => by
      rw [map_mul, map_C, ho i, map_mul]
      exact (Algebra.smul_def (c i) (Ideal.Quotient.mk J (MvPolynomial.map π (b i)))).symm
    simp only [map_sub, map_sum, e, hc, sub_self]
  -- hence lies in `⟨S⟩ + 𝔪[v]`
  have hg' : f - ∑ i, C (o i) * b i ∈ I ⊔ Ideal.map C (RingHom.ker π) := by
    have h1 : f - ∑ i, C (o i) * b i ∈
        Ideal.comap (MvPolynomial.map π) (Ideal.map (MvPolynomial.map π) I) := by
      rw [← hJ]; exact hg
    rwa [Ideal.comap_map_of_surjective _ (map_surjective π hπ),
      show Ideal.comap (MvPolynomial.map π) ⊥ =
        RingHom.ker (MvPolynomial.map π : MvPolynomial (Fin N) O →+* _) from rfl,
      MvPolynomial.ker_map] at h1
  obtain ⟨g₁, hg₁, g₂, hg₂, hg12⟩ := Submodule.mem_sup.1 hg'
  have hfx : Ideal.Quotient.mk I f =
      ∑ i, o i • Ideal.Quotient.mk I (b i) + Ideal.Quotient.mk I g₂ := by
    have e1 : f = ∑ i, C (o i) * b i + g₁ + g₂ := by
      rw [add_assoc, hg12]; ring
    have e2 : Ideal.Quotient.mk I g₁ = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hg₁
    rw [e1, map_add, map_add, e2, add_zero, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    exact (Algebra.smul_def (o i) (Ideal.Quotient.mk I (b i))).symm
  rw [hfx]
  refine Submodule.add_mem_sup (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) ?_
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← hker]
  have e3 : Ideal.map (algebraMap O (MvPolynomial (Fin N) O ⧸ I)) (RingHom.ker π) =
      Ideal.map (Ideal.Quotient.mk I) (Ideal.map C (RingHom.ker π)) := by
    rw [Ideal.map_map]; rfl
  rw [e3]
  exact Ideal.mem_map_of_mem _ hg₂

/-- **Counting zeros by a spanning family of the special fibre.** Let `O` be a local ring,
`π : O → k` a surjection onto a field, `ε : O → L` a ring homomorphism to a field, and `S` a set
of polynomials over `O` with `O[v] ⧸ ⟨S⟩` integral over `O`. If `t_1, …, t_n` span
`k[v] ⧸ ⟨π(S)⟩` over `k`, then the zeros in `L^N` of `S` with coefficients mapped through `ε` are
at most `n`. -/
theorem encard_zeros_le_of_span_residue {L : Type*} [Field L] (π : O →+* k)
    (hπ : Function.Surjective π) (ε : O →+* L) (S : Set (MvPolynomial (Fin N) O))
    (hS : Algebra.IsIntegral O (MvPolynomial (Fin N) O ⧸ Ideal.span S))
    {ι : Type*} [Fintype ι] (t : ι → MvPolynomial (Fin N) k)
    (ht : Submodule.span k (Set.range fun i =>
      Ideal.Quotient.mk (Ideal.span (MvPolynomial.map π '' S)) (t i)) = ⊤) :
    {z : Fin N → L | ∀ f ∈ S, eval z (MvPolynomial.map ε f) = 0}.encard ≤ Fintype.card ι := by
  have : Algebra.FiniteType O (MvPolynomial (Fin N) O ⧸ Ideal.span S) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O _) (Ideal.Quotient.mkₐ_surjective O _)
  have : Module.Finite O (MvPolynomial (Fin N) O ⧸ Ideal.span S) := Algebra.IsIntegral.finite
  choose q hq using fun i => map_surjective π hπ (t i)
  exact encard_zeros_le_of_span ε S _
    (span_eq_top_of_span_residue π hπ S q (by simp only [hq]; exact ht))

/-- **Counting zeros by the special fibre.** Let `O` be a local ring, `π : O → k` a surjection
onto a field, `ε : O → L` a ring homomorphism to a field, and `S` a set of polynomials over `O`
with `O[v] ⧸ ⟨S⟩` integral over `O`. Then the zeros in `L^N` of `S` with coefficients mapped
through `ε` are at most `dim_k k[v] ⧸ ⟨π(S)⟩`. -/
theorem encard_zeros_le_finrank {L : Type*} [Field L] (π : O →+* k) (hπ : Function.Surjective π)
    (ε : O →+* L) (S : Set (MvPolynomial (Fin N) O))
    (hS : Algebra.IsIntegral O (MvPolynomial (Fin N) O ⧸ Ideal.span S)) :
    {z : Fin N → L | ∀ f ∈ S, eval z (MvPolynomial.map ε f) = 0}.encard ≤
      Module.finrank k (MvPolynomial (Fin N) k ⧸ Ideal.span (MvPolynomial.map π '' S)) := by
  have hIJ : Ideal.span S ≤ (Ideal.span (MvPolynomial.map π '' S)).comap (MvPolynomial.map π) :=
    Ideal.span_le.2 fun f hf => Ideal.subset_span ⟨f, hf, rfl⟩
  let Φ := Ideal.quotientMap (Ideal.span (MvPolynomial.map π '' S)) (MvPolynomial.map π) hIJ
  have hΦ : Function.Surjective Φ := Ideal.quotientMap_surjective (map_surjective π hπ)
  have hcomp : (algebraMap k (MvPolynomial (Fin N) k ⧸ Ideal.span (MvPolynomial.map π '' S))).comp
      π = Φ.comp (algebraMap O (MvPolynomial (Fin N) O ⧸ Ideal.span S)) := by
    refine RingHom.ext fun a => ?_
    change Ideal.Quotient.mk (Ideal.span (MvPolynomial.map π '' S)) (C (π a)) =
      Ideal.Quotient.mk (Ideal.span (MvPolynomial.map π '' S)) (MvPolynomial.map π (C a))
    rw [map_C]
  have : Algebra.IsIntegral k (MvPolynomial (Fin N) k ⧸ Ideal.span (MvPolynomial.map π '' S)) :=
    ⟨fun x => by
      obtain ⟨a, rfl⟩ := hΦ x
      exact IsIntegral.map_of_comp_eq π Φ hcomp (Algebra.IsIntegral.isIntegral a)⟩
  have : Algebra.FiniteType k (MvPolynomial (Fin N) k ⧸ Ideal.span (MvPolynomial.map π '' S)) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ_surjective k _)
  have : Module.Finite k (MvPolynomial (Fin N) k ⧸ Ideal.span (MvPolynomial.map π '' S)) :=
    Algebra.IsIntegral.finite
  let B := Module.finBasis k (MvPolynomial (Fin N) k ⧸ Ideal.span (MvPolynomial.map π '' S))
  choose t ht using fun i => Ideal.Quotient.mk_surjective (B i)
  simpa using encard_zeros_le_of_span_residue π hπ ε S hS t (by simp only [ht]; exact B.span_eq)

end Nakayama

/-! ### The local ring `ℤ[μ]_𝔪` -/

section Point

variable (p : ℕ) [Fact p.Prime] {r : ℕ} (μ₀ : Fin r → ℤ)

/-- The ideal `𝔪 = (p, μ_1 - μ₀_1, …, μ_r - μ₀_r)` of `ℤ[μ]` (maximal: `ptIdeal_isMaximal`). -/
def ptIdeal : Ideal (MvPolynomial (Fin r) ℤ) :=
  Ideal.span (insert (C (p : ℤ)) (Set.range fun i => X i - C (μ₀ i)))

/-- Evaluation at `μ₀` followed by reduction modulo `p`, `ℤ[μ] → 𝔽_p`. -/
def redPt : MvPolynomial (Fin r) ℤ →+* ZMod p :=
  (Int.castRingHom (ZMod p)).comp (eval μ₀)

theorem redPt_surjective : Function.Surjective (redPt p μ₀) := fun x => by
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
  exact ⟨C m, by simp [redPt]⟩

omit [Fact p.Prime] in
/-- Every polynomial is congruent to its value at `μ₀` modulo the `μ_i - μ₀_i`. -/
theorem sub_C_eval_mem_span (f : MvPolynomial (Fin r) ℤ) :
    f - C (eval μ₀ f) ∈ Ideal.span (Set.range fun i => X i - C (μ₀ i)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg =>
    have e : f + g - C (eval μ₀ (f + g)) = (f - C (eval μ₀ f)) + (g - C (eval μ₀ g)) := by
      rw [map_add, C_add]; ring
    rw [e]
    exact add_mem hf hg
  | mul_X f i hf =>
    have e : f * X i - C (eval μ₀ (f * X i)) =
        (f - C (eval μ₀ f)) * X i + C (eval μ₀ f) * (X i - C (μ₀ i)) := by
      rw [map_mul, eval_X, C_mul]; ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

/-- `𝔪` is the kernel of `f ↦ f(μ₀) mod p`. -/
theorem ptIdeal_eq_ker : ptIdeal p μ₀ = RingHom.ker (redPt p μ₀) := by
  apply le_antisymm
  · rw [ptIdeal, Ideal.span_le]
    rintro f (rfl | ⟨i, rfl⟩)
    · simp [redPt]
    · simp [redPt]
  · intro f hf
    rw [RingHom.mem_ker, redPt, RingHom.comp_apply, eq_intCast,
      ZMod.intCast_zmod_eq_zero_iff_dvd] at hf
    obtain ⟨m, hm⟩ := hf
    have h1 : f - C (eval μ₀ f) ∈ ptIdeal p μ₀ :=
      Ideal.span_mono (Set.subset_insert _ _) (sub_C_eval_mem_span μ₀ f)
    have h2 : C (eval μ₀ f) ∈ ptIdeal p μ₀ := by
      rw [hm, C_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
    simpa using add_mem h1 h2

instance ptIdeal_isMaximal : (ptIdeal p μ₀).IsMaximal := by
  rw [ptIdeal_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _ (redPt_surjective p μ₀)

/-- The local ring `O = ℤ[μ]_𝔪`, `𝔪 = (p, μ - μ₀)`. (A `def` with the instances below rather
than an `abbrev`: with an `abbrev`, instance search fails for the quotients
`MvPolynomial (Fin N) O ⧸ I`.) -/
def Opt : Type := Localization.AtPrime (ptIdeal p μ₀)

instance : CommRing (Opt p μ₀) := inferInstanceAs (CommRing (Localization.AtPrime (ptIdeal p μ₀)))

instance : Algebra (MvPolynomial (Fin r) ℤ) (Opt p μ₀) :=
  inferInstanceAs (Algebra (MvPolynomial (Fin r) ℤ) (Localization.AtPrime (ptIdeal p μ₀)))

instance : IsLocalization.AtPrime (Opt p μ₀) (ptIdeal p μ₀) :=
  inferInstanceAs (IsLocalization.AtPrime (Localization.AtPrime (ptIdeal p μ₀)) (ptIdeal p μ₀))

instance : IsLocalRing (Opt p μ₀) := IsLocalization.AtPrime.isLocalRing (Opt p μ₀) (ptIdeal p μ₀)

instance : IsNoetherianRing (Opt p μ₀) :=
  IsLocalization.isNoetherianRing (ptIdeal p μ₀).primeCompl (Opt p μ₀) inferInstance

/-- The residue map `O → O ⧸ 𝔪 ≅ 𝔽_p`: `μ ↦ μ₀ mod p` (`resPt_algebraMap`). -/
def resPt : Opt p μ₀ →+* ZMod p :=
  IsLocalization.lift (M := (ptIdeal p μ₀).primeCompl) (g := redPt p μ₀) fun y =>
    isUnit_iff_ne_zero.2 fun h =>
      Ideal.mem_primeCompl_iff.1 y.2 ((ptIdeal_eq_ker p μ₀).ge (RingHom.mem_ker.2 h))

theorem resPt_algebraMap (f : MvPolynomial (Fin r) ℤ) :
    resPt p μ₀ (algebraMap _ (Opt p μ₀) f) = ((eval μ₀ f : ℤ) : ZMod p) :=
  IsLocalization.lift_eq _ f

theorem resPt_surjective : Function.Surjective (resPt p μ₀) := fun x => by
  obtain ⟨f, rfl⟩ := redPt_surjective p μ₀ x
  exact ⟨algebraMap _ _ f, IsLocalization.lift_eq _ f⟩

/-- `resPt` is the reduction modulo the maximal ideal of `O`. -/
theorem ker_resPt : RingHom.ker (resPt p μ₀) = IsLocalRing.maximalIdeal (Opt p μ₀) :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (resPt_surjective p μ₀))

/-- Evaluation at `μ₀`, `O → ℚ` (`evalPt_algebraMap`): it is defined on `O` since a denominator
`s ∉ 𝔪` has `s(μ₀) ≢ 0 mod p`, in particular `s(μ₀) ≠ 0`. -/
def evalPt : Opt p μ₀ →+* ℚ :=
  IsLocalization.lift (M := (ptIdeal p μ₀).primeCompl) (g := (Int.castRingHom ℚ).comp (eval μ₀))
    fun y => isUnit_iff_ne_zero.2 fun h => Ideal.mem_primeCompl_iff.1 y.2 <|
      (ptIdeal_eq_ker p μ₀).ge <| RingHom.mem_ker.2 <| by
        rw [RingHom.comp_apply, eq_intCast, Int.cast_eq_zero] at h
        rw [redPt, RingHom.comp_apply, h, map_zero]

theorem evalPt_algebraMap (f : MvPolynomial (Fin r) ℤ) :
    evalPt p μ₀ (algebraMap _ (Opt p μ₀) f) = ((eval μ₀ f : ℤ) : ℚ) :=
  IsLocalization.lift_eq _ f

variable {N : ℕ}

/-- **The point count of Theorem 6.20.** Let `p` be a prime, `μ₀ ∈ ℤ^r`, `O = ℤ[μ]_𝔪` with
`𝔪 = (p, μ - μ₀)`, and `S` a finite set of polynomials in `v_1, …, v_N` over `O` such that
`O[v] ⧸ ⟨S⟩` is integral over `O` (as given by `CC6Full.goodred`). If
`dim_{𝔽_p} 𝔽_p[v] ⧸ ⟨S mod 𝔪⟩ ≤ d`, then `S`, specialized at `μ₀` through `O → ℚ → ℂ`, has at
most `d` zeros in `ℂ^N`. -/
theorem encard_complexZeros_le (S : Finset (MvPolynomial (Fin N) (Opt p μ₀)))
    (hS : Algebra.IsIntegral (Opt p μ₀)
      (MvPolynomial (Fin N) (Opt p μ₀) ⧸ Ideal.span (S : Set (MvPolynomial (Fin N) (Opt p μ₀)))))
    {d : ℕ} (hd : Module.finrank (ZMod p) (MvPolynomial (Fin N) (ZMod p) ⧸
      Ideal.span (MvPolynomial.map (resPt p μ₀) '' (S : Set (MvPolynomial (Fin N) (Opt p μ₀)))))
      ≤ d) :
    {z : Fin N → ℂ | ∀ f ∈ S,
      eval z (MvPolynomial.map ((Rat.castHom ℂ).comp (evalPt p μ₀)) f) = 0}.encard ≤ d := by
  have h := encard_zeros_le_finrank (resPt p μ₀) (resPt_surjective p μ₀)
    ((Rat.castHom ℂ).comp (evalPt p μ₀)) (S : Set (MvPolynomial (Fin N) (Opt p μ₀))) hS
  simp only [Finset.mem_coe] at h
  exact h.trans (by exact_mod_cast hd)

/-- `encard_complexZeros_le`, with `Set.Finite` and `Set.ncard`. -/
theorem ncard_complexZeros_le (S : Finset (MvPolynomial (Fin N) (Opt p μ₀)))
    (hS : Algebra.IsIntegral (Opt p μ₀)
      (MvPolynomial (Fin N) (Opt p μ₀) ⧸ Ideal.span (S : Set (MvPolynomial (Fin N) (Opt p μ₀)))))
    {d : ℕ} (hd : Module.finrank (ZMod p) (MvPolynomial (Fin N) (ZMod p) ⧸
      Ideal.span (MvPolynomial.map (resPt p μ₀) '' (S : Set (MvPolynomial (Fin N) (Opt p μ₀)))))
      ≤ d) :
    {z : Fin N → ℂ | ∀ f ∈ S,
        eval z (MvPolynomial.map ((Rat.castHom ℂ).comp (evalPt p μ₀)) f) = 0}.Finite ∧
      {z : Fin N → ℂ | ∀ f ∈ S,
        eval z (MvPolynomial.map ((Rat.castHom ℂ).comp (evalPt p μ₀)) f) = 0}.ncard ≤ d :=
  Set.encard_le_coe_iff_finite_ncard_le.1 (encard_complexZeros_le p μ₀ S hS hd)

/-- `encard_complexZeros_le` with a finite set `T` of polynomials over `𝔽_p` whose images span
`𝔽_p[v] ⧸ ⟨S mod 𝔪⟩` over `𝔽_p` (for example the standard monomials of a Gröbner basis) in place
of the dimension: at most `#T` complex zeros. -/
theorem encard_complexZeros_le_of_span (S : Finset (MvPolynomial (Fin N) (Opt p μ₀)))
    (hS : Algebra.IsIntegral (Opt p μ₀)
      (MvPolynomial (Fin N) (Opt p μ₀) ⧸ Ideal.span (S : Set (MvPolynomial (Fin N) (Opt p μ₀)))))
    (T : Finset (MvPolynomial (Fin N) (ZMod p)))
    (hT : Submodule.span (ZMod p) (Ideal.Quotient.mk (Ideal.span
      (MvPolynomial.map (resPt p μ₀) '' (S : Set (MvPolynomial (Fin N) (Opt p μ₀))))) '' T) = ⊤) :
    {z : Fin N → ℂ | ∀ f ∈ S,
      eval z (MvPolynomial.map ((Rat.castHom ℂ).comp (evalPt p μ₀)) f) = 0}.encard ≤ T.card := by
  have h := encard_zeros_le_of_span_residue (resPt p μ₀) (resPt_surjective p μ₀)
    ((Rat.castHom ℂ).comp (evalPt p μ₀)) (S : Set (MvPolynomial (Fin N) (Opt p μ₀))) hS
    (fun x : (T : Set (MvPolynomial (Fin N) (ZMod p))) => x.1)
    (by rw [← hT]; exact congrArg _ (Set.image_eq_range _ _).symm)
  simp only [Finset.mem_coe, Finset.coe_sort_coe, Fintype.card_coe] at h
  exact h

end Point

end

end CC6Full
