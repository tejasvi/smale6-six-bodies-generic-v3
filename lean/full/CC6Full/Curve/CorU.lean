import CC6Full.Curve.Algebra
import CC6Full.Curve.Fibre

/-!
# Corollary 2.4: infinitely many central configurations give a nontrivial curve

Corollary 2.4 (`cor:curve`), in the form of the five-body proof of [Tom26, Corollary 2.5]:

> Let `m ∈ (ℝ_{>0})^{n+2}`. If the planar `(n+2)`-body problem with masses `m` has infinitely many central
> configurations up to similarity, then `Y_m` contains an irreducible curve `C` on which `U` does not vanish
> identically and some `r²_kl` is not constant.

`exists_curve`. The set `T = Y_m ∩ {U ≠ 0}` is infinite (`finitelyManyCC_of_finite`, which rests on Lemma 2.1
(`lem:slice`) and [Tom26, Lemma 2.1]). So some non-maximal prime `P` containing the ideal of `Y_m` misses `U`
(`exists_prime_of_infinite`), and some prime `Q ⊇ P` of dimension one misses `U` (`exists_curve_ideal`): an
irreducible curve `C ⊆ Y_m` with `U ∉ I(C)`. If every `r²_kl` were constant on `C`, the zero set of `I(C)` would
lie in a fibre of `(r²_kl)_{k,l}` on `Y_m`, which is finite since `Σ_k m_k > 0` (`r2_fibre_finite`), whereas a
prime of dimension one has infinitely many zeros (`zeroLocus_infinite_of_ringKrullDim_eq_one`). So `C` is
nontrivial.

The curve is found inside `{U ≠ 0}`, so the constancy of `U` on curves (Lemma 2.3 (`lem:U`) (b)) is not used; it
gives the paper's form (`U` a nonzero constant on `C`) separately.
-/

namespace CC6Full

open Finset MvPolynomial

variable {n : ℕ}

/-- **Corollary 2.4** (`cor:curve`). If positive masses `m` have infinitely many central configurations up to
similarity, then `Y_m` contains a nontrivial irreducible curve. -/
theorem exists_curve {m : Fin (n + 2) → ℝ} (hm : ∀ i, 0 < m i) (h : ¬ FinitelyManyCC m) :
    ∃ C : Curve n m, C.Nontrivial := by
  have hT : {y : Coord (n + 2) → ℂ | y ∈ Ym m ∧ eval y (Upoly m) ≠ 0}.Infinite := fun hfin =>
    h (finitelyManyCC_of_finite hm hfin)
  obtain ⟨P, hP, hYP, hUP, hPmax⟩ := exists_prime_of_infinite (I := idealY m) (g := Upoly m)
    (fun y hy f hf => eval_eq_zero_of_mem_idealY hf hy.1) hT (fun y hy => hy.2)
  obtain ⟨Q, hQ, hPQ, hUQ, hdim⟩ := exists_curve_ideal hPmax hUP
  refine ⟨⟨⟨Q, hQ, hdim⟩, hYP.trans hPQ⟩, hUQ, ?_⟩
  by_contra hconst
  push Not at hconst
  choose c hc using hconst
  have hM : ∑ i, m i ≠ 0 := (Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty).ne'
  have hsub : {y : Coord (n + 2) → ℂ | ∀ f ∈ Q, eval y f = 0} ⊆
      {y | y ∈ Ym m ∧ ∀ k l, eval y (r2P k l) = c k l} := by
    intro y hy
    refine ⟨mem_Ym_iff_zeroLocus.mpr fun f hf => hy f (hYP.trans hPQ hf), fun k l => ?_⟩
    have := hy _ (hc k l)
    rwa [map_sub, eval_C, sub_eq_zero] at this
  exact zeroLocus_infinite_of_ringKrullDim_eq_one hdim ((r2_fibre_finite hM c).subset hsub)

end CC6Full
