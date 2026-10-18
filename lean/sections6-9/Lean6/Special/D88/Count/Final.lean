import Lean6.Special.D88.Count.Systems
import Lean6.Special.D88.Count.DimSound

/-!
# Lemma 6.19(b): the dimension bounds from a checked basis

`count_KC_of`, `count_S12_of`: if a list `B` of polynomials over `ZMod 65521` passes `dimCheck 65521 11 B N`
(`N = 4788` for KC′, `20,316` for S12) and every element of `B` vanishes at every common zero of the engines' input
(`Comp.Count.kcInputs`, `s12Inputs`, the msolve inputs reduced modulo `65521`) in every commutative
`ZMod 65521`-algebra — the soundness statement of a Gröbner engine written in Lean — then
`(ZMod 65521)[v] ⧸ ⟨KC′(μ₀)⟩` (resp. `⟨S12(μ₀)⟩`), with the equations of §6.7, is finite-dimensional of dimension
at most `N`. These are Lemma 6.19(b)'s upper bounds, the only direction the proof uses; the engine run supplies the
two hypotheses.
-/

namespace Lean6.Special.D88.Count

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.Count MvPolynomial

instance fact_prime_65521 : Fact (Nat.Prime 65521) := ⟨by norm_num⟩

/-- **Reduction modulo `p` commutes with evaluation** in a `ZMod p`-algebra. -/
theorem eval_reduceMod (p : ℕ) [NeZero p] {R : Type*} [CommRing R] [Algebra (ZMod p) R] (x : ℕ → R) :
    ∀ f : Poly ℤ, Poly.eval (K4.C4.algH p R) x (reduceMod p f) = Poly.eval (intHom R) x f
  | [] => rfl
  | t :: f => by
    simp only [reduceMod, List.map_cons, Poly.eval_cons] at *
    rw [show (List.map (fun t => ((t.1 % (p : ℤ)).toNat, t.2)) f) = reduceMod p f from rfl, eval_reduceMod p x f,
      K4.C4.algH_f]
    congr 1
    have hp : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    have h0 : 0 ≤ t.1 % (p : ℤ) := Int.emod_nonneg _ hp.ne'
    have hc : (((t.1 % (p : ℤ)).toNat : ℕ) : ZMod p) = ((t.1 : ℤ) : ZMod p) := by
      rw [← ZMod.intCast_mod t.1 p]
      exact_mod_cast congrArg (fun z : ℤ => (z : ZMod p)) (Int.toNat_of_nonneg h0)
    rw [hc, map_intCast]
    rfl

theorem s12Inputs_len : ∀ f ∈ s12Inputs, ∀ t ∈ f, t.2.length ≤ 11 := by decide

theorem kcInputs_len : ∀ f ∈ kcInputs, ∀ t ∈ f, t.2.length ≤ 11 := by decide

theorem thirty_mul_inv : (30 : MvPolynomial (Fin 11) (ZMod 65521)) * C (30 : ZMod 65521)⁻¹ = 1 := by
  rw [show (30 : MvPolynomial (Fin 11) (ZMod 65521)) = C 30 from (map_ofNat C 30).symm, ← C_mul,
    mul_inv_cancel₀ (by decide : (30 : ZMod 65521) ≠ 0), C_1]

/-- The engine input of S12, row `j`, as a polynomial: `s12U j · S12eqs j`. -/
theorem toMv_s12Input (j : Fin 12) :
    toMv 11 65521 (reduceMod 65521 (s12InputsZ.getD j [])) = s12U j * S12eqs j := by
  have hlen : ∀ t ∈ reduceMod 65521 (s12InputsZ.getD j []), t.2.length ≤ 11 := by
    intro t ht
    refine s12Inputs_len _ ?_ t ht
    simp only [s12Inputs, List.mem_map]
    refine ⟨s12InputsZ.getD j [], ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ (by simp [s12InputsZ])]
    exact List.getElem_mem _
  rw [← aeval_X_left_apply (toMv 11 65521 _), ← eval_toMv X _ hlen, eval_reduceMod,
    eval_s12InputsZ _ thirty_mul_inv]
  rfl

/-- The engine input of KC′, row `j`, as a polynomial: `kcU' j · KCprimeEqs j`. -/
theorem toMv_kcInput (j : Fin 12) :
    toMv 11 65521 (reduceMod 65521 (kcInputsZ.getD j [])) = kcU' j * KCprimeEqs j := by
  have hlen : ∀ t ∈ reduceMod 65521 (kcInputsZ.getD j []), t.2.length ≤ 11 := by
    intro t ht
    refine kcInputs_len _ ?_ t ht
    simp only [kcInputs, List.mem_map]
    refine ⟨kcInputsZ.getD j [], ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ (by simp [kcInputsZ])]
    exact List.getElem_mem _
  rw [← aeval_X_left_apply (toMv 11 65521 _), ← eval_toMv X _ hlen, eval_reduceMod, eval_kcInputsZ]
  rfl

/-- The ideal of the engine input of S12 lies in the ideal of the equations of §6.7. -/
theorem span_s12Inputs_le :
    Ideal.span {q | ∃ f ∈ s12Inputs, toMv 11 65521 f = q} ≤ Ideal.span (Set.range S12eqs) := by
  rw [Ideal.span_le]
  rintro q ⟨f, hf, rfl⟩
  simp only [s12Inputs, List.mem_map] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
  have hi12 : i < 12 := by simpa [s12InputsZ] using hi
  have := toMv_s12Input ⟨i, hi12⟩
  rw [show s12InputsZ.getD (⟨i, hi12⟩ : Fin 12) [] = s12InputsZ[i] from List.getD_eq_getElem _ _ hi] at this
  have hmem := Ideal.mul_mem_left (Ideal.span (Set.range S12eqs)) (s12U ⟨i, hi12⟩)
    (Ideal.subset_span ⟨(⟨i, hi12⟩ : Fin 12), rfl⟩)
  rw [← this] at hmem
  exact hmem

/-- The ideal of the engine input of KC′ lies in the ideal of the equations of §6.7. -/
theorem span_kcInputs_le :
    Ideal.span {q | ∃ f ∈ kcInputs, toMv 11 65521 f = q} ≤ Ideal.span (Set.range KCprimeEqs) := by
  rw [Ideal.span_le]
  rintro q ⟨f, hf, rfl⟩
  simp only [kcInputs, List.mem_map] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
  have hi12 : i < 12 := by simpa [kcInputsZ] using hi
  have := toMv_kcInput ⟨i, hi12⟩
  rw [show kcInputsZ.getD (⟨i, hi12⟩ : Fin 12) [] = kcInputsZ[i] from List.getD_eq_getElem _ _ hi] at this
  have hmem := Ideal.mul_mem_left (Ideal.span (Set.range KCprimeEqs)) (kcU' ⟨i, hi12⟩)
    (Ideal.subset_span ⟨(⟨i, hi12⟩ : Fin 12), rfl⟩)
  rw [← this] at hmem
  exact hmem

theorem dimCheck_len {p n N : ℕ} {B : List (Poly ℕ)} (h : dimCheck p n B N = true) :
    ∀ g ∈ B, ∀ t ∈ g, t.2.length ≤ n := by
  unfold dimCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  intro g hg t ht
  exact ((polyOK_spec (h.1 g hg)).2.1 t ht).2.2.le

/-- The quotient of Lemma 6.19(b) for KC′. -/
abbrev AqKC := MvPolynomial (Fin 11) (ZMod 65521) ⧸ Ideal.span (Set.range KCprimeEqs)

/-- The quotient of Lemma 6.19(b) for S12. -/
abbrev AqS12 := MvPolynomial (Fin 11) (ZMod 65521) ⧸ Ideal.span (Set.range S12eqs)

/-- **Lemma 6.19(b) for KC′, from a checked basis.** -/
theorem count_KC_of (B : List (Poly ℕ)) (hcheck : dimCheck 65521 11 B 4788 = true)
    (hgood : ∀ (R : Type) [CommRing R] [Algebra (ZMod 65521) R] (x : ℕ → R),
      (∀ f ∈ kcInputs, Poly.eval (K4.C4.algH 65521 R) x f = 0) → ∀ g ∈ B, Poly.eval (K4.C4.algH 65521 R) x g = 0) :
    Module.Finite (ZMod 65521) AqKC ∧ Module.finrank (ZMod 65521) AqKC ≤ 4788 :=
  dimCheck_sound 65521 11 B 4788 hcheck _ fun g hg =>
    span_kcInputs_le (mem_span_of_good kcInputs B kcInputs_len (dimCheck_len hcheck) hgood g hg)

/-- **Lemma 6.19(b) for S12, from a checked basis.** -/
theorem count_S12_of (B : List (Poly ℕ)) (hcheck : dimCheck 65521 11 B 20316 = true)
    (hgood : ∀ (R : Type) [CommRing R] [Algebra (ZMod 65521) R] (x : ℕ → R),
      (∀ f ∈ s12Inputs, Poly.eval (K4.C4.algH 65521 R) x f = 0) → ∀ g ∈ B, Poly.eval (K4.C4.algH 65521 R) x g = 0) :
    Module.Finite (ZMod 65521) AqS12 ∧ Module.finrank (ZMod 65521) AqS12 ≤ 20316 :=
  dimCheck_sound 65521 11 B 20316 hcheck _ fun g hg =>
    span_s12Inputs_le (mem_span_of_good s12Inputs B s12Inputs_len (dimCheck_len hcheck) hgood g hg)

end Lean6.Special.D88.Count
