import CC6Full.Six.D98Lead
import CC6Full.Six.Three
import CC6Full.Six.D98Elim

/-!
# Diagram 98: the polynomial of Theorem 6.12 (`thm:d98`)

§6.5 of the paper (`ss:d98`). At a singular place with diagram `98`, the leading data of the triangles
`A = {4, 5, 6}` and `B = {1, 2, 3}` (`{3, 4, 5}` and `{0, 1, 2}` in Lean, renumbered by `triA` and `triB`) satisfy
Lemma 6.11 (`d98_lead`). By Lemma 6.9 (`three_shape`), the shape `τ` of the `A`-data is a root of `S_{m_A}` and the
`w`-shape `τ'` of the `B`-data is a root of `S_{m_B}`, with `ẑ_j = s ℓ_j(τ)/M_A` and `ŵ_l = s' ℓ_l(τ')/M_B`. Choose
`ρ` with `ρ² = −s s' L L'/(M_A M_B)`, `L = ℓ₁ℓ₂ℓ₃(τ; m_A)` and `L' = ℓ₁ℓ₂ℓ₃(τ'; m_B)`. Then the relation
`p̂_jl² ẑ_j ŵ_l = −1` of Lemma 6.11 (c) gives `c_jl² = m_j² m_l² Λ_j(τ) Λ_l(τ')` for `c_jl = m_j m_l p̂_jl ρ`, and
Lemma 6.11 (d) gives `Σ c_jl = 0` (`d98_cnorm`). This is the paper's `c_jl² = κ m_j² m_l² Λ_j(τ) Λ_l(τ')` divided by
the common factor `κ = 1/ρ²`.

The paper eliminates `τ`, `τ'` and the `c_jl` with the product `Φ` over the sign matrices and two resultants.
Here the integral elimination lemma replaces the resultants: `elim_integral_int` (through `elim_gInt`) is applied
to the system `S98` in the unknowns `t`, `t'`, `c_jl` (`U98`) with the parameters `(μ, μ') ∈ ℚ³ × ℚ³`:
`S_μ(t)`, `S_μ'(t')`, `c_jl² − μ_j² μ'_l² Λ_j(t; μ) Λ_l(t'; μ')` and `Σ c_jl`. The shapes are integral over
`ℚ[μ, μ'][1/g]`, `g = (μ₁ + μ₂)(μ'₁ + μ'₂)`, because the leading coefficient of `S_μ` is `(μ₁ + μ₂)⁴`, and the `c_jl`
are square roots of integral elements (`hint98`). At `μ = μ' = (1, 2, 40)` the system has no complex solution: this
is the heavy-mass fact `HeavyFact` of Lemma 6.13 (`lem:dominant`), that no signed sum `Σ ε_jl √Y_jl` vanishes, taken
here as a hypothesis. The eliminant `P(μ, μ')` is renamed to the masses of the bodies, `μ = m_A` and `μ' = m_B`.

## Main statements

* `μH`, `HeavyFact`: the masses `(1, 2, 40)` and the heavy-mass fact of Lemma 6.13 for two triangles.
* `d98_cnorm`: the normalized cross coefficients.
* `d98_poly`: **Theorem 6.12**, the polynomial: `P ≠ 0` and `P(m) = 0` for every germ with diagram `98`.
-/

namespace CC6Full.Six

open MvPolynomial

noncomputable section

/-! ## The heavy-mass fact -/

/-- The masses `μ_H = (1, 2, 40)` of Lemma 6.13 (`lem:dominant`), as complex numbers. -/
def μH : Fin 3 → ℂ := ![1, 2, 40]

/-- **The heavy-mass fact of Lemma 6.13** (`lem:dominant`) for two triangles: for roots `t`, `t'` of `S_{μ_H}`,
`μ_H = (1, 2, 40)`, and square roots `c_jl` of `Y_jl = μ_j² μ_l² Λ_j(t) Λ_l(t')`, the sum `Σ_{j,l} c_jl` is not zero.
Equivalently, no signed sum `Σ ε_jl √Y_jl` vanishes, that is `Ψ(t, t') ≠ 0` at `μ = μ' = μ_H` in the proof of
Theorem 6.12. -/
def HeavyFact : Prop :=
  ∀ t t' : ℂ, (Sμ μH).IsRoot t → (Sμ μH).IsRoot t' → ∀ c : Fin 3 → Fin 3 → ℂ,
    (∀ j l, c j l ^ 2 = μH j ^ 2 * μH l ^ 2 * (LamP μH j).eval t * (LamP μH l).eval t') →
      ∑ j, ∑ l, c j l ≠ 0

/-! ## The normalized cross coefficients -/

/-- The algebra of the proof of **Theorem 6.12** (`thm:d98`). Let `ẑ_j/s = ℓ_j(τ; μ)/M_μ` and
`ŵ_l/s' = ℓ_l(τ'; μ')/M_μ'` (Lemma 6.9 for the two triangles), `p̂_jl² ẑ_j ŵ_l = −1` and `Σ μ_j μ'_l p̂_jl = 0`
(Lemma 6.11 (c), (d)). With `ρ² = −s s' L L'/(M_μ M_μ')`, `L = ℓ₁ℓ₂ℓ₃(τ; μ)` and `L' = ℓ₁ℓ₂ℓ₃(τ'; μ')`, the numbers
`c_jl = μ_j μ'_l p̂_jl ρ` satisfy `c_jl² = μ_j² μ'_l² Λ_j(τ; μ) Λ_l(τ'; μ')` and `Σ c_jl = 0`: by `ℓ_j Λ_j = L`,
`p̂_jl² ρ² M_μ M_μ' = −p̂_jl² (s ℓ_j)(s' ℓ'_l) Λ_j Λ'_l = −p̂_jl² ẑ_j ŵ_l M_μ M_μ' Λ_j Λ'_l = M_μ M_μ' Λ_j Λ'_l`. -/
theorem d98_cnorm {μA μB zh wh : Fin 3 → ℂ} {ph : Fin 3 → Fin 3 → ℂ} {s s' τ τ' : ℂ}
    (hs : s ≠ 0) (hs' : s' ≠ 0) (hMA : Mμ μA ≠ 0) (hMB : Mμ μB ≠ 0)
    (hz : ∀ j, zh j / s = (ellP μA j).eval τ / Mμ μA)
    (hw : ∀ l, wh l / s' = (ellP μB l).eval τ' / Mμ μB)
    (hc : ∀ j l, ph j l ^ 2 * zh j * wh l = -1)
    (hsum : ∑ j, ∑ l, μA j * μB l * ph j l = 0) :
    ∃ c : Fin 3 → Fin 3 → ℂ,
      (∀ j l, c j l ^ 2 = μA j ^ 2 * μB l ^ 2 * (LamP μA j).eval τ * (LamP μB l).eval τ') ∧
        ∑ j, ∑ l, c j l = 0 := by
  obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq
    (-(s * s' * ((ellP μA 0).eval τ * (ellP μA 1).eval τ * (ellP μA 2).eval τ) *
      ((ellP μB 0).eval τ' * (ellP μB 1).eval τ' * (ellP μB 2).eval τ')) / (Mμ μA * Mμ μB)) two_pos
  have hM : Mμ μA * Mμ μB ≠ 0 := mul_ne_zero hMA hMB
  have e4 : ρ ^ 2 * (Mμ μA * Mμ μB) = -(s * s' * ((ellP μA 0).eval τ * (ellP μA 1).eval τ * (ellP μA 2).eval τ) *
      ((ellP μB 0).eval τ' * (ellP μB 1).eval τ' * (ellP μB 2).eval τ')) := by
    rw [hρ]
    exact div_mul_cancel₀ _ hM
  refine ⟨fun j l => μA j * μB l * ph j l * ρ, fun j l => ?_, ?_⟩
  · have e1 : zh j * Mμ μA = s * (ellP μA j).eval τ := by
      have h := hz j
      rw [div_eq_div_iff hs hMA] at h
      linear_combination h
    have e2 : wh l * Mμ μB = s' * (ellP μB l).eval τ' := by
      have h := hw l
      rw [div_eq_div_iff hs' hMB] at h
      linear_combination h
    have e5 := ellP_mul_LamP μA τ j
    have e6 := ellP_mul_LamP μB τ' l
    have key : (ph j l * ρ) ^ 2 * (Mμ μA * Mμ μB) =
        (LamP μA j).eval τ * (LamP μB l).eval τ' * (Mμ μA * Mμ μB) := by
      linear_combination ph j l ^ 2 * e4 +
        ph j l ^ 2 * s * s' * ((ellP μB 0).eval τ' * (ellP μB 1).eval τ' * (ellP μB 2).eval τ') * e5 +
        ph j l ^ 2 * s * s' * (ellP μA j).eval τ * (LamP μA j).eval τ * e6 +
        ph j l ^ 2 * s' * (ellP μB l).eval τ' * (LamP μA j).eval τ * (LamP μB l).eval τ' * e1 +
        ph j l ^ 2 * zh j * Mμ μA * (LamP μA j).eval τ * (LamP μB l).eval τ' * e2 -
        Mμ μA * Mμ μB * (LamP μA j).eval τ * (LamP μB l).eval τ' * hc j l
    have key' := mul_right_cancel₀ hM key
    show (μA j * μB l * ph j l * ρ) ^ 2 = _
    linear_combination μA j ^ 2 * μB l ^ 2 * key'
  · show ∑ j, ∑ l, μA j * μB l * ph j l * ρ = 0
    rw [show ∑ j, ∑ l, μA j * μB l * ph j l * ρ = (∑ j, ∑ l, μA j * μB l * ph j l) * ρ by
      simp only [Finset.sum_mul], hsum, zero_mul]

/-! ## The system -/

/-- The unknowns of the elimination for Theorem 6.12: the shape `t` of `A`, the shape `t'` of `B` and the nine
cross coefficients `c_jl`. -/
inductive U98
  | tA
  | tB
  | c (j l : Fin 3)

/-- The point `(t, t', c)` of `ℂ^U98`. -/
def U98.pt (t t' : ℂ) (c : Fin 3 → Fin 3 → ℂ) : U98 → ℂ
  | .tA => t
  | .tB => t'
  | .c j l => c j l

/-- The polynomial ring `ℚ[μ, μ', t, t', c]` of the system: the parameters are `μ_j = X (Sum.inl (Sum.inl j))` (the
masses of `A`) and `μ'_l = X (Sum.inl (Sum.inr l))` (the masses of `B`). -/
abbrev R98 := MvPolynomial ((Fin 3 ⊕ Fin 3) ⊕ U98) ℚ

/-- The inclusion `ℚ[μ, μ'] → ℚ[μ, μ', t, t', c]`. -/
abbrev rn98 : MvPolynomial (Fin 3 ⊕ Fin 3) ℚ →+* R98 := (rename Sum.inl).toRingHom

/-- The masses `μ` of `A`, variables of `ℚ[μ, μ']`. -/
def μA98 (j : Fin 3) : MvPolynomial (Fin 3 ⊕ Fin 3) ℚ := X (Sum.inl j)

/-- The masses `μ'` of `B`, variables of `ℚ[μ, μ']`. -/
def μB98 (l : Fin 3) : MvPolynomial (Fin 3 ⊕ Fin 3) ℚ := X (Sum.inr l)

/-- `S_μ(t)`. -/
def sys98A : R98 := (Sμ μA98).eval₂ rn98 (X (Sum.inr U98.tA))

/-- `S_μ'(t')`. -/
def sys98B : R98 := (Sμ μB98).eval₂ rn98 (X (Sum.inr U98.tB))

/-- `c_jl² − μ_j² μ'_l² Λ_j(t; μ) Λ_l(t'; μ')`. -/
def sys98C (j l : Fin 3) : R98 :=
  X (Sum.inr (U98.c j l)) ^ 2 - rn98 (μA98 j ^ 2 * μB98 l ^ 2) *
    (LamP μA98 j).eval₂ rn98 (X (Sum.inr U98.tA)) * (LamP μB98 l).eval₂ rn98 (X (Sum.inr U98.tB))

/-- `Σ_{j,l} c_jl`. -/
def sys98S : R98 := ∑ j, ∑ l, X (Sum.inr (U98.c j l))

/-- The system of the proof of Theorem 6.12. -/
def S98 : Set R98 :=
  insert sys98A (insert sys98B (insert sys98S (Set.range fun jl : Fin 3 × Fin 3 => sys98C jl.1 jl.2)))

theorem sys98A_mem : sys98A ∈ S98 := Set.mem_insert _ _

theorem sys98B_mem : sys98B ∈ S98 := Set.mem_insert_of_mem _ (Set.mem_insert _ _)

theorem sys98S_mem : sys98S ∈ S98 := Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem sys98C_mem (j l : Fin 3) : sys98C j l ∈ S98 :=
  Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨(j, l), rfl⟩))

/-- `g = (μ₁ + μ₂)(μ'₁ + μ'₂)`. -/
def g98 : MvPolynomial (Fin 3 ⊕ Fin 3) ℚ := (μA98 0 + μA98 1) * (μB98 0 + μB98 1)

/-- The parameter point `μ = μ' = (1, 2, 40)`. -/
def μ₀98 : Fin 3 ⊕ Fin 3 → ℚ := Sum.elim ![1, 2, 40] ![1, 2, 40]

/-! ## Evaluation of the system -/

section Eval

variable (μ : Fin 3 ⊕ Fin 3 → ℂ) (x : U98 → ℂ)

theorem aeval_eval₂_rn98 (p : Polynomial (MvPolynomial (Fin 3 ⊕ Fin 3) ℚ)) (u : U98) :
    aeval (Sum.elim μ x) (p.eval₂ rn98 (X (Sum.inr u))) = (p.map (aeval μ).toRingHom).eval (x u) := by
  have h := Polynomial.hom_eval₂ p rn98 (aeval (Sum.elim μ x)).toRingHom (X (Sum.inr u))
  have hc : (aeval (Sum.elim μ x)).toRingHom.comp rn98 = (aeval μ).toRingHom :=
    RingHom.ext fun q => by simp [aeval_rename]
  rw [hc, Polynomial.eval₂_eq_eval_map (aeval μ).toRingHom] at h
  simpa using h

theorem comp_μA98 : (aeval μ).toRingHom ∘ μA98 = fun j => μ (Sum.inl j) := by
  funext j
  simp [μA98]

theorem comp_μB98 : (aeval μ).toRingHom ∘ μB98 = fun l => μ (Sum.inr l) := by
  funext l
  simp [μB98]

theorem aeval_sys98A : aeval (Sum.elim μ x) sys98A = (Sμ fun j => μ (Sum.inl j)).eval (x U98.tA) := by
  rw [sys98A, aeval_eval₂_rn98, map_Sμ, comp_μA98]

theorem aeval_sys98B : aeval (Sum.elim μ x) sys98B = (Sμ fun l => μ (Sum.inr l)).eval (x U98.tB) := by
  rw [sys98B, aeval_eval₂_rn98, map_Sμ, comp_μB98]

theorem aeval_sys98C (j l : Fin 3) : aeval (Sum.elim μ x) (sys98C j l) =
    x (U98.c j l) ^ 2 - μ (Sum.inl j) ^ 2 * μ (Sum.inr l) ^ 2 *
      (LamP (fun j => μ (Sum.inl j)) j).eval (x U98.tA) * (LamP (fun l => μ (Sum.inr l)) l).eval (x U98.tB) := by
  have hA : aeval (Sum.elim μ x) (rn98 (μA98 j)) = μ (Sum.inl j) := by simp [μA98]
  have hB : aeval (Sum.elim μ x) (rn98 (μB98 l)) = μ (Sum.inr l) := by simp [μB98]
  simp only [sys98C, map_sub, map_mul, map_pow, hA, hB, aeval_eval₂_rn98, map_LamP, comp_μA98, comp_μB98, aeval_X,
    Sum.elim_inr]

theorem aeval_sys98S : aeval (Sum.elim μ x) sys98S = ∑ j, ∑ l, x (U98.c j l) := by
  simp [sys98S]

end Eval

/-! ## Integrality, the parameter point, the germs -/

/-- Every unknown is integral over `ℚ[μ, μ'][1/g]` modulo the system: `t` and `t'` are roots of `S_μ` and `S_μ'`,
whose leading coefficients `(μ₁ + μ₂)⁴` and `(μ'₁ + μ'₂)⁴` divide `g⁴`, and `c_jl` is a square root of
`μ_j² μ'_l² Λ_j(t; μ) Λ_l(t'; μ')`. -/
theorem hint98 (i : U98) : Ideal.Quotient.mk (Ideal.span S98) (X (Sum.inr i)) ∈
    gInt ((Ideal.Quotient.mk (Ideal.span S98)).comp (rename Sum.inl).toRingHom) g98 := by
  have hmk : ∀ f ∈ S98, Ideal.Quotient.mk (Ideal.span S98) f = 0 := fun f hf =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hf)
  have hev : ∀ (p : Polynomial (MvPolynomial (Fin 3 ⊕ Fin 3) ℚ)) (y : R98),
      Ideal.Quotient.mk (Ideal.span S98) (p.eval₂ rn98 y) =
        p.eval₂ ((Ideal.Quotient.mk (Ideal.span S98)).comp (rename Sum.inl).toRingHom)
          (Ideal.Quotient.mk (Ideal.span S98) y) :=
    fun p y => Polynomial.hom_eval₂ p rn98 _ y
  have htA : Ideal.Quotient.mk (Ideal.span S98) (X (Sum.inr U98.tA)) ∈
      gInt ((Ideal.Quotient.mk (Ideal.span S98)).comp (rename Sum.inl).toRingHom) g98 :=
    mem_gInt_of_Sμ _ g98 μA98 (X_add_X_pow_ne_zero (Sum.inl 0) (Sum.inl 1) 4) (a := 4) (u := (μB98 0 + μB98 1) ^ 4)
      (by rw [g98]; ring) ((hev _ _).symm.trans (hmk _ sys98A_mem))
  have htB : Ideal.Quotient.mk (Ideal.span S98) (X (Sum.inr U98.tB)) ∈
      gInt ((Ideal.Quotient.mk (Ideal.span S98)).comp (rename Sum.inl).toRingHom) g98 :=
    mem_gInt_of_Sμ _ g98 μB98 (X_add_X_pow_ne_zero (Sum.inr 0) (Sum.inr 1) 4) (a := 4) (u := (μA98 0 + μA98 1) ^ 4)
      (by rw [g98]; ring) ((hev _ _).symm.trans (hmk _ sys98B_mem))
  cases i with
  | tA => exact htA
  | tB => exact htB
  | c j l =>
    refine mem_gInt_of_sq _ _ ?_
    have h0 := hmk _ (sys98C_mem j l)
    rw [sys98C, map_sub, sub_eq_zero, map_pow] at h0
    rw [h0, map_mul, map_mul, hev, hev]
    exact mul_mem (mul_mem (map_mem_gInt _ _ (μA98 j ^ 2 * μB98 l ^ 2)) (eval₂_mem_gInt _ _ htA _))
      (eval₂_mem_gInt _ _ htB _)

theorem hg98 : eval μ₀98 g98 ≠ 0 := by
  norm_num [g98, μ₀98, μA98, μB98]

/-- At `μ = μ' = (1, 2, 40)` the system has no complex solution, by the heavy-mass fact of Lemma 6.13. -/
theorem hnone98 (hH : HeavyFact) (x : U98 → ℂ) :
    ∃ f ∈ S98, aeval (Sum.elim (fun k => (μ₀98 k : ℂ)) x) f ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hA : ∀ j, ((μ₀98 (Sum.inl j) : ℚ) : ℂ) = μH j := by
    intro j
    fin_cases j <;> simp [μ₀98, μH]
  have hB : ∀ l, ((μ₀98 (Sum.inr l) : ℚ) : ℂ) = μH l := by
    intro l
    fin_cases l <;> simp [μ₀98, μH]
  have hA' : (fun j => ((μ₀98 (Sum.inl j) : ℚ) : ℂ)) = μH := funext hA
  have hB' : (fun l => ((μ₀98 (Sum.inr l) : ℚ) : ℂ)) = μH := funext hB
  have h1 := hcon _ sys98A_mem
  have h2 := hcon _ sys98B_mem
  have h3 := hcon _ sys98S_mem
  rw [aeval_sys98A, hA'] at h1
  rw [aeval_sys98B, hB'] at h2
  rw [aeval_sys98S] at h3
  refine hH (x U98.tA) (x U98.tB) h1 h2 (fun j l => x (U98.c j l)) (fun j l => ?_) h3
  have h4 := hcon _ (sys98C_mem j l)
  rw [aeval_sys98C, hA', hB', hA, hB, sub_eq_zero] at h4
  exact h4

/-- The germ side of Theorem 6.12: at a singular place with diagram `98`, the system has a complex solution at the
masses `μ = m_A`, `μ' = m_B`: the shapes `τ`, `τ'` of the two triangles (Lemma 6.9) and the normalized cross
coefficients of `d98_cnorm`. -/
theorem sol98 {m : Fin 6 → ℝ} (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d98) :
    ∃ x : U98 → ℂ, ∀ f ∈ S98, aeval (Sum.elim (fun k => (m (Sum.elim triA triB k) : ℂ)) x) f = 0 := by
  obtain ⟨⟨hA, -⟩, ⟨hB, -⟩, hc, hs⟩ := d98_lead hm G hD
  obtain ⟨hsA, hzA, hτA⟩ :=
    three_shape (fun j => K4.mass_ne_zero hm (triA j)) (Mμ_mass_ne_zero hm triA) hA
  obtain ⟨hsB, hwB, hτB⟩ :=
    three_shape (fun l => K4.mass_ne_zero hm (triB l)) (Mμ_mass_ne_zero hm triB) hB
  obtain ⟨c, hc2, hcs⟩ :=
    d98_cnorm hsA hsB (Mμ_mass_ne_zero hm triA) (Mμ_mass_ne_zero hm triB) hzA hwB hc hs
  refine ⟨U98.pt (((G.z (triA 0)).coeff (-2) - (G.z (triA 2)).coeff (-2)) /
      ((G.z (triA 0)).coeff (-2) - (G.z (triA 1)).coeff (-2)))
    (((G.w (triB 0)).coeff (-2) - (G.w (triB 2)).coeff (-2)) /
      ((G.w (triB 0)).coeff (-2) - (G.w (triB 1)).coeff (-2))) c, ?_⟩
  rintro f (rfl | rfl | rfl | ⟨⟨j, l⟩, rfl⟩)
  · rw [aeval_sys98A]
    exact hτA
  · rw [aeval_sys98B]
    exact hτB
  · rw [aeval_sys98S]
    exact hcs
  · rw [aeval_sys98C]
    exact sub_eq_zero.mpr (hc2 j l)

theorem triAB_injective : Function.Injective (Sum.elim triA triB) :=
  triA_injective.sumElim triB_injective triA_ne_triB

/-! ## Theorem 6.12 -/

/-- **Theorem 6.12** (`thm:d98`), the polynomial, given the heavy-mass fact of Lemma 6.13 (`lem:dominant`): there is a
nonzero `P ∈ ℤ[m₁, …, m₆]` with `P(m) = 0` for all positive masses `m` that have a germ (a singular place) with
diagram `98` in the labelling of Table 1. `P` is the eliminant `P(μ, μ')` of the system `S98` (`elim_gInt`, the
integral elimination lemma in place of the resultants of the paper), with `μ = m_A = (m₄, m₅, m₆)` and
`μ' = m_B = (m₁, m₂, m₃)`; it is nonzero because `P((1, 2, 40), (1, 2, 40)) ≠ 0`. -/
theorem d98_poly (hH : HeavyFact) : ∃ P : MvPolynomial (Fin 6) ℤ, P ≠ 0 ∧
    ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, G.HasDiagram Diagram.d98 →
      MvPolynomial.aeval m P = 0 := by
  obtain ⟨P, hP0, hP⟩ := elim_gInt S98 g98 hint98 μ₀98 hg98 (hnone98 hH)
  refine ⟨rename (Sum.elim triA triB) P, fun h0 => hP0 ?_, fun m hm G hD => ?_⟩
  · have h1 : rename (Sum.elim triA triB) P = rename (Sum.elim triA triB) (0 : MvPolynomial (Fin 3 ⊕ Fin 3) ℤ) := by
      rw [h0, map_zero]
    rw [rename_injective _ triAB_injective h1, map_zero]
  · rw [aeval_rename]
    exact aeval_real_eq_zero (hP _ (sol98 hm G hD))

end

end CC6Full.Six
