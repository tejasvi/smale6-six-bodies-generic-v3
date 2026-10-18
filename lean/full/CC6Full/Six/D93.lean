import CC6Full.Six.D93Lead
import CC6Full.Six.D98

/-!
# Diagram 93: the polynomial of Theorem 6.15 (`thm:d93`)

§6.6 of the paper (`ss:d93`). At a singular place with diagram `93`, the triangle `B = {1, 2, 3}` (`{0, 1, 2}` in
Lean, renumbered by `triB`) is fully `w`-circled, and the body `4` of the paper (`3` in Lean) is not `z`-circled. The
facts of the proof of Theorem 6.15 on the leading data are `d93_lead`: the leading system of `B` solves `N(m_B)`,
and with `P_l` the leading coefficient of `p_{4l}` and `ẑ_4` that of `z_4`, `P_l² ẑ_4 ŵ_l = −1` and
`Σ_{l∈B} m_l P_l = 0`. By Lemma 6.9 (`three_shape`), the shape `τ'` of `(ŵ_B, [z_B]_2, p̂_B)` is a root of `S_{m_B}`,
with `ŵ_l = s' ℓ_l(τ')/M_B`. Choose `ρ` with `ρ² = −ẑ_4 s' L'/M_B`, `L' = ℓ₁ℓ₂ℓ₃(τ'; m_B)`. Then
`c_l = m_l P_l ρ` satisfy `c_l² = m_l² Λ_l(τ')` and `Σ c_l = 0` (`d93_cnorm`): the relation
`Σ_l ε_l m_l ŵ_l^{-1/2} = 0` of the paper, with the signs absorbed into the `c_l`.

The paper takes `P_93(μ) = Res_t(S_μ(t), Φ₃(t; μ))`, `Φ₃` the product of the four sums `√Y₁ ± √Y₂ ± √Y₃`. Here the
integral elimination lemma replaces the resultant: `elim_integral_int` (through `elim_gInt`) is applied to the
system `S93` in the unknowns `t`, `c_l` (`U93`) with the parameters `μ ∈ ℚ³`: `S_μ(t)`, `c_l² − μ_l² Λ_l(t; μ)` and
`Σ c_l`. The shape is integral over `ℚ[μ][1/g]`, `g = μ₁ + μ₂`, and the `c_l` are square roots of integral elements
(`hint93`). At `μ = (1, 2, 40)` the system has no complex solution: this is the heavy-mass fact `HeavyFact3` from the
proof of Lemma 6.13 (`lem:dominant`), that no sum `√Y₁ ± √Y₂ ± √Y₃` vanishes, taken here as a hypothesis. The
eliminant `P(μ)` is renamed to the masses of `B`, `μ = m_B = (m₁, m₂, m₃)`.

## Main statements

* `HeavyFact3`: the heavy-mass fact for one triangle.
* `d93_cnorm`: the normalized cross coefficients.
* `d93_poly`: **Theorem 6.15**, the polynomial: `P ≠ 0` and `P(m) = 0` for every germ with diagram `93`.
-/

namespace CC6Full.Six

open MvPolynomial

noncomputable section

/-! ## The heavy-mass fact -/

/-- **The heavy-mass fact of Lemma 6.13** (`lem:dominant`) for one triangle, used in Theorem 6.15: for a root `t` of
`S_{μ_H}`, `μ_H = (1, 2, 40)`, and square roots `c_l` of `Y_l = μ_l² Λ_l(t)`, the sum `c₁ + c₂ + c₃` is not zero.
Equivalently, no sum `√Y₁ ± √Y₂ ± √Y₃` vanishes, that is `Φ₃(t; μ_H) ≠ 0` at the roots of `S_{μ_H}` (the proof of
Lemma 6.13 gives `A₃(t) > A₁(t) + A₂(t)` with `A_l(t) = |√Y_l|`). -/
def HeavyFact3 : Prop :=
  ∀ t : ℂ, (Sμ μH).IsRoot t → ∀ c : Fin 3 → ℂ, (∀ l, c l ^ 2 = μH l ^ 2 * (LamP μH l).eval t) →
    ∑ l, c l ≠ 0

/-! ## The normalized cross coefficients -/

/-- The algebra of the proof of **Theorem 6.15** (`thm:d93`). Let `ŵ_l/s' = ℓ_l(τ'; μ)/M_μ` (Lemma 6.9),
`P_l² ẑ ŵ_l = −1` and `Σ μ_l P_l = 0`. With `ρ² = −ẑ s' L'/M_μ`, `L' = ℓ₁ℓ₂ℓ₃(τ'; μ)`, the numbers `c_l = μ_l P_l ρ`
satisfy `c_l² = μ_l² Λ_l(τ'; μ)` and `Σ c_l = 0`: by `ℓ_l Λ_l = L'`,
`P_l² ρ² M_μ = −P_l² ẑ (s' ℓ_l) Λ_l = −P_l² ẑ ŵ_l M_μ Λ_l = M_μ Λ_l`. -/
theorem d93_cnorm {μB wh P : Fin 3 → ℂ} {τ' s' zh : ℂ} (hs' : s' ≠ 0) (hMB : Mμ μB ≠ 0)
    (hw : ∀ l, wh l / s' = (ellP μB l).eval τ' / Mμ μB)
    (hc : ∀ l, P l ^ 2 * zh * wh l = -1)
    (hsum : ∑ l, μB l * P l = 0) :
    ∃ c : Fin 3 → ℂ, (∀ l, c l ^ 2 = μB l ^ 2 * (LamP μB l).eval τ') ∧ ∑ l, c l = 0 := by
  obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq
    (-(zh * s' * ((ellP μB 0).eval τ' * (ellP μB 1).eval τ' * (ellP μB 2).eval τ')) / Mμ μB) two_pos
  have e4 : ρ ^ 2 * Mμ μB = -(zh * s' * ((ellP μB 0).eval τ' * (ellP μB 1).eval τ' * (ellP μB 2).eval τ')) := by
    rw [hρ]
    exact div_mul_cancel₀ _ hMB
  refine ⟨fun l => μB l * P l * ρ, fun l => ?_, ?_⟩
  · have e2 : wh l * Mμ μB = s' * (ellP μB l).eval τ' := by
      have h := hw l
      rw [div_eq_div_iff hs' hMB] at h
      linear_combination h
    have e6 := ellP_mul_LamP μB τ' l
    have key : (P l * ρ) ^ 2 * Mμ μB = (LamP μB l).eval τ' * Mμ μB := by
      linear_combination P l ^ 2 * e4 + P l ^ 2 * zh * s' * e6 +
        P l ^ 2 * zh * (LamP μB l).eval τ' * e2 - Mμ μB * (LamP μB l).eval τ' * hc l
    have key' := mul_right_cancel₀ hMB key
    show (μB l * P l * ρ) ^ 2 = _
    linear_combination μB l ^ 2 * key'
  · show ∑ l, μB l * P l * ρ = 0
    rw [← Finset.sum_mul, hsum, zero_mul]

/-! ## The system -/

/-- The unknowns of the elimination for Theorem 6.15: the shape `t` of `B` and the three cross coefficients `c_l`. -/
inductive U93
  | t
  | c (l : Fin 3)

/-- The point `(t, c)` of `ℂ^U93`. -/
def U93.pt (t : ℂ) (c : Fin 3 → ℂ) : U93 → ℂ
  | .t => t
  | .c l => c l

/-- The polynomial ring `ℚ[μ, t, c]` of the system; the parameters `μ_l = X (Sum.inl l)` are the masses of `B`. -/
abbrev R93 := MvPolynomial (Fin 3 ⊕ U93) ℚ

/-- The inclusion `ℚ[μ] → ℚ[μ, t, c]`. -/
abbrev rn93 : MvPolynomial (Fin 3) ℚ →+* R93 := (rename Sum.inl).toRingHom

/-- The masses `μ`, variables of `ℚ[μ]`. -/
def μ93 (l : Fin 3) : MvPolynomial (Fin 3) ℚ := X l

/-- `S_μ(t)`. -/
def sys93T : R93 := (Sμ μ93).eval₂ rn93 (X (Sum.inr U93.t))

/-- `c_l² − μ_l² Λ_l(t; μ)`. -/
def sys93C (l : Fin 3) : R93 :=
  X (Sum.inr (U93.c l)) ^ 2 - rn93 (μ93 l ^ 2) * (LamP μ93 l).eval₂ rn93 (X (Sum.inr U93.t))

/-- `Σ_l c_l`. -/
def sys93S : R93 := ∑ l, X (Sum.inr (U93.c l))

/-- The system of the proof of Theorem 6.15. -/
def S93 : Set R93 := insert sys93T (insert sys93S (Set.range sys93C))

theorem sys93T_mem : sys93T ∈ S93 := Set.mem_insert _ _

theorem sys93S_mem : sys93S ∈ S93 := Set.mem_insert_of_mem _ (Set.mem_insert _ _)

theorem sys93C_mem (l : Fin 3) : sys93C l ∈ S93 :=
  Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨l, rfl⟩)

/-- `g = μ₁ + μ₂`. -/
def g93 : MvPolynomial (Fin 3) ℚ := μ93 0 + μ93 1

/-- The parameter point `μ = (1, 2, 40)`. -/
def μ₀93 : Fin 3 → ℚ := ![1, 2, 40]

/-! ## Evaluation of the system -/

section Eval

variable (μ : Fin 3 → ℂ) (x : U93 → ℂ)

theorem aeval_eval₂_rn93 (p : Polynomial (MvPolynomial (Fin 3) ℚ)) (u : U93) :
    aeval (Sum.elim μ x) (p.eval₂ rn93 (X (Sum.inr u))) = (p.map (aeval μ).toRingHom).eval (x u) := by
  have h := Polynomial.hom_eval₂ p rn93 (aeval (Sum.elim μ x)).toRingHom (X (Sum.inr u))
  have hc : (aeval (Sum.elim μ x)).toRingHom.comp rn93 = (aeval μ).toRingHom :=
    RingHom.ext fun q => by simp [aeval_rename]
  rw [hc, Polynomial.eval₂_eq_eval_map (aeval μ).toRingHom] at h
  simpa using h

theorem comp_μ93 : (aeval μ).toRingHom ∘ μ93 = μ := by
  funext l
  simp [μ93]

theorem aeval_sys93T : aeval (Sum.elim μ x) sys93T = (Sμ μ).eval (x U93.t) := by
  rw [sys93T, aeval_eval₂_rn93, map_Sμ, comp_μ93]

theorem aeval_sys93C (l : Fin 3) :
    aeval (Sum.elim μ x) (sys93C l) = x (U93.c l) ^ 2 - μ l ^ 2 * (LamP μ l).eval (x U93.t) := by
  have hl : aeval (Sum.elim μ x) (rn93 (μ93 l)) = μ l := by simp [μ93]
  simp only [sys93C, map_sub, map_mul, map_pow, hl, aeval_eval₂_rn93, map_LamP, comp_μ93, aeval_X, Sum.elim_inr]

theorem aeval_sys93S : aeval (Sum.elim μ x) sys93S = ∑ l, x (U93.c l) := by
  simp [sys93S]

end Eval

/-! ## Integrality, the parameter point, the germs -/

/-- Every unknown is integral over `ℚ[μ][1/g]` modulo the system: `t` is a root of `S_μ`, whose leading coefficient
is `g⁴ = (μ₁ + μ₂)⁴`, and `c_l` is a square root of `μ_l² Λ_l(t; μ)`. -/
theorem hint93 (i : U93) : Ideal.Quotient.mk (Ideal.span S93) (X (Sum.inr i)) ∈
    gInt ((Ideal.Quotient.mk (Ideal.span S93)).comp (rename Sum.inl).toRingHom) g93 := by
  have hmk : ∀ f ∈ S93, Ideal.Quotient.mk (Ideal.span S93) f = 0 := fun f hf =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hf)
  have hev : ∀ (p : Polynomial (MvPolynomial (Fin 3) ℚ)) (y : R93),
      Ideal.Quotient.mk (Ideal.span S93) (p.eval₂ rn93 y) =
        p.eval₂ ((Ideal.Quotient.mk (Ideal.span S93)).comp (rename Sum.inl).toRingHom)
          (Ideal.Quotient.mk (Ideal.span S93) y) :=
    fun p y => Polynomial.hom_eval₂ p rn93 _ y
  have ht : Ideal.Quotient.mk (Ideal.span S93) (X (Sum.inr U93.t)) ∈
      gInt ((Ideal.Quotient.mk (Ideal.span S93)).comp (rename Sum.inl).toRingHom) g93 :=
    mem_gInt_of_Sμ _ g93 μ93 (X_add_X_pow_ne_zero 0 1 4) (a := 4) (u := 1) (by rw [g93, one_mul])
      ((hev _ _).symm.trans (hmk _ sys93T_mem))
  cases i with
  | t => exact ht
  | c l =>
    refine mem_gInt_of_sq _ _ ?_
    have h0 := hmk _ (sys93C_mem l)
    rw [sys93C, map_sub, sub_eq_zero, map_pow] at h0
    rw [h0, map_mul, hev]
    exact mul_mem (map_mem_gInt _ _ (μ93 l ^ 2)) (eval₂_mem_gInt _ _ ht _)

theorem hg93 : eval μ₀93 g93 ≠ 0 := by
  norm_num [g93, μ₀93, μ93]

/-- At `μ = (1, 2, 40)` the system has no complex solution, by the heavy-mass fact for one triangle. -/
theorem hnone93 (hH : HeavyFact3) (x : U93 → ℂ) :
    ∃ f ∈ S93, aeval (Sum.elim (fun k => (μ₀93 k : ℂ)) x) f ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hμ : ∀ l, ((μ₀93 l : ℚ) : ℂ) = μH l := by
    intro l
    fin_cases l <;> simp [μ₀93, μH]
  have hμ' : (fun l => ((μ₀93 l : ℚ) : ℂ)) = μH := funext hμ
  have h1 := hcon _ sys93T_mem
  have h3 := hcon _ sys93S_mem
  rw [aeval_sys93T, hμ'] at h1
  rw [aeval_sys93S] at h3
  refine hH (x U93.t) h1 (fun l => x (U93.c l)) (fun l => ?_) h3
  have h4 := hcon _ (sys93C_mem l)
  rw [aeval_sys93C, hμ', hμ, sub_eq_zero] at h4
  exact h4

/-- The germ side of Theorem 6.15: at a singular place with diagram `93`, the system has a complex solution at the
masses `μ = m_B`: the shape `τ'` of the leading system of `B` (Lemma 6.9) and the normalized cross coefficients of
`d93_cnorm`. -/
theorem sol93 {m : Fin 6 → ℝ} (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d93) :
    ∃ x : U93 → ℂ, ∀ f ∈ S93, aeval (Sum.elim (fun l => (m (triB l) : ℂ)) x) f = 0 := by
  obtain ⟨-, hB, hc, hs⟩ := d93_lead hm G hD
  obtain ⟨hsB, hwB, hτB⟩ :=
    three_shape (fun l => K4.mass_ne_zero hm (triB l)) (Mμ_mass_ne_zero hm triB) hB
  obtain ⟨c, hc2, hcs⟩ := d93_cnorm hsB (Mμ_mass_ne_zero hm triB) hwB hc hs
  refine ⟨U93.pt (((G.w (triB 0)).coeff (-2) - (G.w (triB 2)).coeff (-2)) /
      ((G.w (triB 0)).coeff (-2) - (G.w (triB 1)).coeff (-2))) c, ?_⟩
  rintro f (rfl | rfl | ⟨l, rfl⟩)
  · rw [aeval_sys93T]
    exact hτB
  · rw [aeval_sys93S]
    exact hcs
  · rw [aeval_sys93C]
    exact sub_eq_zero.mpr (hc2 l)

/-! ## Theorem 6.15 -/

/-- **Theorem 6.15** (`thm:d93`), the polynomial, given the heavy-mass fact of Lemma 6.13 (`lem:dominant`) for one
triangle: there is a nonzero `P ∈ ℤ[m₁, …, m₆]` with `P(m) = 0` for all positive masses `m` that have a germ (a
singular place) with diagram `93` in the labelling of Table 1. `P` is the eliminant `P(μ)` of the system `S93`
(`elim_gInt`, the integral elimination lemma in place of the resultant `P_93` of the paper), with
`μ = m_B = (m₁, m₂, m₃)`; it is nonzero because `P(1, 2, 40) ≠ 0`. -/
theorem d93_poly (hH : HeavyFact3) : ∃ P : MvPolynomial (Fin 6) ℤ, P ≠ 0 ∧
    ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, G.HasDiagram Diagram.d93 →
      MvPolynomial.aeval m P = 0 := by
  obtain ⟨P, hP0, hP⟩ := elim_gInt S93 g93 hint93 μ₀93 hg93 (hnone93 hH)
  refine ⟨rename triB P, fun h0 => hP0 ?_, fun m hm G hD => ?_⟩
  · have h1 : rename triB P = rename triB (0 : MvPolynomial (Fin 3) ℤ) := by
      rw [h0, map_zero]
    rw [rename_injective _ triB_injective h1, map_zero]
  · rw [aeval_rename]
    exact aeval_real_eq_zero (hP _ (sol93 hm G hD))

end

end CC6Full.Six
