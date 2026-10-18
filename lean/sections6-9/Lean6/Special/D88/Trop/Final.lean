import Lean6.Special.D88.Trop.Cover
import Lean6.Special.Comp.D88.Trop.RunN4
import Lean6.Special.Comp.D88.Trop.RunKC

/-!
# Lemma 6.19(a): the hypotheses of Lemma 6.18 for `S12` and `KC12` at `μ₀ = (1, 2, 3, 30)`, `p = 65521`

For each of the two systems (`N4`: the ideal of `S12`; `KC`: the ideal of `KC12`), with `G = G_N4` (30 polynomials) or
`G_KC` (101 polynomials) in the seventeen torus coordinates `ξ` with coefficients in `ℤ[μ₁, …, μ₄]`:

* **(i) `G` lies in the ideal** (`n4_G_mem`, `kc_G_mem`): for every `g ∈ G` there are polynomials `c₁, …, c₁₂` with
  `g(ξ(v), μ) = Σ_j c_j(v, μ, i_u) F_j(v, μ, i_u)` at every point of every commutative ring at which `μ_u i_u = 1`,
  where `F₁, …, F₁₂` are the polynomials of `S12` (resp. `KC12`) of `Sys`, `ξ(v)` the coordinates as polynomials in the
  unknowns, and `μ_u = μ₄` (resp. `μ₃`). So `g(ξ(v))` lies in the ideal of the system over `ℤ[μ, 1/μ_u]`, hence over
  `O = ℤ[μ]_𝔪` (`μ₄ ≡ 30`, `μ₃ ≡ 3` are units there).
* **(ii) the coefficients are units of `O`** (`n4_units`, `kc_units`): every coefficient of `g` as a polynomial in `ξ`
  (a polynomial in `μ`) is nonzero at `μ₀` modulo `p` (354 and 1133 coefficients), and the `ξ`-monomials of `g` are
  distinct.
* **(iii)–(iv) the initial forms** (`n4_torus`, `kc_torus`): for every `w ∈ ℚ^17` with some `w_i < 0` and every field
  `K` of characteristic `p`, the initial forms at `w` of the reductions `Gb` (the coefficients at `μ₀` modulo `p`) have
  no common zero in `(K^*)^17` — **given** the torus emptiness of one explicit system for each of `S12` and `KC12`
  (`hypsN4`, `hypsKC`, `n4_hyps`, `kc_hyps`): the initial system on the ray `w = (0, …, 0, 2, …, 2, −1, …, −1)`
  (the `X`-coordinates `0`, the `Y`- (resp. `U`-) coordinates `2`, the `p_kl` `−1`), along which the `Y`-positions
  escape to infinity. For these two systems the checker would need a Nullstellensatz certificate, which Singular's
  `lift` did not produce in 35 minutes (memory past 15 and 25 GB), nor Macaulay2's change matrix in 10 minutes; Singular
  finds the unit ideal by `std` in 13 s and 5 s, and msolve gives the reduced basis `[1]` in under a second
  (`gen/d88trop/hypcheck.py`, `logs/d88trop/hyps.log`). They are hypotheses of the two theorems.

In the proof of Lemma 6.18 the valuation vector `w = ν(ξ)` has a negative entry, `w` lies in the prevariety and the
reduced initial forms vanish at the residues, which are nonzero: (iii)–(iv) exclude this for all such `w` at once, so
they replace the hypothesis on the cones of a fan `Σ` (and need neither gfan's fan nor its completeness). Lemma 6.18
itself (the valuative argument) is stated in the paper, not formalized. The gfan inputs of the d88 run are `Gb` up to
unit scalars, term by term (`n4_gfan`, `kc_gfan`).
-/

namespace Lean6.Special.D88.Trop

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.D88.Trop

/-! ## (i) -/

theorem mem_sound {σ : ℕ → Poly ℤ} {F : List (Poly ℤ)} {rel : Poly ℤ} {G : List GPoly}
    {cofs : List (List (Poly ℤ))} {c0s : List (Poly ℤ)} (h : checkMem σ F rel G cofs c0s = true) {i : ℕ}
    (hi : i < G.length) {R : Type*} [CommRing R] (x : ℕ → R) (hrel : Poly.eval (intHom R) x rel = 0) :
    Poly.eval (intHom R) (fun j => Poly.eval (intHom R) x (σ j)) (flat G[i]) =
      (((cofs.getD i []).zip F).map fun cf => Poly.eval (intHom R) x cf.1 * Poly.eval (intHom R) x cf.2).sum := by
  simp only [checkMem, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hl1, hl2⟩, -⟩, hall⟩ := h
  have hz : i < (G.zip (cofs.zip c0s)).length := by simp [hi, ← hl1, ← hl2]
  have hm := hall _ (List.getElem_mem hz)
  simp only [List.getElem_zip] at hm
  have h0 := Poly.isZero_sound (intHom R) x hm
  rw [Poly.eval_sub, Poly.eval_subst, Poly.eval_add, Poly.eval_sum, Poly.eval_mul, hrel, mul_zero, add_zero,
    sub_eq_zero] at h0
  rw [h0, List.map_map]
  have hc : cofs.getD i [] = cofs[i]'(by omega) := List.getD_eq_getElem _ _ _
  rw [hc]
  congr 1
  refine List.map_congr_left fun cf _ => ?_
  simp [Poly.eval_mul]

/-- **(i) for `S12`.** -/
theorem n4_G_mem (i : ℕ) (hi : i < GN4.length) {R : Type*} [CommRing R] (x : ℕ → R) (hu : x 14 * x 15 = 1) :
    Poly.eval (intHom R) (fun j => Poly.eval (intHom R) x (n4σ j)) (flat GN4[i]) =
      (((cofN4.getD i []).zip n4F).map fun cf =>
        Poly.eval (intHom R) x cf.1 * Poly.eval (intHom R) x cf.2).sum := by
  refine mem_sound n4_mem_ok hi x ?_
  simp [n4rel, ps, pm, V, K, Poly.eval_normalize, Poly.eval_sub, Poly.eval_mul, Poly.eval_var, Poly.eval_const, hu,
    intHom]

/-- **(i) for `KC12`.** -/
theorem kc_G_mem (i : ℕ) (hi : i < GKC.length) {R : Type*} [CommRing R] (x : ℕ → R) (hu : x 14 * x 16 = 1) :
    Poly.eval (intHom R) (fun j => Poly.eval (intHom R) x (kcσ j)) (flat GKC[i]) =
      (((cofKC.getD i []).zip kcF).map fun cf =>
        Poly.eval (intHom R) x cf.1 * Poly.eval (intHom R) x cf.2).sum := by
  refine mem_sound kc_mem_ok hi x ?_
  simp [kcrel, ps, pm, V, K, Poly.eval_normalize, Poly.eval_sub, Poly.eval_mul, Poly.eval_var, Poly.eval_const, hu,
    intHom]

/-! ## (ii) -/

theorem units_sound {p : ℕ} {μ₀ : List ℤ} {G : List GPoly} (h : checkUnits p μ₀ G = true) :
    ∀ g ∈ G, (∀ t ∈ g, ¬ (p : ℤ) ∣ evalZ μ₀ t.2) ∧ (g.map fun t => Mono.trim t.1).Nodup := by
  intro g hg
  simp only [checkUnits, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨hall, hnd⟩ := h g hg
  refine ⟨fun t ht hdvd => (hall t ht).1.1 (Int.emod_eq_zero_of_dvd hdvd), by simpa using hnd⟩

/-- **(ii) for `S12`.** -/
theorem n4_units : ∀ g ∈ GN4, (∀ t ∈ g, ¬ (65521 : ℤ) ∣ evalZ [1, 2, 3, 30] t.2) ∧
    (g.map fun t => Mono.trim t.1).Nodup := by
  have := units_sound n4_units_ok
  exact_mod_cast this

/-- **(ii) for `KC12`.** -/
theorem kc_units : ∀ g ∈ GKC, (∀ t ∈ g, ¬ (65521 : ℤ) ∣ evalZ [1, 2, 3, 30] t.2) ∧
    (g.map fun t => Mono.trim t.1).Nodup := by
  have := units_sound kc_units_ok
  exact_mod_cast this

/-! ## (iii)–(iv) -/

instance : NeZero (65521 : ℕ) := ⟨by norm_num⟩

/-- **(iii)–(iv) for `S12`**, given the torus emptiness of the systems `hypsN4` (the initial systems of the cells
where the checker does not reproduce the emptiness; see `n4_hyps_count`). -/
theorem n4_torus (hH : HypsOK 65521 hypsN4) (w : ℕ → ℚ) (hw : ∃ i < 17, w i < 0) : TorusEmpty 65521 GbN4 w :=
  cover_sound n4_gb_ok hH n4_cover_ok w hw

/-- **(iii)–(iv) for `KC12`**, given the torus emptiness of the systems `hypsKC`. -/
theorem kc_torus (hH : HypsOK 65521 hypsKC) (w : ℕ → ℚ) (hw : ∃ i < 17, w i < 0) : TorusEmpty 65521 GbKC w :=
  cover_sound kc_gb_ok hH kc_cover_ok w hw

/-- The number of assumed systems for `S12`. -/
theorem n4_hyps : hypsN4.length = DataN4.hypCount := n4_hyps_count
/-- The number of assumed systems for `KC12`. -/
theorem kc_hyps : hypsKC.length = DataKC.hypCount := kc_hyps_count

/-! ## Sizes and the comparison with the d88 run -/

/-- `G` for `S12` has 30 polynomials with 354 coefficients (`ξ`-terms). -/
theorem n4_size : GN4.length = 30 ∧ (GN4.map List.length).sum = 354 := ⟨n4_count, n4_terms⟩
/-- `G` for `KC12` has 101 polynomials with 1133 coefficients (`ξ`-terms). -/
theorem kc_size : GKC.length = 101 ∧ (GKC.map List.length).sum = 1133 := ⟨kc_count, kc_terms⟩

/-- The gfan input of the d88 run for `S12` is `Gb` up to unit scalars, term by term. -/
theorem n4_gfan : gfanOKN4 = true := n4_gfan_ok
/-- The gfan input of the d88 run for `KC` is `Gb` up to unit scalars, term by term. -/
theorem kc_gfan : gfanOKKC = true := kc_gfan_ok

end Lean6.Special.D88.Trop
