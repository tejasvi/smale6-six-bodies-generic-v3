import CC6Full.Main
import CC6Full.Germ.Diagram

/-!
# The reduction to the classes of diagrams (Proposition 3.1, Section 8)

The proof of Theorem 1.1 in Section 8 (`sec:proof`) treats one representative of each class of Proposition 3.1
(`prop:enum`). By Lemma 2.11 (`lem:rules`) and Proposition 3.1, the diagram of a singular place is the image of the
representative `D` of its class under a relabelling, possibly followed by the exchange of the colours; by Lemma 2.9
(`lem:symm`), the inverse relabelling and, if needed, the involution `ι` give a place with diagram `D`, for a
permutation of the masses and with the same `ℓ`. This file proves this reduction for germs.

* `DiagExcluded D`: there are finitely many nonzero `P_i ∈ ℤ[m₁, …, m₆]` such that every germ with diagram `D` and
  `ℓ ≤ 0`, for positive masses `m`, makes one of them vanish at a permutation of `m`.
* Lemma 2.9 on diagrams: `Germ.HasDiagram.relabel` (if `D` is the diagram of `G`, then `D.relabel σ` is the diagram
  of `G.relabel σ`), `Germ.hasDiagram_relabel_iff`, `Germ.hasDiagram_relabel_symm_iff`, and
  `Germ.hasDiagram_swap_iff` (`D.swap` is the diagram of `G.swap`). Hence `diagExcluded_relabel_iff` and
  `diagExcluded_swap_iff`.
* `Diagram.Ordered D`: every stroke of `D` is stored as a pair `(k, l)` with `k ≤ l`. The statements on relabelling
  need it: `Diagram.zS` and `Diagram.wS` read only the stored pairs `(k, l)` with `k < l`, while `Diagram.relabel`
  turns every stored pair with `k ≠ l` into a stroke. Relabelled diagrams are ordered (`Diagram.ordered_relabel`),
  and so are the diagrams given by `Diagram.ofLists` (`Diagram.ordered_ofLists`), among them those of Table 1.
* `DiagExcluded.of_poly`, `DiagExcluded.of_exists_poly`: one nonzero polynomial vanishes at `m` for every germ with
  diagram `D` (the form of Theorems 6.12 and 6.15); `DiagExcluded.of_no_germ`: no germ for positive masses has
  diagram `D` (the form of Theorem 6.5).
* `germExclusion_of_fintype`, `germExclusion_of_finset`: `GermExclusion` holds if every germ with `ℓ ≤ 0` for
  positive masses has one of finitely many excluded diagrams. `germExclusion_of_classes`: `GermExclusion` from a
  finite set `reps` of ordered diagrams such that every germ for positive masses has the diagram `D.relabel σ` or
  `(D.relabel σ).swap` for some `D ∈ reps` (Lemma 2.11 and Proposition 3.1), and `DiagExcluded D` for every
  `D ∈ reps` (Propositions 4.5 and 5.3, Sections 6 and 7).
-/

namespace CC6Full

/-! ## Ordered diagrams and relabelling -/

namespace Diagram

variable {n : ℕ}

/-- Every stroke of `D` is stored as a pair `(k, l)` with `k ≤ l`, as `Diagram.ofLists` and `Diagram.relabel` store
them. -/
def Ordered (D : Diagram n) : Prop :=
  (∀ e ∈ D.zStrokes, e.1 ≤ e.2) ∧ ∀ e ∈ D.wStrokes, e.1 ≤ e.2

instance decidableOrdered (D : Diagram n) : Decidable D.Ordered :=
  inferInstanceAs (Decidable ((∀ e ∈ D.zStrokes, e.1 ≤ e.2) ∧ ∀ e ∈ D.wStrokes, e.1 ≤ e.2))

@[simp] theorem swap_swap (D : Diagram n) : D.swap.swap = D := rfl

theorem swap_relabel (σ : Equiv.Perm (Fin n)) (D : Diagram n) : (D.relabel σ).swap = D.swap.relabel σ := rfl

theorem ord2_comm (k l : Fin n) : ord2 k l = ord2 l k := by
  unfold ord2
  rw [min_comm, max_comm]

theorem ord2_le (k l : Fin n) : (ord2 k l).1 ≤ (ord2 k l).2 := min_le_max

theorem ord2_of_le {e : Fin n × Fin n} (h : e.1 ≤ e.2) : ord2 e.1 e.2 = e := by
  simp only [ord2, min_eq_left h, max_eq_right h, Prod.mk.eta]

/-- `ord2` of the images of the entries of `ord2 k l` is `ord2` of the images of `k` and `l`. -/
theorem ord2_map (f : Fin n → Fin n) (k l : Fin n) :
    ord2 (f (ord2 k l).1) (f (ord2 k l).2) = ord2 (f k) (f l) := by
  rcases le_total k l with h | h
  · simp only [ord2, min_eq_left h, max_eq_right h]
  · rw [ord2_comm k l]
    simp only [ord2, min_eq_left h, max_eq_right h]
    rw [min_comm, max_comm]

/-- The pair `ord2 k l` lies in the relabelled set of strokes iff `ord2 (σ k) (σ l)` lies in the set, if the strokes
are stored as pairs `(k, l)` with `k ≤ l`. -/
theorem ord2_mem_image_iff {s : Finset (Fin n × Fin n)} (hs : ∀ e ∈ s, e.1 ≤ e.2) (σ : Equiv.Perm (Fin n))
    (k l : Fin n) :
    ord2 k l ∈ s.image (fun e => ord2 (σ.symm e.1) (σ.symm e.2)) ↔ ord2 (σ k) (σ l) ∈ s := by
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨e, he, h⟩
    have key : ord2 (σ k) (σ l) = e := by
      rw [← ord2_map σ k l, ← h, ord2_map σ, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        ord2_of_le (hs e he)]
    rw [key]
    exact he
  · intro h
    refine ⟨ord2 (σ k) (σ l), h, ?_⟩
    rw [ord2_map σ.symm, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Body `k` of `D.relabel σ` is `z`-circled iff body `σ k` of `D` is. -/
theorem mem_relabel_zCircles (σ : Equiv.Perm (Fin n)) (D : Diagram n) (k : Fin n) :
    k ∈ (D.relabel σ).zCircles ↔ σ k ∈ D.zCircles := by
  show k ∈ D.zCircles.image σ.symm ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [Equiv.apply_symm_apply]
  · intro h
    exact ⟨σ k, h, Equiv.symm_apply_apply σ k⟩

/-- Body `k` of `D.relabel σ` is `w`-circled iff body `σ k` of `D` is. -/
theorem mem_relabel_wCircles (σ : Equiv.Perm (Fin n)) (D : Diagram n) (k : Fin n) :
    k ∈ (D.relabel σ).wCircles ↔ σ k ∈ D.wCircles := by
  show k ∈ D.wCircles.image σ.symm ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [Equiv.apply_symm_apply]
  · intro h
    exact ⟨σ k, h, Equiv.symm_apply_apply σ k⟩

/-- `kl` is a `z`-stroke of `D.relabel σ` iff `σ k σ l` is a `z`-stroke of `D`, for ordered `D`. -/
theorem Ordered.relabel_zS {D : Diagram n} (hD : D.Ordered) (σ : Equiv.Perm (Fin n)) (k l : Fin n) :
    (D.relabel σ).zS k l ↔ D.zS (σ k) (σ l) :=
  and_congr σ.injective.ne_iff.symm (ord2_mem_image_iff hD.1 σ k l)

/-- `kl` is a `w`-stroke of `D.relabel σ` iff `σ k σ l` is a `w`-stroke of `D`, for ordered `D`. -/
theorem Ordered.relabel_wS {D : Diagram n} (hD : D.Ordered) (σ : Equiv.Perm (Fin n)) (k l : Fin n) :
    (D.relabel σ).wS k l ↔ D.wS (σ k) (σ l) :=
  and_congr σ.injective.ne_iff.symm (ord2_mem_image_iff hD.2 σ k l)

theorem ordered_relabel (σ : Equiv.Perm (Fin n)) (D : Diagram n) : (D.relabel σ).Ordered := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩ <;>
  · simp only [relabel, Finset.mem_image] at he
    obtain ⟨a, -, rfl⟩ := he
    exact ord2_le _ _

theorem Ordered.swap {D : Diagram n} (hD : D.Ordered) : D.swap.Ordered := ⟨hD.2, hD.1⟩

theorem ordered_swap_iff {D : Diagram n} : D.swap.Ordered ↔ D.Ordered :=
  ⟨fun h => h.swap, fun h => h.swap⟩

theorem ordered_ofLists (zs ws : List (ℕ × ℕ)) (zc wc : List ℕ) : (ofLists zs ws zc wc : Diagram n).Ordered := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩ <;>
  · simp only [ofLists, List.mem_toFinset, List.mem_filterMap] at he
    obtain ⟨a, -, ha⟩ := he
    split_ifs at ha
    cases ha
    exact ord2_le _ _

end Diagram

/-! ## The diagram of a relabelled germ and of the exchanged germ (Lemma 2.9) -/

namespace Germ

variable {n : ℕ} {m : Fin n → ℝ}

/-- Lemma 2.9 (b) on diagrams: `G.swap` has the diagram `D` iff `G` has the diagram `D.swap`. -/
theorem hasDiagram_swap_iff {G : Germ n m} {D : Diagram n} : G.swap.HasDiagram D ↔ G.HasDiagram D.swap :=
  ⟨fun h => h.swap, fun h => h.swap⟩

theorem hasDiagram_swap_swap_iff {G : Germ n m} {D : Diagram n} :
    G.swap.HasDiagram D.swap ↔ G.HasDiagram D :=
  ⟨fun h => h.swap, fun h => h.swap⟩

/-- Lemma 2.9 (a) on diagrams: if `D` is the diagram of `G` and `D` is ordered, then `D.relabel σ` is the diagram of
`G.relabel σ`. -/
theorem HasDiagram.relabel {G : Germ n m} {D : Diagram n} (h : G.HasDiagram D) (hD : D.Ordered)
    (σ : Equiv.Perm (Fin n)) : (G.relabel σ).HasDiagram (D.relabel σ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun k l => ?_, fun k l => ?_, fun k => ?_, fun k => ?_⟩
  · rw [relabel_zStroke, hD.relabel_zS]
    exact h1 (σ k) (σ l)
  · rw [relabel_wStroke, hD.relabel_wS]
    exact h2 (σ k) (σ l)
  · rw [relabel_zCircle, Diagram.mem_relabel_zCircles]
    exact h3 (σ k)
  · rw [relabel_wCircle, Diagram.mem_relabel_wCircles]
    exact h4 (σ k)

theorem hasDiagram_relabel_iff {G : Germ n m} {D : Diagram n} (hD : D.Ordered) (σ : Equiv.Perm (Fin n)) :
    (G.relabel σ).HasDiagram (D.relabel σ) ↔ G.HasDiagram D := by
  refine ⟨fun h => ?_, fun h => h.relabel hD σ⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun k l => ?_, fun k l => ?_, fun k => ?_, fun k => ?_⟩
  · have h' := h1 (σ.symm k) (σ.symm l)
    rwa [relabel_zStroke, hD.relabel_zS, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h'
  · have h' := h2 (σ.symm k) (σ.symm l)
    rwa [relabel_wStroke, hD.relabel_wS, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h'
  · have h' := h3 (σ.symm k)
    rwa [relabel_zCircle, Diagram.mem_relabel_zCircles, Equiv.apply_symm_apply] at h'
  · have h' := h4 (σ.symm k)
    rwa [relabel_wCircle, Diagram.mem_relabel_wCircles, Equiv.apply_symm_apply] at h'

/-- `G` has the diagram `D.relabel σ` iff the germ `G.relabel σ⁻¹`, for the masses `m ∘ σ⁻¹`, has the diagram `D`,
for ordered `D`. -/
theorem hasDiagram_relabel_symm_iff {G : Germ n m} {D : Diagram n} (hD : D.Ordered) (σ : Equiv.Perm (Fin n)) :
    G.HasDiagram (D.relabel σ) ↔ (G.relabel σ.symm).HasDiagram D := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun k l => ?_, fun k l => ?_, fun k => ?_, fun k => ?_⟩
    · rw [relabel_zStroke, h1, hD.relabel_zS, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    · rw [relabel_wStroke, h2, hD.relabel_wS, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    · rw [relabel_zCircle, h3, Diagram.mem_relabel_zCircles, Equiv.apply_symm_apply]
    · rw [relabel_wCircle, h4, Diagram.mem_relabel_wCircles, Equiv.apply_symm_apply]
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun k l => ?_, fun k l => ?_, fun k => ?_, fun k => ?_⟩
    · have h' := h1 (σ k) (σ l)
      rwa [relabel_zStroke, Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← hD.relabel_zS] at h'
    · have h' := h2 (σ k) (σ l)
      rwa [relabel_wStroke, Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← hD.relabel_wS] at h'
    · have h' := h3 (σ k)
      rwa [relabel_zCircle, Equiv.symm_apply_apply, ← Diagram.mem_relabel_zCircles] at h'
    · have h' := h4 (σ k)
      rwa [relabel_wCircle, Equiv.symm_apply_apply, ← Diagram.mem_relabel_wCircles] at h'

end Germ

/-! ## Excluded diagrams -/

/-- The germs with diagram `D` and `ℓ ≤ 0` are excluded for generic masses: there are finitely many nonzero integer
polynomials in the six masses such that every germ with diagram `D` and `ℓ ≤ 0`, for positive masses `m`, makes one
of them vanish at a permutation of `m`. -/
def DiagExcluded (D : Diagram 6) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (P : ι → MvPolynomial (Fin 6) ℤ), (∀ i, P i ≠ 0) ∧
    ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, G.HasDiagram D → G.ell ≤ 0 →
      ∃ i, ∃ σ : Equiv.Perm (Fin 6), MvPolynomial.aeval (m ∘ σ) (P i) = 0

namespace DiagExcluded

variable {D : Diagram 6}

/-- The exchange of the colours (Lemma 2.9 (b)): the same polynomials exclude `D.swap`. -/
theorem swap (h : DiagExcluded D) : DiagExcluded D.swap := by
  obtain ⟨ι, hι, P, hP0, hP⟩ := h
  refine ⟨ι, hι, P, hP0, fun m hm G hG hℓ => ?_⟩
  exact hP m hm G.swap (Germ.hasDiagram_swap_iff.mpr hG) (by rw [Germ.swap_ell]; exact hℓ)

/-- Relabelling (Lemma 2.9 (a)): the same polynomials exclude `D.relabel σ`, for ordered `D`. -/
theorem relabel (h : DiagExcluded D) (hD : D.Ordered) (σ : Equiv.Perm (Fin 6)) :
    DiagExcluded (D.relabel σ) := by
  obtain ⟨ι, hι, P, hP0, hP⟩ := h
  refine ⟨ι, hι, P, hP0, fun m hm G hG hℓ => ?_⟩
  obtain ⟨i, τ, hi⟩ := hP (m ∘ σ.symm) (fun k => hm _) (G.relabel σ.symm)
    ((Germ.hasDiagram_relabel_symm_iff hD σ).mp hG) (by rw [Germ.relabel_ell]; exact hℓ)
  refine ⟨i, σ.symm * τ, ?_⟩
  rw [Equiv.Perm.coe_mul]
  exact hi

theorem of_relabel (hD : D.Ordered) (σ : Equiv.Perm (Fin 6)) (h : DiagExcluded (D.relabel σ)) :
    DiagExcluded D := by
  obtain ⟨ι, hι, P, hP0, hP⟩ := h
  refine ⟨ι, hι, P, hP0, fun m hm G hG hℓ => ?_⟩
  obtain ⟨i, τ, hi⟩ := hP (m ∘ σ) (fun k => hm _) (G.relabel σ) ((Germ.hasDiagram_relabel_iff hD σ).mpr hG)
    (by rw [Germ.relabel_ell]; exact hℓ)
  refine ⟨i, σ * τ, ?_⟩
  rw [Equiv.Perm.coe_mul]
  exact hi

/-- The image of an excluded ordered diagram under the relabelling by `σ`, followed by the exchange of the colours if
`b`, is excluded. -/
theorem relabel_cond (h : DiagExcluded D) (hD : D.Ordered) (σ : Equiv.Perm (Fin 6)) (b : Bool) :
    DiagExcluded (bif b then (D.relabel σ).swap else D.relabel σ) := by
  cases b
  · exact h.relabel hD σ
  · exact (h.relabel hD σ).swap

/-- `D` is excluded if one nonzero polynomial vanishes at `m` for every germ with diagram `D` for positive masses
`m`. -/
theorem of_poly (P : MvPolynomial (Fin 6) ℤ) (hP : P ≠ 0)
    (h : ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, G.HasDiagram D → MvPolynomial.aeval m P = 0) :
    DiagExcluded D := by
  refine ⟨Unit, inferInstance, fun _ => P, fun _ => hP, fun m hm G hG _ => ⟨(), 1, ?_⟩⟩
  rw [Equiv.Perm.coe_one, Function.comp_id]
  exact h m hm G hG

/-- `DiagExcluded.of_poly` in the form of `Six.d98_poly` and `Six.d93_poly`. -/
theorem of_exists_poly (h : ∃ P : MvPolynomial (Fin 6) ℤ, P ≠ 0 ∧
    ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, G.HasDiagram D → MvPolynomial.aeval m P = 0) :
    DiagExcluded D := by
  obtain ⟨P, hP, hm⟩ := h
  exact of_poly P hP hm

/-- `D` is excluded if no germ for positive masses has diagram `D` (the empty family of polynomials). -/
theorem of_no_germ (h : ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, ¬ G.HasDiagram D) :
    DiagExcluded D :=
  ⟨Empty, inferInstance, Empty.elim, fun i => i.elim, fun m hm G hG _ => absurd hG (h m hm G)⟩

end DiagExcluded

theorem diagExcluded_relabel_iff {D : Diagram 6} (hD : D.Ordered) (σ : Equiv.Perm (Fin 6)) :
    DiagExcluded D ↔ DiagExcluded (D.relabel σ) :=
  ⟨fun h => h.relabel hD σ, DiagExcluded.of_relabel hD σ⟩

theorem diagExcluded_swap_iff {D : Diagram 6} : DiagExcluded D ↔ DiagExcluded D.swap :=
  ⟨DiagExcluded.swap, fun h => h.swap⟩

/-! ## The reduction -/

/-- `GermExclusion` holds if every germ with `ℓ ≤ 0`, for positive masses, has one of finitely many excluded diagrams
`E k`: the family of polynomials is the union of their families. -/
theorem germExclusion_of_fintype {κ : Type} [Fintype κ] (E : κ → Diagram 6)
    (hE : ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, G.ell ≤ 0 → ∃ k, G.HasDiagram (E k))
    (hexc : ∀ k, DiagExcluded (E k)) : GermExclusion := by
  simp only [DiagExcluded] at hexc
  choose ι hι P hP0 hP using hexc
  refine ⟨(k : κ) × ι k, inferInstance, fun i => P i.1 i.2, fun i => hP0 _ _, ?_⟩
  intro m hm G hℓ
  obtain ⟨k, hk⟩ := hE m hm G hℓ
  obtain ⟨i, σ, h⟩ := hP k m hm G hk hℓ
  exact ⟨⟨k, i⟩, σ, h⟩

/-- `GermExclusion` holds if every germ with `ℓ ≤ 0`, for positive masses, has its diagram in a finite set of
excluded diagrams. -/
theorem germExclusion_of_finset (S : Finset (Diagram 6))
    (hS : ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, G.ell ≤ 0 → ∃ D ∈ S, G.HasDiagram D)
    (hexc : ∀ D ∈ S, DiagExcluded D) : GermExclusion := by
  refine germExclusion_of_fintype (κ := S) Subtype.val (fun m hm G hℓ => ?_) (fun D => hexc D.1 D.2)
  obtain ⟨D, hD, h⟩ := hS m hm G hℓ
  exact ⟨⟨D, hD⟩, h⟩

/-- **The reduction to the classes of Proposition 3.1** (Section 8): if every germ for positive masses has the
diagram `D.relabel σ` or `(D.relabel σ).swap` for some ordered `D ∈ reps` (Lemma 2.11 and Proposition 3.1), and every
`D ∈ reps` is excluded, then `GermExclusion` holds. The excluded diagrams are the images
`bif b then (D.relabel σ).swap else D.relabel σ`, `D ∈ reps` (`DiagExcluded.relabel_cond`). -/
theorem germExclusion_of_classes (reps : Finset (Diagram 6)) (hord : ∀ D ∈ reps, D.Ordered)
    (hcls : ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, ∃ D ∈ reps, ∃ σ : Equiv.Perm (Fin 6), ∃ b : Bool,
      G.HasDiagram (bif b then (D.relabel σ).swap else D.relabel σ))
    (hexc : ∀ D ∈ reps, DiagExcluded D) : GermExclusion := by
  refine germExclusion_of_fintype (κ := reps × Equiv.Perm (Fin 6) × Bool)
    (fun a => bif a.2.2 then (a.1.1.relabel a.2.1).swap else a.1.1.relabel a.2.1) (fun m hm G _ => ?_)
    (fun a => (hexc a.1.1 a.1.2).relabel_cond (hord a.1.1 a.1.2) a.2.1 a.2.2)
  obtain ⟨D, hD, σ, b, h⟩ := hcls m hm G
  exact ⟨(⟨D, hD⟩, σ, b), h⟩

end CC6Full
