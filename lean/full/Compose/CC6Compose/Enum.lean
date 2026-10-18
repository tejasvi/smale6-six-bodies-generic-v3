import CC6Compose.EnumCore
import L6Check.F1.Main

/-!
# Bridge: the classification of Proposition 3.1 from the enumeration of the certificate project

The classification hypothesis of `ClassesExcluded` (the second conjunct: every diagram of a germ for positive masses
is the image of an ordered representative under a relabelling, possibly followed by the exchange of the colours), for
the 191 representatives of the class file `n6.json` (`L6F1.classes6`), from `L6F1.F1_main`: a labelled diagram code
satisfying `L6F1.okRules 6` lies in the orbit (`L6F1.orbit 6`, built with `L6F1.actP`) of one of them.

* `toDiagram d`: the labelled diagram (`Diagram 6`) of a code `d : L6F1.Diagram` (edge code in base 4 over the pair
  positions, circle bit masks): the strokes are the pairs `(k, l)`, `k < l`, of the kinds `z`, `zw` resp. `w`, `zw`,
  and the circled bodies are the bits of the masks. `toDiagram_ordered`: it is ordered.
* `toDiagram_actP`: the symmetry `L6F1.actP 6 σ s` of the codes (the body `k` becomes `σ k`, then the colours are
  exchanged if `s`) is sent to `Diagram.relabel σ⁻¹`, followed by `Diagram.swap` if `s` (`Diagram.relabel τ` makes
  the body `k` the body `τ k` of the diagram, so the relabelling of the codes by `σ` is `Diagram.relabel σ.symm`).
* `germCode G`: the code of the diagram of a germ on six bodies (`germCode_zStroke`, `germCode_wStroke`,
  `germCode_zc`, `germCode_wc`), in range (`germCode_inRange`), with diagram `toDiagram (germCode G)`
  (`hasDiagram_germCode`).
* `rulesZ_of_germ`: the rules (E1)–(E6), (C1)–(C4) of `L6F1.rulesZ 6` (colour `z`) hold for a code whose strokes and
  circles are those of a germ for positive masses, from the rules proved for germs (`Germ.E1_z`, `Germ.E2`,
  `Germ.E3`, `Germ.E4_z`, `Germ.E5'`, `Germ.E6`, `Germ.C1_z`, `Germ.C2_z`, `Germ.C3_z`, `Germ.C4_z`). The rules in the
  colour `w` are those of the germ `G.swap`, so `okRules_germCode`: `L6F1.okRules 6 (germCode G) = true`.
* `reps6`: the images under `toDiagram` of the 191 representatives; `reps6_ordered`, `reps6_card`, and
  `classes6_cover`: the second conjunct of `ClassesExcluded` for `reps6`. `classesExcluded_of`: `ClassesExcluded`
  from the exclusion of each diagram of `reps6`.

The computation behind `L6F1.F1_main` is `L6F1.check_n6` (`native_decide`), so `classes6_cover`, `reps6_card` and
`classesExcluded_of` depend on the native evaluation of that computation in addition to `propext`,
`Classical.choice`, `Quot.sound`; the other statements of this file depend on these three only.
-/

namespace CC6Compose

open CC6Full Finset

noncomputable section

variable {m : Fin 6 → ℝ}

/-! ## The classification -/

/-- **The representatives**: the labelled diagrams of the 191 representatives of `n6.json`. -/
def reps6 : Finset (Diagram 6) := (L6F1.classes6.map fun x => toDiagram x.1).toFinset

theorem mem_reps6 {D : Diagram 6} : D ∈ reps6 ↔ ∃ x ∈ L6F1.classes6, toDiagram x.1 = D := by
  simp only [reps6, List.mem_toFinset, List.mem_map]

theorem reps6_ordered : ∀ D ∈ reps6, D.Ordered := by
  intro D hD
  obtain ⟨x, -, rfl⟩ := mem_reps6.mp hD
  exact toDiagram_ordered x.1

theorem strokesOf_inj {s t : ℕ → ℕ → Bool} (h : strokesOf s = strokesOf t) {a b : ℕ} (hab : a < b)
    (hb : b < 6) : s a b = t a b := by
  have hs : ((⟨a, hab.trans hb⟩, ⟨b, hb⟩) : Fin 6 × Fin 6) ∈ strokesOf s ↔ s a b = true :=
    mem_strokesOf.trans ⟨fun h' => h'.2, fun h' => ⟨hab, h'⟩⟩
  have ht : ((⟨a, hab.trans hb⟩, ⟨b, hb⟩) : Fin 6 × Fin 6) ∈ strokesOf t ↔ t a b = true :=
    mem_strokesOf.trans ⟨fun h' => h'.2, fun h' => ⟨hab, h'⟩⟩
  rw [h] at hs
  exact Bool.eq_iff_iff.mpr (hs.symm.trans ht)

theorem circlesOf_inj {c c' : ℕ} (h : circlesOf c = circlesOf c') {k : ℕ} (hk : k < 6) :
    L6F1.circled c k = L6F1.circled c' k := by
  have hs : (⟨k, hk⟩ : Fin 6) ∈ circlesOf c ↔ L6F1.circled c k = true := mem_circlesOf
  have ht : (⟨k, hk⟩ : Fin 6) ∈ circlesOf c' ↔ L6F1.circled c' k = true := mem_circlesOf
  rw [h] at hs
  exact Bool.eq_iff_iff.mpr (hs.symm.trans ht)

/-- `toDiagram` is injective on the codes in range. -/
theorem toDiagram_inj {d d' : L6F1.Diagram} (hd : L6F1.inRange 6 d = true) (hd' : L6F1.inRange 6 d' = true)
    (h : toDiagram d = toDiagram d') : d = d' := by
  have hz : strokesOf (L6F1.zStroke d.e) = strokesOf (L6F1.zStroke d'.e) := congrArg Diagram.zStrokes h
  have hw : strokesOf (L6F1.wStroke d.e) = strokesOf (L6F1.wStroke d'.e) := congrArg Diagram.wStrokes h
  have hzc : circlesOf d.zc = circlesOf d'.zc := congrArg Diagram.zCircles h
  have hwc : circlesOf d.wc = circlesOf d'.wc := congrArg Diagram.wCircles h
  exact L6F1.diagram_ext le_rfl hd hd'
    (fun a b hab hb => kind_eq_of_strokes (strokesOf_inj hz hab hb) (strokesOf_inj hw hab hb))
    (fun k hk => circlesOf_inj hzc hk) (fun k hk => circlesOf_inj hwc hk)

/-- The 191 representatives give 191 labelled diagrams. -/
theorem reps6_card : reps6.card = 191 := by
  obtain ⟨-, -, -, -, hlen, -, -, -, -, -, hkeys⟩ := L6F1.F1_main
  have hnd : (L6F1.classes6.map fun x => toDiagram x.1).Nodup := by
    rw [List.pairwise_map] at hkeys
    unfold List.Nodup
    rw [List.pairwise_map]
    refine hkeys.imp_of_mem fun hx hy hlt heq => ?_
    rw [toDiagram_inj (L6F1.classes6_inRange _ hx) (L6F1.classes6_inRange _ hy) heq] at hlt
    exact lt_irrefl _ hlt
  rw [reps6, List.toFinset_card_of_nodup hnd, List.length_map, hlen]

/-- **Proposition 3.1 for germs** (the second conjunct of `ClassesExcluded`): for positive masses, the diagram of
every germ is the image of one of the representatives under a relabelling, followed by the exchange of the colours
if `b`. -/
theorem classes6_cover : ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, ∃ D ∈ reps6,
    ∃ σ : Equiv.Perm (Fin 6), ∃ b : Bool, G.HasDiagram (bif b then (D.relabel σ).swap else D.relabel σ) := by
  intro m hm G
  obtain ⟨-, -, -, -, -, hcls, -⟩ := L6F1.F1_main
  obtain ⟨x, hx, σ, s, hσ⟩ :=
    (hcls (germCode G)).mp ⟨L6F1.mem_allDiagrams.mpr (germCode_inRange G), okRules_germCode hm G⟩
  refine ⟨toDiagram x.1, mem_reps6.mpr ⟨x, hx, rfl⟩, σ.symm, s, ?_⟩
  have h := hasDiagram_germCode G
  rw [hσ, toDiagram_actP] at h
  exact h

/-- `ClassesExcluded` from the exclusion of each representative. -/
theorem classesExcluded_of (h : ∀ D ∈ reps6, DiagExcluded D) : ClassesExcluded :=
  ⟨reps6, reps6_ordered, classes6_cover, h⟩

end

end CC6Compose
